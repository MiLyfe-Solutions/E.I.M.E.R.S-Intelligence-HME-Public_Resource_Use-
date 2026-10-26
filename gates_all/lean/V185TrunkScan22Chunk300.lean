import V185TrunkScan22Chunk299

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2675524 : List Nat := [2, 3, 4, 2, 2, 1, 1, 7]
def baseStart_2675524 : Nat := 118140960795 + 2675524 * 2 ^ 59
def prefixEnd_2675524 : Nat := 4983230072969 + 3 ^ 40 * 2675524 * 2
def baseEnd_2675524 : Nat := 101765171454821869166333

theorem tailTrace_2675524 : CollatzResearch.WordTrace tailWord_2675524 prefixEnd_2675524 101765171454821869166333 := by
  unfold tailWord_2675524
  simp only [CollatzResearch.WordTrace]
  refine ⟨48792188579520482982604813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65056251439360643976806417 48792188579520482982604813)
  ·
    refine ⟨18297070717320181118476805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48792188579520482982604813 18297070717320181118476805)
    ·
      refine ⟨3430700759497533959714401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18297070717320181118476805 3430700759497533959714401)
      ·
        refine ⟨2573025569623150469785801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3430700759497533959714401 2573025569623150469785801)
        ·
          refine ⟨1929769177217362852339351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2573025569623150469785801 1929769177217362852339351)
          ·
            refine ⟨2894653765826044278509027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929769177217362852339351 2894653765826044278509027)
            ·
              refine ⟨4341980648739066417763541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894653765826044278509027 4341980648739066417763541)
              ·
                refine ⟨101765171454821869166333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4341980648739066417763541 101765171454821869166333)
                ·
                  rfl

theorem cell22_2675524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 7].length) (baseStart_2675524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675524 prefixEnd_2675524 := by exact prefixLift 2675524
  have htrace : WordTrace (prefixWord ++ tailWord_2675524) baseStart_2675524 baseEnd_2675524 := by
    simpa [prefixWord, tailWord_2675524, baseEnd_2675524] using wordTrace_append hprefix tailTrace_2675524
  have hstable : (prefixWord ++ tailWord_2675524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675524).length < 2 ^ (prefixWord ++ tailWord_2675524).sum := by decide
  have hdescent : baseEnd_2675524 < baseStart_2675524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675586 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2675586 : Nat := 118140960795 + 2675586 * 2 ^ 59
def prefixEnd_2675586 : Nat := 4983230072969 + 3 ^ 40 * 2675586 * 2
def baseEnd_2675586 : Nat := 305302588986816442482269

theorem tailTrace_2675586 : CollatzResearch.WordTrace tailWord_2675586 prefixEnd_2675586 305302588986816442482269 := by
  unfold tailWord_2675586
  simp only [CollatzResearch.WordTrace]
  refine ⟨24396659621204087638491653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65057758989877567035977741 24396659621204087638491653)
  ·
    refine ⟨4574373678975766432217185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24396659621204087638491653 4574373678975766432217185)
    ·
      refine ⟨3430780259231824824162889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4574373678975766432217185 3430780259231824824162889)
      ·
        refine ⟨2573085194423868618122167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3430780259231824824162889 2573085194423868618122167)
        ·
          refine ⟨3859627791635802927183251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573085194423868618122167 3859627791635802927183251)
          ·
            refine ⟨5789441687453704390774877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859627791635802927183251 5789441687453704390774877)
            ·
              refine ⟨2171040632795139146540579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5789441687453704390774877 2171040632795139146540579)
              ·
                refine ⟨3256560949192708719810869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171040632795139146540579 3256560949192708719810869)
                ·
                  refine ⟨305302588986816442482269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3256560949192708719810869 305302588986816442482269)
                  ·
                    rfl

theorem cell22_2675586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2675586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675586 prefixEnd_2675586 := by exact prefixLift 2675586
  have htrace : WordTrace (prefixWord ++ tailWord_2675586) baseStart_2675586 baseEnd_2675586 := by
    simpa [prefixWord, tailWord_2675586, baseEnd_2675586] using wordTrace_append hprefix tailTrace_2675586
  have hstable : (prefixWord ++ tailWord_2675586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675586).length < 2 ^ (prefixWord ++ tailWord_2675586).sum := by decide
  have hdescent : baseEnd_2675586 < baseStart_2675586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675593 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_2675593 : Nat := 118140960795 + 2675593 * 2 ^ 59
def prefixEnd_2675593 : Nat := 4983230072969 + 3 ^ 40 * 2675593 * 2
def baseEnd_2675593 : Nat := 915910163203503642521785

theorem tailTrace_2675593 : CollatzResearch.WordTrace tailWord_2675593 prefixEnd_2675593 915910163203503642521785 := by
  unfold tailWord_2675593
  simp only [CollatzResearch.WordTrace]
  refine ⟨97586893795790990749471433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65057929197193993832980955 97586893795790990749471433)
  ·
    refine ⟨73190170346843243062103575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97586893795790990749471433 73190170346843243062103575)
    ·
      refine ⟨109785255520264864593155363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73190170346843243062103575 109785255520264864593155363)
      ·
        refine ⟨164677883280397296889733045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109785255520264864593155363 164677883280397296889733045)
        ·
          refine ⟨15438551557537246583412473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164677883280397296889733045 15438551557537246583412473)
          ·
            refine ⟨11578913668152934937559355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15438551557537246583412473 11578913668152934937559355)
            ·
              refine ⟨17368370502229402406339033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11578913668152934937559355 17368370502229402406339033)
              ·
                refine ⟨13026277876672051804754275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17368370502229402406339033 13026277876672051804754275)
                ·
                  refine ⟨19539416815008077707131413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13026277876672051804754275 19539416815008077707131413)
                  ·
                    refine ⟨915910163203503642521785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19539416815008077707131413 915910163203503642521785)
                    ·
                      rfl

theorem cell22_2675593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_2675593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675593 prefixEnd_2675593 := by exact prefixLift 2675593
  have htrace : WordTrace (prefixWord ++ tailWord_2675593) baseStart_2675593 baseEnd_2675593 := by
    simpa [prefixWord, tailWord_2675593, baseEnd_2675593] using wordTrace_append hprefix tailTrace_2675593
  have hstable : (prefixWord ++ tailWord_2675593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675593).length < 2 ^ (prefixWord ++ tailWord_2675593).sum := by decide
  have hdescent : baseEnd_2675593 < baseStart_2675593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675595 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 2, 3]
def baseStart_2675595 : Nat := 118140960795 + 2675595 * 2 ^ 59
def prefixEnd_2675595 : Nat := 4983230072969 + 3 ^ 40 * 2675595 * 2
def baseEnd_2675595 : Nat := 915910847844376303971779

theorem tailTrace_2675595 : CollatzResearch.WordTrace tailWord_2675595 prefixEnd_2675595 915910847844376303971779 := by
  unfold tailWord_2675595
  simp only [CollatzResearch.WordTrace]
  refine ⟨97586966741783745091044239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65057977827855830060696159 97586966741783745091044239)
  ·
    refine ⟨146380450112675617636566359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97586966741783745091044239 146380450112675617636566359)
    ·
      refine ⟨219570675169013426454849539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146380450112675617636566359 219570675169013426454849539)
      ·
        refine ⟨329356012753520139682274309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219570675169013426454849539 329356012753520139682274309)
        ·
          refine ⟨61754252391285026190426433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329356012753520139682274309 61754252391285026190426433)
          ·
            refine ⟨46315689293463769642819825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61754252391285026190426433 46315689293463769642819825)
            ·
              refine ⟨34736766970097827232114869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46315689293463769642819825 34736766970097827232114869)
              ·
                refine ⟨3256571903446671303010769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34736766970097827232114869 3256571903446671303010769)
                ·
                  refine ⟨2442428927585003477258077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3256571903446671303010769 2442428927585003477258077)
                  ·
                    refine ⟨915910847844376303971779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442428927585003477258077 915910847844376303971779)
                    ·
                      rfl

theorem cell22_2675595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 3].length) (baseStart_2675595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675595 prefixEnd_2675595 := by exact prefixLift 2675595
  have htrace : WordTrace (prefixWord ++ tailWord_2675595) baseStart_2675595 baseEnd_2675595 := by
    simpa [prefixWord, tailWord_2675595, baseEnd_2675595] using wordTrace_append hprefix tailTrace_2675595
  have hstable : (prefixWord ++ tailWord_2675595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675595).length < 2 ^ (prefixWord ++ tailWord_2675595).sum := by decide
  have hdescent : baseEnd_2675595 < baseStart_2675595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675687 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 5]
def baseStart_2675687 : Nat := 118140960795 + 2675687 * 2 ^ 59
def prefixEnd_2675687 : Nat := 4983230072969 + 3 ^ 40 * 2675687 * 2
def baseEnd_2675687 : Nat := 305314113774839576890499

theorem tailTrace_2675687 : CollatzResearch.WordTrace tailWord_2675687 prefixEnd_2675687 305314113774839576890499 := by
  unfold tailWord_2675687
  simp only [CollatzResearch.WordTrace]
  refine ⟨97590322257450444803393315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65060214838300296535595543 97590322257450444803393315)
  ·
    refine ⟨146385483386175667205089973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97590322257450444803393315 146385483386175667205089973)
    ·
      refine ⟨13723639067453968800477185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146385483386175667205089973 13723639067453968800477185)
      ·
        refine ⟨10292729300590476600357889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13723639067453968800477185 10292729300590476600357889)
        ·
          refine ⟨7719546975442857450268417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10292729300590476600357889 7719546975442857450268417)
          ·
            refine ⟨5789660231582143087701313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7719546975442857450268417 5789660231582143087701313)
            ·
              refine ⟨4342245173686607315775985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5789660231582143087701313 4342245173686607315775985)
              ·
                refine ⟨3256683880264955486831989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342245173686607315775985 3256683880264955486831989)
                ·
                  refine ⟨305314113774839576890499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3256683880264955486831989 305314113774839576890499)
                  ·
                    rfl

theorem cell22_2675687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 5].length) (baseStart_2675687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675687 prefixEnd_2675687 := by exact prefixLift 2675687
  have htrace : WordTrace (prefixWord ++ tailWord_2675687) baseStart_2675687 baseEnd_2675687 := by
    simpa [prefixWord, tailWord_2675687, baseEnd_2675687] using wordTrace_append hprefix tailTrace_2675687
  have hstable : (prefixWord ++ tailWord_2675687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675687).length < 2 ^ (prefixWord ++ tailWord_2675687).sum := by decide
  have hdescent : baseEnd_2675687 < baseStart_2675687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675702 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2675702 : Nat := 118140960795 + 2675702 * 2 ^ 59
def prefixEnd_2675702 : Nat := 4983230072969 + 3 ^ 40 * 2675702 * 2
def baseEnd_2675702 : Nat := 915947476131063691546451

theorem tailTrace_2675702 : CollatzResearch.WordTrace tailWord_2675702 prefixEnd_2675702 915947476131063691546451 := by
  unfold tailWord_2675702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099429334524756397824335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65060579568264068243459573 6099429334524756397824335)
  ·
    refine ⟨9149144001787134596736503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6099429334524756397824335 9149144001787134596736503)
    ·
      refine ⟨13723716002680701895104755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9149144001787134596736503 13723716002680701895104755)
      ·
        refine ⟨20585574004021052842657133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13723716002680701895104755 20585574004021052842657133)
        ·
          refine ⟨7719590251507894815996425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20585574004021052842657133 7719590251507894815996425)
          ·
            refine ⟨5789692688630921111997319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7719590251507894815996425 5789692688630921111997319)
            ·
              refine ⟨8684539032946381667995979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789692688630921111997319 8684539032946381667995979)
              ·
                refine ⟨13026808549419572501993969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8684539032946381667995979 13026808549419572501993969)
                ·
                  refine ⟨9770106412064679376495477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13026808549419572501993969 9770106412064679376495477)
                  ·
                    refine ⟨915947476131063691546451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9770106412064679376495477 915947476131063691546451)
                    ·
                      rfl

theorem cell22_2675702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2675702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675702 prefixEnd_2675702 := by exact prefixLift 2675702
  have htrace : WordTrace (prefixWord ++ tailWord_2675702) baseStart_2675702 baseEnd_2675702 := by
    simpa [prefixWord, tailWord_2675702, baseEnd_2675702] using wordTrace_append hprefix tailTrace_2675702
  have hstable : (prefixWord ++ tailWord_2675702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675702).length < 2 ^ (prefixWord ++ tailWord_2675702).sum := by decide
  have hdescent : baseEnd_2675702 < baseStart_2675702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675747 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 4, 3]
def baseStart_2675747 : Nat := 118140960795 + 2675747 * 2 ^ 59
def prefixEnd_2675747 : Nat := 4983230072969 + 3 ^ 40 * 2675747 * 2
def baseEnd_2675747 : Nat := 915962880550698574171313

theorem tailTrace_2675747 : CollatzResearch.WordTrace tailWord_2675747 prefixEnd_2675747 915962880550698574171313 := by
  unfold tailWord_2675747
  simp only [CollatzResearch.WordTrace]
  refine ⟨97592510637233075050577495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65061673758155383367051663 97592510637233075050577495)
  ·
    refine ⟨146388765955849612575866243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97592510637233075050577495 146388765955849612575866243)
    ·
      refine ⟨219583148933774418863799365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146388765955849612575866243 219583148933774418863799365)
      ·
        refine ⟨41171840425082703536962381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219583148933774418863799365 41171840425082703536962381)
        ·
          refine ⟨15439440159406013826360893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41171840425082703536962381 15439440159406013826360893)
          ·
            refine ⟨5789790059777255184885335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15439440159406013826360893 5789790059777255184885335)
            ·
              refine ⟨8684685089665882777328003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789790059777255184885335 8684685089665882777328003)
              ·
                refine ⟨13027027634498824165992005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8684685089665882777328003 13027027634498824165992005)
                ·
                  refine ⟨2442567681468529531123501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13027027634498824165992005 2442567681468529531123501)
                  ·
                    refine ⟨915962880550698574171313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442567681468529531123501 915962880550698574171313)
                    ·
                      rfl

theorem cell22_2675747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 3].length) (baseStart_2675747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675747 prefixEnd_2675747 := by exact prefixLift 2675747
  have htrace : WordTrace (prefixWord ++ tailWord_2675747) baseStart_2675747 baseEnd_2675747 := by
    simpa [prefixWord, tailWord_2675747, baseEnd_2675747] using wordTrace_append hprefix tailTrace_2675747
  have hstable : (prefixWord ++ tailWord_2675747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675747).length < 2 ^ (prefixWord ++ tailWord_2675747).sum := by decide
  have hdescent : baseEnd_2675747 < baseStart_2675747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675764 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2675764 : Nat := 118140960795 + 2675764 * 2 ^ 59
def prefixEnd_2675764 : Nat := 4983230072969 + 3 ^ 40 * 2675764 * 2
def baseEnd_2675764 : Nat := 915968699998116196496261

theorem tailTrace_2675764 : CollatzResearch.WordTrace tailWord_2675764 prefixEnd_2675764 915968699998116196496261 := by
  unfold tailWord_2675764
  simp only [CollatzResearch.WordTrace]
  refine ⟨48796565339085743476973173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65062087118780991302630897 48796565339085743476973173)
  ·
    refine ⟨4574678000539288450966235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48796565339085743476973173 4574678000539288450966235)
    ·
      refine ⟨6862017000808932676449353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574678000539288450966235 6862017000808932676449353)
      ·
        refine ⟨5146512750606699507337015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862017000808932676449353 5146512750606699507337015)
        ·
          refine ⟨7719769125910049261005523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146512750606699507337015 7719769125910049261005523)
          ·
            refine ⟨11579653688865073891508285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719769125910049261005523 11579653688865073891508285)
            ·
              refine ⟨4342370133324402709315607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11579653688865073891508285 4342370133324402709315607)
              ·
                refine ⟨6513555199986604063973411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342370133324402709315607 6513555199986604063973411)
                ·
                  refine ⟨9770332799979906095960117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6513555199986604063973411 9770332799979906095960117)
                  ·
                    refine ⟨915968699998116196496261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9770332799979906095960117 915968699998116196496261)
                    ·
                      rfl

theorem cell22_2675764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2675764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675764 prefixEnd_2675764 := by exact prefixLift 2675764
  have htrace : WordTrace (prefixWord ++ tailWord_2675764) baseStart_2675764 baseEnd_2675764 := by
    simpa [prefixWord, tailWord_2675764, baseEnd_2675764] using wordTrace_append hprefix tailTrace_2675764
  have hstable : (prefixWord ++ tailWord_2675764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675764).length < 2 ^ (prefixWord ++ tailWord_2675764).sum := by decide
  have hdescent : baseEnd_2675764 < baseStart_2675764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675777 : List Nat := [1, 2, 5, 1, 3, 1, 1, 8]
def baseStart_2675777 : Nat := 118140960795 + 2675777 * 2 ^ 59
def prefixEnd_2675777 : Nat := 4983230072969 + 3 ^ 40 * 2675777 * 2
def baseEnd_2675777 : Nat := 101774794462643166213469

theorem tailTrace_2675777 : CollatzResearch.WordTrace tailWord_2675777 prefixEnd_2675777 101774794462643166213469 := by
  unfold tailWord_2675777
  simp only [CollatzResearch.WordTrace]
  refine ⟨97593604827124390174169585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65062403218082926782779723 97593604827124390174169585)
  ·
    refine ⟨73195203620343292630627189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97593604827124390174169585 73195203620343292630627189)
    ·
      refine ⟨6862050339407183684121299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73195203620343292630627189 6862050339407183684121299)
      ·
        refine ⟨10293075509110775526181949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862050339407183684121299 10293075509110775526181949)
        ·
          refine ⟨3859903315916540822318231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10293075509110775526181949 3859903315916540822318231)
          ·
            refine ⟨5789854973874811233477347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859903315916540822318231 5789854973874811233477347)
            ·
              refine ⟨8684782460812216850216021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789854973874811233477347 8684782460812216850216021)
              ·
                refine ⟨101774794462643166213469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8684782460812216850216021 101774794462643166213469)
                ·
                  rfl

theorem cell22_2675777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 8].length) (baseStart_2675777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675777 prefixEnd_2675777 := by exact prefixLift 2675777
  have htrace : WordTrace (prefixWord ++ tailWord_2675777) baseStart_2675777 baseEnd_2675777 := by
    simpa [prefixWord, tailWord_2675777, baseEnd_2675777] using wordTrace_append hprefix tailTrace_2675777
  have hstable : (prefixWord ++ tailWord_2675777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675777).length < 2 ^ (prefixWord ++ tailWord_2675777).sum := by decide
  have hdescent : baseEnd_2675777 < baseStart_2675777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675809 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 1, 3]
def baseStart_2675809 : Nat := 118140960795 + 2675809 * 2 ^ 59
def prefixEnd_2675809 : Nat := 4983230072969 + 3 ^ 40 * 2675809 * 2
def baseEnd_2675809 : Nat := 915984104417751079121123

theorem tailTrace_2675809 : CollatzResearch.WordTrace tailWord_2675809 prefixEnd_2675809 915984104417751079121123 := by
  unfold tailWord_2675809
  simp only [CollatzResearch.WordTrace]
  refine ⟨97594771963008459639334481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65063181308672306426222987 97594771963008459639334481)
  ·
    refine ⟨73196078972256344729500861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97594771963008459639334481 73196078972256344729500861)
    ·
      refine ⟨27448529614596129273562823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73196078972256344729500861 27448529614596129273562823)
      ·
        refine ⟨41172794421894193910344235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27448529614596129273562823 41172794421894193910344235)
        ·
          refine ⟨61759191632841290865516353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41172794421894193910344235 61759191632841290865516353)
          ·
            refine ⟨46319393724630968149137265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61759191632841290865516353 46319393724630968149137265)
            ·
              refine ⟨34739545293473226111852949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46319393724630968149137265 34739545293473226111852949)
              ·
                refine ⟨1628416185631557473993107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34739545293473226111852949 1628416185631557473993107)
                ·
                  refine ⟨2442624278447336210989661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628416185631557473993107 2442624278447336210989661)
                  ·
                    refine ⟨915984104417751079121123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442624278447336210989661 915984104417751079121123)
                    ·
                      rfl

theorem cell22_2675809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_2675809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675809 prefixEnd_2675809 := by exact prefixLift 2675809
  have htrace : WordTrace (prefixWord ++ tailWord_2675809) baseStart_2675809 baseEnd_2675809 := by
    simpa [prefixWord, tailWord_2675809, baseEnd_2675809] using wordTrace_append hprefix tailTrace_2675809
  have hstable : (prefixWord ++ tailWord_2675809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675809).length < 2 ^ (prefixWord ++ tailWord_2675809).sum := by decide
  have hdescent : baseEnd_2675809 < baseStart_2675809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675820 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_2675820 : Nat := 118140960795 + 2675820 * 2 ^ 59
def prefixEnd_2675820 : Nat := 4983230072969 + 3 ^ 40 * 2675820 * 2
def baseEnd_2675820 : Nat := 915987869942550717096089

theorem tailTrace_2675820 : CollatzResearch.WordTrace tailWord_2675820 prefixEnd_2675820 915987869942550717096089 := by
  unfold tailWord_2675820
  simp only [CollatzResearch.WordTrace]
  refine ⟨48797586582984304258992457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65063448777312405678656609 48797586582984304258992457)
  ·
    refine ⟨36598189937238228194244343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48797586582984304258992457 36598189937238228194244343)
    ·
      refine ⟨54897284905857342291366515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36598189937238228194244343 54897284905857342291366515)
      ·
        refine ⟨82345927358786013437049773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54897284905857342291366515 82345927358786013437049773)
        ·
          refine ⟨30879722759544755038893665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82345927358786013437049773 30879722759544755038893665)
          ·
            refine ⟨23159792069658566279170249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30879722759544755038893665 23159792069658566279170249)
            ·
              refine ⟨17369844052243924709377687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23159792069658566279170249 17369844052243924709377687)
              ·
                refine ⟨26054766078365887064066531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17369844052243924709377687 26054766078365887064066531)
                ·
                  refine ⟨39082149117548830596099797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26054766078365887064066531 39082149117548830596099797)
                  ·
                    refine ⟨915987869942550717096089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39082149117548830596099797 915987869942550717096089)
                    ·
                      rfl

theorem cell22_2675820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_2675820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675820 prefixEnd_2675820 := by exact prefixLift 2675820
  have htrace : WordTrace (prefixWord ++ tailWord_2675820) baseStart_2675820 baseEnd_2675820 := by
    simpa [prefixWord, tailWord_2675820, baseEnd_2675820] using wordTrace_append hprefix tailTrace_2675820
  have hstable : (prefixWord ++ tailWord_2675820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675820).length < 2 ^ (prefixWord ++ tailWord_2675820).sum := by decide
  have hdescent : baseEnd_2675820 < baseStart_2675820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675852 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_2675852 : Nat := 118140960795 + 2675852 * 2 ^ 59
def prefixEnd_2675852 : Nat := 4983230072969 + 3 ^ 40 * 2675852 * 2
def baseEnd_2675852 : Nat := 915998824196513300295991

theorem tailTrace_2675852 : CollatzResearch.WordTrace tailWord_2675852 prefixEnd_2675852 915998824196513300295991 := by
  unfold tailWord_2675852
  simp only [CollatzResearch.WordTrace]
  refine ⟨48798170150926338991574905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65064226867901785322099873 48798170150926338991574905)
  ·
    refine ⟨36598627613194754243681179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48798170150926338991574905 36598627613194754243681179)
    ·
      refine ⟨54897941419792131365521769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36598627613194754243681179 54897941419792131365521769)
      ·
        refine ⟨41173456064844098524141327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54897941419792131365521769 41173456064844098524141327)
        ·
          refine ⟨61760184097266147786211991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41173456064844098524141327 61760184097266147786211991)
          ·
            refine ⟨92640276145899221679317987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61760184097266147786211991 92640276145899221679317987)
            ·
              refine ⟨138960414218848832518976981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92640276145899221679317987 138960414218848832518976981)
              ·
                refine ⟨3256884708254269512163523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138960414218848832518976981 3256884708254269512163523)
                ·
                  refine ⟨4885327062381404268245285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256884708254269512163523 4885327062381404268245285)
                  ·
                    refine ⟨915998824196513300295991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4885327062381404268245285 915998824196513300295991)
                    ·
                      rfl

theorem cell22_2675852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_2675852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675852 prefixEnd_2675852 := by exact prefixLift 2675852
  have htrace : WordTrace (prefixWord ++ tailWord_2675852) baseStart_2675852 baseEnd_2675852 := by
    simpa [prefixWord, tailWord_2675852, baseEnd_2675852] using wordTrace_append hprefix tailTrace_2675852
  have hstable : (prefixWord ++ tailWord_2675852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675852).length < 2 ^ (prefixWord ++ tailWord_2675852).sum := by decide
  have hdescent : baseEnd_2675852 < baseStart_2675852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675897 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_2675897 : Nat := 118140960795 + 2675897 * 2 ^ 59
def prefixEnd_2675897 : Nat := 4983230072969 + 3 ^ 40 * 2675897 * 2
def baseEnd_2675897 : Nat := 916014228616148182920853

theorem tailTrace_2675897 : CollatzResearch.WordTrace tailWord_2675897 prefixEnd_2675897 916014228616148182920853 := by
  unfold tailWord_2675897
  simp only [CollatzResearch.WordTrace]
  refine ⟨97597981586689650668537945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65065321057793100445691963 97597981586689650668537945)
  ·
    refine ⟨73198486190017238001403459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97597981586689650668537945 73198486190017238001403459)
    ·
      refine ⟨109797729285025857002105189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73198486190017238001403459 109797729285025857002105189)
      ·
        refine ⟨20587074240942348187894723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109797729285025857002105189 20587074240942348187894723)
        ·
          refine ⟨30880611361413522281842085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20587074240942348187894723 30880611361413522281842085)
          ·
            refine ⟨5790114630265035427845391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30880611361413522281842085 5790114630265035427845391)
            ·
              refine ⟨8685171945397553141768087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790114630265035427845391 8685171945397553141768087)
              ·
                refine ⟨13027757918096329712652131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685171945397553141768087 13027757918096329712652131)
                ·
                  refine ⟨19541636877144494568978197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13027757918096329712652131 19541636877144494568978197)
                  ·
                    refine ⟨916014228616148182920853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19541636877144494568978197 916014228616148182920853)
                    ·
                      rfl

theorem cell22_2675897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_2675897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675897 prefixEnd_2675897 := by exact prefixLift 2675897
  have htrace : WordTrace (prefixWord ++ tailWord_2675897) baseStart_2675897 baseEnd_2675897 := by
    simpa [prefixWord, tailWord_2675897, baseEnd_2675897] using wordTrace_append hprefix tailTrace_2675897
  have hstable : (prefixWord ++ tailWord_2675897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675897).length < 2 ^ (prefixWord ++ tailWord_2675897).sum := by decide
  have hdescent : baseEnd_2675897 < baseStart_2675897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675933 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2675933 : Nat := 118140960795 + 2675933 * 2 ^ 59
def prefixEnd_2675933 : Nat := 4983230072969 + 3 ^ 40 * 2675933 * 2
def baseEnd_2675933 : Nat := 916026552151856089020743

theorem tailTrace_2675933 : CollatzResearch.WordTrace tailWord_2675933 prefixEnd_2675933 916026552151856089020743 := by
  unfold tailWord_2675933
  simp only [CollatzResearch.WordTrace]
  refine ⟨97599294614559228816848453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65066196409706152544565635 97599294614559228816848453)
  ·
    refine ⟨18299867740229855403159085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97599294614559228816848453 18299867740229855403159085)
    ·
      refine ⟨6862450402586195776184657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18299867740229855403159085 6862450402586195776184657)
      ·
        refine ⟨5146837801939646832138493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862450402586195776184657 5146837801939646832138493)
        ·
          refine ⟨1930064175727367562051935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5146837801939646832138493 1930064175727367562051935)
          ·
            refine ⟨2895096263591051343077903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930064175727367562051935 2895096263591051343077903)
            ·
              refine ⟨4342644395386577014616855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895096263591051343077903 4342644395386577014616855)
              ·
                refine ⟨6513966593079865521925283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4342644395386577014616855 6513966593079865521925283)
                ·
                  refine ⟨9770949889619798282887925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6513966593079865521925283 9770949889619798282887925)
                  ·
                    refine ⟨916026552151856089020743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9770949889619798282887925 916026552151856089020743)
                    ·
                      rfl

theorem cell22_2675933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2675933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675933 prefixEnd_2675933 := by exact prefixLift 2675933
  have htrace : WordTrace (prefixWord ++ tailWord_2675933) baseStart_2675933 baseEnd_2675933 := by
    simpa [prefixWord, tailWord_2675933, baseEnd_2675933] using wordTrace_append hprefix tailTrace_2675933
  have hstable : (prefixWord ++ tailWord_2675933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675933).length < 2 ^ (prefixWord ++ tailWord_2675933).sum := by decide
  have hdescent : baseEnd_2675933 < baseStart_2675933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2675944 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2675944 : Nat := 118140960795 + 2675944 * 2 ^ 59
def prefixEnd_2675944 : Nat := 4983230072969 + 3 ^ 40 * 2675944 * 2
def baseEnd_2675944 : Nat := 916030317676655726995709

theorem tailTrace_2675944 : CollatzResearch.WordTrace tailWord_2675944 prefixEnd_2675944 916030317676655726995709 := by
  unfold tailWord_2675944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48799847908759688847749443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65066463878346251796999257 48799847908759688847749443)
  ·
    refine ⟨73199771863139533271624165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48799847908759688847749443 73199771863139533271624165)
    ·
      refine ⟨13724957224338662488429531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73199771863139533271624165 13724957224338662488429531)
      ·
        refine ⟨20587435836507993732644297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13724957224338662488429531 20587435836507993732644297)
        ·
          refine ⟨15440576877380995299483223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20587435836507993732644297 15440576877380995299483223)
          ·
            refine ⟨23160865316071492949224835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15440576877380995299483223 23160865316071492949224835)
            ·
              refine ⟨34741297974107239423837253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23160865316071492949224835 34741297974107239423837253)
              ·
                refine ⟨6513993370145107391969485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34741297974107239423837253 6513993370145107391969485)
                ·
                  refine ⟨2442747513804415271988557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6513993370145107391969485 2442747513804415271988557)
                  ·
                    refine ⟨916030317676655726995709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442747513804415271988557 916030317676655726995709)
                    ·
                      rfl

theorem cell22_2675944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2675944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2675944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2675944 prefixEnd_2675944 := by exact prefixLift 2675944
  have htrace : WordTrace (prefixWord ++ tailWord_2675944) baseStart_2675944 baseEnd_2675944 := by
    simpa [prefixWord, tailWord_2675944, baseEnd_2675944] using wordTrace_append hprefix tailTrace_2675944
  have hstable : (prefixWord ++ tailWord_2675944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2675944).length < 2 ^ (prefixWord ++ tailWord_2675944).sum := by decide
  have hdescent : baseEnd_2675944 < baseStart_2675944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2675944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676004 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_2676004 : Nat := 118140960795 + 2676004 * 2 ^ 59
def prefixEnd_2676004 : Nat := 4983230072969 + 3 ^ 40 * 2676004 * 2
def baseEnd_2676004 : Nat := 916050856902835570495525

theorem tailTrace_2676004 : CollatzResearch.WordTrace tailWord_2676004 prefixEnd_2676004 916050856902835570495525 := by
  unfold tailWord_2676004
  simp only [CollatzResearch.WordTrace]
  refine ⟨48800942098651003971341533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65067922798201338628455377 48800942098651003971341533)
  ·
    refine ⟨18300353286994126489253075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48800942098651003971341533 18300353286994126489253075)
    ·
      refine ⟨27450529930491189733879613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18300353286994126489253075 27450529930491189733879613)
      ·
        refine ⟨10293948723934196150204855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27450529930491189733879613 10293948723934196150204855)
        ·
          refine ⟨15440923085901294225307283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10293948723934196150204855 15440923085901294225307283)
          ·
            refine ⟨23161384628851941337960925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15440923085901294225307283 23161384628851941337960925)
            ·
              refine ⟨8685519235819478001735347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23161384628851941337960925 8685519235819478001735347)
              ·
                refine ⟨13028278853729217002603021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8685519235819478001735347 13028278853729217002603021)
                ·
                  refine ⟨4885604570148456375976133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13028278853729217002603021 4885604570148456375976133)
                  ·
                    refine ⟨916050856902835570495525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4885604570148456375976133 916050856902835570495525)
                    ·
                      rfl

theorem cell22_2676004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_2676004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676004 prefixEnd_2676004 := by exact prefixLift 2676004
  have htrace : WordTrace (prefixWord ++ tailWord_2676004) baseStart_2676004 baseEnd_2676004 := by
    simpa [prefixWord, tailWord_2676004, baseEnd_2676004] using wordTrace_append hprefix tailTrace_2676004
  have hstable : (prefixWord ++ tailWord_2676004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676004).length < 2 ^ (prefixWord ++ tailWord_2676004).sum := by decide
  have hdescent : baseEnd_2676004 < baseStart_2676004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676029 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_2676029 : Nat := 118140960795 + 2676029 * 2 ^ 59
def prefixEnd_2676029 : Nat := 4983230072969 + 3 ^ 40 * 2676029 * 2
def baseEnd_2676029 : Nat := 916059414913743838620449

theorem tailTrace_2676029 : CollatzResearch.WordTrace tailWord_2676029 prefixEnd_2676029 916059414913743838620449 := by
  unfold tailWord_2676029
  simp only [CollatzResearch.WordTrace]
  refine ⟨97602796022211437212343141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65068530681474291474895427 97602796022211437212343141)
  ·
    refine ⟨18300524254164644477314339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97602796022211437212343141 18300524254164644477314339)
    ·
      refine ⟨27450786381246966715971509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18300524254164644477314339 27450786381246966715971509)
      ·
        refine ⟨2573511223241903129622329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27450786381246966715971509 2573511223241903129622329)
        ·
          refine ⟨1930133417431427347216747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2573511223241903129622329 1930133417431427347216747)
          ·
            refine ⟨2895200126147141020825121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930133417431427347216747 2895200126147141020825121)
            ·
              refine ⟨2171400094610355765618841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895200126147141020825121 2171400094610355765618841)
              ·
                refine ⟨1628550070957766824214131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171400094610355765618841 1628550070957766824214131)
                ·
                  refine ⟨2442825106436650236321197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628550070957766824214131 2442825106436650236321197)
                  ·
                    refine ⟨916059414913743838620449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442825106436650236321197 916059414913743838620449)
                    ·
                      rfl

theorem cell22_2676029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_2676029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676029 prefixEnd_2676029 := by exact prefixLift 2676029
  have htrace : WordTrace (prefixWord ++ tailWord_2676029) baseStart_2676029 baseEnd_2676029 := by
    simpa [prefixWord, tailWord_2676029, baseEnd_2676029] using wordTrace_append hprefix tailTrace_2676029
  have hstable : (prefixWord ++ tailWord_2676029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676029).length < 2 ^ (prefixWord ++ tailWord_2676029).sum := by decide
  have hdescent : baseEnd_2676029 < baseStart_2676029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676079 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 5, 3]
def baseStart_2676079 : Nat := 118140960795 + 2676079 * 2 ^ 59
def prefixEnd_2676079 : Nat := 4983230072969 + 3 ^ 40 * 2676079 * 2
def baseEnd_2676079 : Nat := 916076530935560374870295

theorem tailTrace_2676079 : CollatzResearch.WordTrace tailWord_2676079 prefixEnd_2676079 916076530935560374870295 := by
  unfold tailWord_2676079
  simp only [CollatzResearch.WordTrace]
  refine ⟨97604619672030295751663291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65069746448020197167775527 97604619672030295751663291)
  ·
    refine ⟨146406929508045443627494937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97604619672030295751663291 146406929508045443627494937)
    ·
      refine ⟨109805197131034082720621203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146406929508045443627494937 109805197131034082720621203)
      ·
        refine ⟨164707795696551124080931805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109805197131034082720621203 164707795696551124080931805)
        ·
          refine ⟨61765423386206671530349427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164707795696551124080931805 61765423386206671530349427)
          ·
            refine ⟨92648135079310007295524141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61765423386206671530349427 92648135079310007295524141)
            ·
              refine ⟨34743050654741252735821553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92648135079310007295524141 34743050654741252735821553)
              ·
                refine ⟨26057287991055939551866165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34743050654741252735821553 26057287991055939551866165)
                ·
                  refine ⟨2442870749161494332987453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26057287991055939551866165 2442870749161494332987453)
                  ·
                    refine ⟨916076530935560374870295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442870749161494332987453 916076530935560374870295)
                    ·
                      rfl

theorem cell22_2676079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_2676079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676079 prefixEnd_2676079 := by exact prefixLift 2676079
  have htrace : WordTrace (prefixWord ++ tailWord_2676079) baseStart_2676079 baseEnd_2676079 := by
    simpa [prefixWord, tailWord_2676079, baseEnd_2676079] using wordTrace_append hprefix tailTrace_2676079
  have hstable : (prefixWord ++ tailWord_2676079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676079).length < 2 ^ (prefixWord ++ tailWord_2676079).sum := by decide
  have hdescent : baseEnd_2676079 < baseStart_2676079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676085 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2676085 : Nat := 118140960795 + 2676085 * 2 ^ 59
def prefixEnd_2676085 : Nat := 4983230072969 + 3 ^ 40 * 2676085 * 2
def baseEnd_2676085 : Nat := 916078584858178359220277

theorem tailTrace_2676085 : CollatzResearch.WordTrace tailWord_2676085 prefixEnd_2676085 916078584858178359220277 := by
  unfold tailWord_2676085
  simp only [CollatzResearch.WordTrace]
  refine ⟨97604838510008558776381709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65069892340005705850921139 97604838510008558776381709)
  ·
    refine ⟨36601814441253209541143141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97604838510008558776381709 36601814441253209541143141)
    ·
      refine ⟨6862840207734976788964339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36601814441253209541143141 6862840207734976788964339)
      ·
        refine ⟨10294260311602465183446509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862840207734976788964339 10294260311602465183446509)
        ·
          refine ⟨3860347616850924443792441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10294260311602465183446509 3860347616850924443792441)
          ·
            refine ⟨2895260712638193332844331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3860347616850924443792441 2895260712638193332844331)
            ·
              refine ⟨4342891068957289999266497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895260712638193332844331 4342891068957289999266497)
              ·
                refine ⟨3257168301717967499449873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342891068957289999266497 3257168301717967499449873)
                ·
                  refine ⟨2442876226288475624587405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257168301717967499449873 2442876226288475624587405)
                  ·
                    refine ⟨916078584858178359220277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442876226288475624587405 916078584858178359220277)
                    ·
                      rfl

theorem cell22_2676085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2676085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676085 prefixEnd_2676085 := by exact prefixLift 2676085
  have htrace : WordTrace (prefixWord ++ tailWord_2676085) baseStart_2676085 baseEnd_2676085 := by
    simpa [prefixWord, tailWord_2676085, baseEnd_2676085] using wordTrace_append hprefix tailTrace_2676085
  have hstable : (prefixWord ++ tailWord_2676085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676085).length < 2 ^ (prefixWord ++ tailWord_2676085).sum := by decide
  have hdescent : baseEnd_2676085 < baseStart_2676085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676130 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2676130 : Nat := 118140960795 + 2676130 * 2 ^ 59
def prefixEnd_2676130 : Nat := 4983230072969 + 3 ^ 40 * 2676130 * 2
def baseEnd_2676130 : Nat := 916093989277813241845139

theorem tailTrace_2676130 : CollatzResearch.WordTrace tailWord_2676130 prefixEnd_2676130 916093989277813241845139 := by
  unfold tailWord_2676130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24401619948711382865442461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65070986529897020974513229 24401619948711382865442461)
  ·
    refine ⟨9150607480766768574540923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24401619948711382865442461 9150607480766768574540923)
    ·
      refine ⟨13725911221150152861811385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150607480766768574540923 13725911221150152861811385)
      ·
        refine ⟨10294433415862614646358539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13725911221150152861811385 10294433415862614646358539)
        ·
          refine ⟨15441650123793921969537809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294433415862614646358539 15441650123793921969537809)
          ·
            refine ⟨11581237592845441477153357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15441650123793921969537809 11581237592845441477153357)
            ·
              refine ⟨4342964097317040553932509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11581237592845441477153357 4342964097317040553932509)
              ·
                refine ⟨1628611536493890207724691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4342964097317040553932509 1628611536493890207724691)
                ·
                  refine ⟨2442917304740835311587037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628611536493890207724691 2442917304740835311587037)
                  ·
                    refine ⟨916093989277813241845139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442917304740835311587037 916093989277813241845139)
                    ·
                      rfl

theorem cell22_2676130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2676130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676130 prefixEnd_2676130 := by exact prefixLift 2676130
  have htrace : WordTrace (prefixWord ++ tailWord_2676130) baseStart_2676130 baseEnd_2676130 := by
    simpa [prefixWord, tailWord_2676130, baseEnd_2676130] using wordTrace_append hprefix tailTrace_2676130
  have hstable : (prefixWord ++ tailWord_2676130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676130).length < 2 ^ (prefixWord ++ tailWord_2676130).sum := by decide
  have hdescent : baseEnd_2676130 < baseStart_2676130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676169 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_2676169 : Nat := 118140960795 + 2676169 * 2 ^ 59
def prefixEnd_2676169 : Nat := 4983230072969 + 3 ^ 40 * 2676169 * 2
def baseEnd_2676169 : Nat := 916107339774830140120019

theorem tailTrace_2676169 : CollatzResearch.WordTrace tailWord_2676169 prefixEnd_2676169 916107339774830140120019 := by
  unfold tailWord_2676169
  simp only [CollatzResearch.WordTrace]
  refine ⟨97607902241704241122439561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65071934827802827414959707 97607902241704241122439561)
  ·
    refine ⟨73205926681278180841829671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97607902241704241122439561 73205926681278180841829671)
    ·
      refine ⟨109808890021917271262744507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73205926681278180841829671 109808890021917271262744507)
      ·
        refine ⟨164713335032875906894116761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109808890021917271262744507 164713335032875906894116761)
        ·
          refine ⟨123535001274656930170587571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164713335032875906894116761 123535001274656930170587571)
          ·
            refine ⟨185302501911985395255881357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123535001274656930170587571 185302501911985395255881357)
            ·
              refine ⟨69488438216994523220955509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185302501911985395255881357 69488438216994523220955509)
              ·
                refine ⟨6514541082843236551964579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69488438216994523220955509 6514541082843236551964579)
                ·
                  refine ⟨9771811624264854827946869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514541082843236551964579 9771811624264854827946869)
                  ·
                    refine ⟨916107339774830140120019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9771811624264854827946869 916107339774830140120019)
                    ·
                      rfl

theorem cell22_2676169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_2676169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676169 prefixEnd_2676169 := by exact prefixLift 2676169
  have htrace : WordTrace (prefixWord ++ tailWord_2676169) baseStart_2676169 baseEnd_2676169 := by
    simpa [prefixWord, tailWord_2676169, baseEnd_2676169] using wordTrace_append hprefix tailTrace_2676169
  have hstable : (prefixWord ++ tailWord_2676169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676169).length < 2 ^ (prefixWord ++ tailWord_2676169).sum := by decide
  have hdescent : baseEnd_2676169 < baseStart_2676169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676184 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_2676184 : Nat := 118140960795 + 2676184 * 2 ^ 59
def prefixEnd_2676184 : Nat := 4983230072969 + 3 ^ 40 * 2676184 * 2
def baseEnd_2676184 : Nat := 916112474581375100994973

theorem tailTrace_2676184 : CollatzResearch.WordTrace tailWord_2676184 prefixEnd_2676184 916112474581375100994973 := by
  unfold tailWord_2676184
  simp only [CollatzResearch.WordTrace]
  refine ⟨48804224668324949342117803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65072299557766599122823737 48804224668324949342117803)
  ·
    refine ⟨73206337002487424013176705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48804224668324949342117803 73206337002487424013176705)
    ·
      refine ⟨54904752751865568009882529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73206337002487424013176705 54904752751865568009882529)
      ·
        refine ⟨41178564563899176007411897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54904752751865568009882529 41178564563899176007411897)
        ·
          refine ⟨30883923422924382005558923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41178564563899176007411897 30883923422924382005558923)
          ·
            refine ⟨46325885134386573008338385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30883923422924382005558923 46325885134386573008338385)
            ·
              refine ⟨34744413850789929756253789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46325885134386573008338385 34744413850789929756253789)
              ·
                refine ⟨13029155194046223658595171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34744413850789929756253789 13029155194046223658595171)
                ·
                  refine ⟨19543732791069335487892757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13029155194046223658595171 19543732791069335487892757)
                  ·
                    refine ⟨916112474581375100994973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19543732791069335487892757 916112474581375100994973)
                    ·
                      rfl

theorem cell22_2676184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_2676184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676184 prefixEnd_2676184 := by exact prefixLift 2676184
  have htrace : WordTrace (prefixWord ++ tailWord_2676184) baseStart_2676184 baseEnd_2676184 := by
    simpa [prefixWord, tailWord_2676184, baseEnd_2676184] using wordTrace_append hprefix tailTrace_2676184
  have hstable : (prefixWord ++ tailWord_2676184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676184).length < 2 ^ (prefixWord ++ tailWord_2676184).sum := by decide
  have hdescent : baseEnd_2676184 < baseStart_2676184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676186 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_2676186 : Nat := 118140960795 + 2676186 * 2 ^ 59
def prefixEnd_2676186 : Nat := 4983230072969 + 3 ^ 40 * 2676186 * 2
def baseEnd_2676186 : Nat := 916113159222247762444967

theorem tailTrace_2676186 : CollatzResearch.WordTrace tailWord_2676186 prefixEnd_2676186 916113159222247762444967 := by
  unfold tailWord_2676186
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402130570660663256452103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65072348188428435350538941 24402130570660663256452103)
  ·
    refine ⟨36603195855990994884678155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24402130570660663256452103 36603195855990994884678155)
    ·
      refine ⟨54904793783986492327017233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36603195855990994884678155 54904793783986492327017233)
      ·
        refine ⟨41178595337989869245262925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54904793783986492327017233 41178595337989869245262925)
        ·
          refine ⟨15441973251746200966973597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41178595337989869245262925 15441973251746200966973597)
          ·
            refine ⟨5790739969404825362615099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15441973251746200966973597 5790739969404825362615099)
            ·
              refine ⟨8686109954107238043922649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790739969404825362615099 8686109954107238043922649)
              ·
                refine ⟨6514582465580428532941987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8686109954107238043922649 6514582465580428532941987)
                ·
                  refine ⟨9771873698370642799412981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6514582465580428532941987 9771873698370642799412981)
                  ·
                    refine ⟨916113159222247762444967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9771873698370642799412981 916113159222247762444967)
                    ·
                      rfl

theorem cell22_2676186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_2676186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676186 prefixEnd_2676186 := by exact prefixLift 2676186
  have htrace : WordTrace (prefixWord ++ tailWord_2676186) baseStart_2676186 baseEnd_2676186 := by
    simpa [prefixWord, tailWord_2676186, baseEnd_2676186] using wordTrace_append hprefix tailTrace_2676186
  have hstable : (prefixWord ++ tailWord_2676186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676186).length < 2 ^ (prefixWord ++ tailWord_2676186).sum := by decide
  have hdescent : baseEnd_2676186 < baseStart_2676186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676199 : List Nat := [1, 1, 5, 2, 1, 12]
def baseStart_2676199 : Nat := 118140960795 + 2676199 * 2 ^ 59
def prefixEnd_2676199 : Nat := 4983230072969 + 3 ^ 40 * 2676199 * 2
def baseEnd_2676199 : Nat := 11310093943060741504567

theorem tailTrace_2676199 : CollatzResearch.WordTrace tailWord_2676199 prefixEnd_2676199 11310093943060741504567 := by
  unfold tailWord_2676199
  simp only [CollatzResearch.WordTrace]
  refine ⟨97608996431595556246031651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65072664287730370830687767 97608996431595556246031651)
  ·
    refine ⟨146413494647393334369047477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97608996431595556246031651 146413494647393334369047477)
    ·
      refine ⟨13726265123193125097098201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146413494647393334369047477 13726265123193125097098201)
      ·
        refine ⟨10294698842394843822823651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13726265123193125097098201 10294698842394843822823651)
        ·
          refine ⟨15442048263592265734235477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294698842394843822823651 15442048263592265734235477)
          ·
            refine ⟨11310093943060741504567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15442048263592265734235477 11310093943060741504567)
            ·
              rfl

theorem cell22_2676199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 12].length) (baseStart_2676199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676199 prefixEnd_2676199 := by exact prefixLift 2676199
  have htrace : WordTrace (prefixWord ++ tailWord_2676199) baseStart_2676199 baseEnd_2676199 := by
    simpa [prefixWord, tailWord_2676199, baseEnd_2676199] using wordTrace_append hprefix tailTrace_2676199
  have hstable : (prefixWord ++ tailWord_2676199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676199).length < 2 ^ (prefixWord ++ tailWord_2676199).sum := by decide
  have hdescent : baseEnd_2676199 < baseStart_2676199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676205 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 4]
def baseStart_2676205 : Nat := 118140960795 + 2676205 * 2 ^ 59
def prefixEnd_2676205 : Nat := 4983230072969 + 3 ^ 40 * 2676205 * 2
def baseEnd_2676205 : Nat := 305373221103512682073303

theorem tailTrace_2676205 : CollatzResearch.WordTrace tailWord_2676205 prefixEnd_2676205 305373221103512682073303 := by
  unfold tailWord_2676205
  simp only [CollatzResearch.WordTrace]
  refine ⟨97609215269573819270750069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65072810179715879513833379 97609215269573819270750069)
  ·
    refine ⟨9150863931522545556632819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97609215269573819270750069 9150863931522545556632819)
    ·
      refine ⟨13726295897283818334949229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150863931522545556632819 13726295897283818334949229)
      ·
        refine ⟨5147360961481431875605961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13726295897283818334949229 5147360961481431875605961)
        ·
          refine ⟨3860520721111073906704471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5147360961481431875605961 3860520721111073906704471)
          ·
            refine ⟨5790781081666610860056707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860520721111073906704471 5790781081666610860056707)
            ·
              refine ⟨8686171622499916290085061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790781081666610860056707 8686171622499916290085061)
              ·
                refine ⟨1628657179218734304390949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8686171622499916290085061 1628657179218734304390949)
                ·
                  refine ⟨305373221103512682073303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628657179218734304390949 305373221103512682073303)
                  ·
                    rfl

theorem cell22_2676205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_2676205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676205 prefixEnd_2676205 := by exact prefixLift 2676205
  have htrace : WordTrace (prefixWord ++ tailWord_2676205) baseStart_2676205 baseEnd_2676205 := by
    simpa [prefixWord, tailWord_2676205, baseEnd_2676205] using wordTrace_append hprefix tailTrace_2676205
  have hstable : (prefixWord ++ tailWord_2676205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676205).length < 2 ^ (prefixWord ++ tailWord_2676205).sum := by decide
  have hdescent : baseEnd_2676205 < baseStart_2676205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676216 : List Nat := [2, 1, 2, 1, 1, 7, 1, 7]
def baseStart_2676216 : Nat := 118140960795 + 2676216 * 2 ^ 59
def prefixEnd_2676216 : Nat := 4983230072969 + 3 ^ 40 * 2676216 * 2
def baseEnd_2676216 : Nat := 101791492092815298243875

theorem tailTrace_2676216 : CollatzResearch.WordTrace tailWord_2676216 prefixEnd_2676216 101791492092815298243875 := by
  unfold tailWord_2676216
  simp only [CollatzResearch.WordTrace]
  refine ⟨48804808236266984074700251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65073077648355978766267001 48804808236266984074700251)
  ·
    refine ⟨73207212354400476112050377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48804808236266984074700251 73207212354400476112050377)
    ·
      refine ⟨54905409265800357084037783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73207212354400476112050377 54905409265800357084037783)
      ·
        refine ⟨82358113898700535626056675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54905409265800357084037783 82358113898700535626056675)
        ·
          refine ⟨123537170848050803439085013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82358113898700535626056675 123537170848050803439085013)
          ·
            refine ⟨2895402441751190705603555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 123537170848050803439085013 2895402441751190705603555)
            ·
              refine ⟨4343103662626786058405333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895402441751190705603555 4343103662626786058405333)
              ·
                refine ⟨101791492092815298243875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4343103662626786058405333 101791492092815298243875)
                ·
                  rfl

theorem cell22_2676216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_2676216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676216 prefixEnd_2676216 := by exact prefixLift 2676216
  have htrace : WordTrace (prefixWord ++ tailWord_2676216) baseStart_2676216 baseEnd_2676216 := by
    simpa [prefixWord, tailWord_2676216, baseEnd_2676216] using wordTrace_append hprefix tailTrace_2676216
  have hstable : (prefixWord ++ tailWord_2676216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676216).length < 2 ^ (prefixWord ++ tailWord_2676216).sum := by decide
  have hdescent : baseEnd_2676216 < baseStart_2676216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676229 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2676229 : Nat := 118140960795 + 2676229 * 2 ^ 59
def prefixEnd_2676229 : Nat := 4983230072969 + 3 ^ 40 * 2676229 * 2
def baseEnd_2676229 : Nat := 916127879001009983619835

theorem tailTrace_2676229 : CollatzResearch.WordTrace tailWord_2676229 prefixEnd_2676229 916127879001009983619835 := by
  unfold tailWord_2676229
  simp only [CollatzResearch.WordTrace]
  refine ⟨97610090621486871369623741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65073393747657914246415827 97610090621486871369623741)
  ·
    refine ⟨36603783983057576763608903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97610090621486871369623741 36603783983057576763608903)
    ·
      refine ⟨54905675974586365145413355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36603783983057576763608903 54905675974586365145413355)
      ·
        refine ⟨82358513961879547718120033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54905675974586365145413355 82358513961879547718120033)
        ·
          refine ⟨61768885471409660788590025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82358513961879547718120033 61768885471409660788590025)
          ·
            refine ⟨46326664103557245591442519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61768885471409660788590025 46326664103557245591442519)
            ·
              refine ⟨69489996155335868387163779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46326664103557245591442519 69489996155335868387163779)
              ·
                refine ⟨104234994233003802580745669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69489996155335868387163779 104234994233003802580745669)
                ·
                  refine ⟨19544061418688212983889813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104234994233003802580745669 19544061418688212983889813)
                  ·
                    refine ⟨916127879001009983619835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19544061418688212983889813 916127879001009983619835)
                    ·
                      rfl

theorem cell22_2676229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2676229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676229 prefixEnd_2676229 := by exact prefixLift 2676229
  have htrace : WordTrace (prefixWord ++ tailWord_2676229) baseStart_2676229 baseEnd_2676229 := by
    simpa [prefixWord, tailWord_2676229, baseEnd_2676229] using wordTrace_append hprefix tailTrace_2676229
  have hstable : (prefixWord ++ tailWord_2676229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676229).length < 2 ^ (prefixWord ++ tailWord_2676229).sum := by decide
  have hdescent : baseEnd_2676229 < baseStart_2676229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676235 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 2, 4]
def baseStart_2676235 : Nat := 118140960795 + 2676235 * 2 ^ 59
def prefixEnd_2676235 : Nat := 4983230072969 + 3 ^ 40 * 2676235 * 2
def baseEnd_2676235 : Nat := 916129932923627967969817

theorem tailTrace_2676235 : CollatzResearch.WordTrace tailWord_2676235 prefixEnd_2676235 916129932923627967969817 := by
  unfold tailWord_2676235
  simp only [CollatzResearch.WordTrace]
  refine ⟨97610309459465134394342159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65073539639643422929561439 97610309459465134394342159)
  ·
    refine ⟨146415464189197701591513239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97610309459465134394342159 146415464189197701591513239)
    ·
      refine ⟨219623196283796552387269859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146415464189197701591513239 219623196283796552387269859)
      ·
        refine ⟨329434794425694828580904789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219623196283796552387269859 329434794425694828580904789)
        ·
          refine ⟨1930281998588055636216239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 329434794425694828580904789 1930281998588055636216239)
          ·
            refine ⟨2895422997882083454324359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930281998588055636216239 2895422997882083454324359)
            ·
              refine ⟨4343134496823125181486539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895422997882083454324359 4343134496823125181486539)
              ·
                refine ⟨6514701745234687772229809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343134496823125181486539 6514701745234687772229809)
                ·
                  refine ⟨4886026308926015829172357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514701745234687772229809 4886026308926015829172357)
                  ·
                    refine ⟨916129932923627967969817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886026308926015829172357 916129932923627967969817)
                    ·
                      rfl

theorem cell22_2676235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 4].length) (baseStart_2676235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676235 prefixEnd_2676235 := by exact prefixLift 2676235
  have htrace : WordTrace (prefixWord ++ tailWord_2676235) baseStart_2676235 baseEnd_2676235 := by
    simpa [prefixWord, tailWord_2676235, baseEnd_2676235] using wordTrace_append hprefix tailTrace_2676235
  have hstable : (prefixWord ++ tailWord_2676235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676235).length < 2 ^ (prefixWord ++ tailWord_2676235).sum := by decide
  have hdescent : baseEnd_2676235 < baseStart_2676235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676254 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2676254 : Nat := 118140960795 + 2676254 * 2 ^ 59
def prefixEnd_2676254 : Nat := 4983230072969 + 3 ^ 40 * 2676254 * 2
def baseEnd_2676254 : Nat := 916136437011918251744759

theorem tailTrace_2676254 : CollatzResearch.WordTrace tailWord_2676254 prefixEnd_2676254 916136437011918251744759 := by
  unfold tailWord_2676254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12201375305799537579910477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65074001630930867092855877 12201375305799537579910477)
  ·
    refine ⟨4575515739674826592466429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12201375305799537579910477 4575515739674826592466429)
    ·
      refine ⟨1715818402378059972174911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4575515739674826592466429 1715818402378059972174911)
      ·
        refine ⟨2573727603567089958262367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715818402378059972174911 2573727603567089958262367)
        ·
          refine ⟨3860591405350634937393551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573727603567089958262367 3860591405350634937393551)
          ·
            refine ⟨5790887108025952406090327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860591405350634937393551 5790887108025952406090327)
            ·
              refine ⟨8686330662038928609135491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790887108025952406090327 8686330662038928609135491)
              ·
                refine ⟨13029495993058392913703237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8686330662038928609135491 13029495993058392913703237)
                ·
                  refine ⟨2443030498698448671319357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13029495993058392913703237 2443030498698448671319357)
                  ·
                    refine ⟨916136437011918251744759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443030498698448671319357 916136437011918251744759)
                    ·
                      rfl

theorem cell22_2676254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2676254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676254 prefixEnd_2676254 := by exact prefixLift 2676254
  have htrace : WordTrace (prefixWord ++ tailWord_2676254) baseStart_2676254 baseEnd_2676254 := by
    simpa [prefixWord, tailWord_2676254, baseEnd_2676254] using wordTrace_append hprefix tailTrace_2676254
  have hstable : (prefixWord ++ tailWord_2676254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676254).length < 2 ^ (prefixWord ++ tailWord_2676254).sum := by decide
  have hdescent : baseEnd_2676254 < baseStart_2676254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676308 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2676308 : Nat := 118140960795 + 2676308 * 2 ^ 59
def prefixEnd_2676308 : Nat := 4983230072969 + 3 ^ 40 * 2676308 * 2
def baseEnd_2676308 : Nat := 916154922315480110894593

theorem tailTrace_2676308 : CollatzResearch.WordTrace tailWord_2676308 prefixEnd_2676308 916154922315480110894593 := by
  unfold tailWord_2676308
  simp only [CollatzResearch.WordTrace]
  refine ⟨48806485994100333930874789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65075314658800445241166385 48806485994100333930874789)
  ·
    refine ⟨9151216123893812612039023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48806485994100333930874789 9151216123893812612039023)
    ·
      refine ⟨13726824185840718918058535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9151216123893812612039023 13726824185840718918058535)
      ·
        refine ⟨20590236278761078377087803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13726824185840718918058535 20590236278761078377087803)
        ·
          refine ⟨30885354418141617565631705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20590236278761078377087803 30885354418141617565631705)
          ·
            refine ⟨23164015813606213174223779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30885354418141617565631705 23164015813606213174223779)
            ·
              refine ⟨34746023720409319761335669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23164015813606213174223779 34746023720409319761335669)
              ·
                refine ⟨3257439723788373727625219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34746023720409319761335669 3257439723788373727625219)
                ·
                  refine ⟨4886159585682560591437829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257439723788373727625219 4886159585682560591437829)
                  ·
                    refine ⟨916154922315480110894593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886159585682560591437829 916154922315480110894593)
                    ·
                      rfl

theorem cell22_2676308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2676308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676308 prefixEnd_2676308 := by exact prefixLift 2676308
  have htrace : WordTrace (prefixWord ++ tailWord_2676308) baseStart_2676308 baseEnd_2676308 := by
    simpa [prefixWord, tailWord_2676308, baseEnd_2676308] using wordTrace_append hprefix tailTrace_2676308
  have hstable : (prefixWord ++ tailWord_2676308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676308).length < 2 ^ (prefixWord ++ tailWord_2676308).sum := by decide
  have hdescent : baseEnd_2676308 < baseStart_2676308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676323 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 6]
def baseStart_2676323 : Nat := 118140960795 + 2676323 * 2 ^ 59
def prefixEnd_2676323 : Nat := 4983230072969 + 3 ^ 40 * 2676323 * 2
def baseEnd_2676323 : Nat := 305386685707341690589849

theorem tailTrace_2676323 : CollatzResearch.WordTrace tailWord_2676323 prefixEnd_2676323 305386685707341690589849 := by
  unfold tailWord_2676323
  simp only [CollatzResearch.WordTrace]
  refine ⟨97613519083146325423545623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65075679388764216949030415 97613519083146325423545623)
  ·
    refine ⟨146420278624719488135318435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97613519083146325423545623 146420278624719488135318435)
    ·
      refine ⟨219630417937079232202977653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146420278624719488135318435 219630417937079232202977653)
      ·
        refine ⟨20590351681601178019029155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219630417937079232202977653 20590351681601178019029155)
        ·
          refine ⟨30885527522401767028543733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20590351681601178019029155 30885527522401767028543733)
          ·
            refine ⟨2895518205225165658925975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30885527522401767028543733 2895518205225165658925975)
            ·
              refine ⟨4343277307837748488388963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895518205225165658925975 4343277307837748488388963)
              ·
                refine ⟨6514915961756622732583445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343277307837748488388963 6514915961756622732583445)
                ·
                  refine ⟨305386685707341690589849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6514915961756622732583445 305386685707341690589849)
                  ·
                    rfl

theorem cell22_2676323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 6].length) (baseStart_2676323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676323 prefixEnd_2676323 := by exact prefixLift 2676323
  have htrace : WordTrace (prefixWord ++ tailWord_2676323) baseStart_2676323 baseEnd_2676323 := by
    simpa [prefixWord, tailWord_2676323, baseEnd_2676323] using wordTrace_append hprefix tailTrace_2676323
  have hstable : (prefixWord ++ tailWord_2676323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676323).length < 2 ^ (prefixWord ++ tailWord_2676323).sum := by decide
  have hdescent : baseEnd_2676323 < baseStart_2676323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676342 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_2676342 : Nat := 118140960795 + 2676342 * 2 ^ 59
def prefixEnd_2676342 : Nat := 4983230072969 + 3 ^ 40 * 2676342 * 2
def baseEnd_2676342 : Nat := 916166561210315355544489

theorem tailTrace_2676342 : CollatzResearch.WordTrace tailWord_2676342 prefixEnd_2676342 916166561210315355544489 := by
  unfold tailWord_2676342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100888254379843229280455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65076141380051661112324853 6100888254379843229280455)
  ·
    refine ⟨9151332381569764843920683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100888254379843229280455 9151332381569764843920683)
    ·
      refine ⟨13726998572354647265881025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9151332381569764843920683 13726998572354647265881025)
      ·
        refine ⟨10295248929265985449410769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13726998572354647265881025 10295248929265985449410769)
        ·
          refine ⟨7721436696949489087058077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10295248929265985449410769 7721436696949489087058077)
          ·
            refine ⟨2895538761356058407646779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7721436696949489087058077 2895538761356058407646779)
            ·
              refine ⟨4343308142034087611470169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895538761356058407646779 4343308142034087611470169)
              ·
                refine ⟨3257481106525565708602627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4343308142034087611470169 3257481106525565708602627)
                ·
                  refine ⟨4886221659788348562903941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257481106525565708602627 4886221659788348562903941)
                  ·
                    refine ⟨916166561210315355544489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886221659788348562903941 916166561210315355544489)
                    ·
                      rfl

theorem cell22_2676342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_2676342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676342 prefixEnd_2676342 := by exact prefixLift 2676342
  have htrace : WordTrace (prefixWord ++ tailWord_2676342) baseStart_2676342 baseEnd_2676342 := by
    simpa [prefixWord, tailWord_2676342, baseEnd_2676342] using wordTrace_append hprefix tailTrace_2676342
  have hstable : (prefixWord ++ tailWord_2676342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676342).length < 2 ^ (prefixWord ++ tailWord_2676342).sum := by decide
  have hdescent : baseEnd_2676342 < baseStart_2676342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676353 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2676353 : Nat := 118140960795 + 2676353 * 2 ^ 59
def prefixEnd_2676353 : Nat := 4983230072969 + 3 ^ 40 * 2676353 * 2
def baseEnd_2676353 : Nat := 916170326735114993519455

theorem tailTrace_2676353 : CollatzResearch.WordTrace tailWord_2676353 prefixEnd_2676353 916170326735114993519455 := by
  unfold tailWord_2676353
  simp only [CollatzResearch.WordTrace]
  refine ⟨97614613273037640547137713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65076408848691760364758475 97614613273037640547137713)
  ·
    refine ⟨73210959954778230410353285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97614613273037640547137713 73210959954778230410353285)
    ·
      refine ⟨13727054991520918201941241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73210959954778230410353285 13727054991520918201941241)
      ·
        refine ⟨10295291243640688651455931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13727054991520918201941241 10295291243640688651455931)
        ·
          refine ⟨15442936865461032977183897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10295291243640688651455931 15442936865461032977183897)
          ·
            refine ⟨11582202649095774732887923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15442936865461032977183897 11582202649095774732887923)
            ·
              refine ⟨17373303973643662099331885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11582202649095774732887923 17373303973643662099331885)
              ·
                refine ⟨6514988990116373287249457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17373303973643662099331885 6514988990116373287249457)
                ·
                  refine ⟨4886241742587279965437093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6514988990116373287249457 4886241742587279965437093)
                  ·
                    refine ⟨916170326735114993519455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886241742587279965437093 916170326735114993519455)
                    ·
                      rfl

theorem cell22_2676353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2676353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676353 prefixEnd_2676353 := by exact prefixLift 2676353
  have htrace : WordTrace (prefixWord ++ tailWord_2676353) baseStart_2676353 baseEnd_2676353 := by
    simpa [prefixWord, tailWord_2676353, baseEnd_2676353] using wordTrace_append hprefix tailTrace_2676353
  have hstable : (prefixWord ++ tailWord_2676353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676353).length < 2 ^ (prefixWord ++ tailWord_2676353).sum := by decide
  have hdescent : baseEnd_2676353 < baseStart_2676353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676458 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_2676458 : Nat := 118140960795 + 2676458 * 2 ^ 59
def prefixEnd_2676458 : Nat := 4983230072969 + 3 ^ 40 * 2676458 * 2
def baseEnd_2676458 : Nat := 305402090126976573214711

theorem tailTrace_2676458 : CollatzResearch.WordTrace tailWord_2676458 prefixEnd_2676458 305402090126976573214711 := by
  unfold tailWord_2676458
  simp only [CollatzResearch.WordTrace]
  refine ⟨24404610734414310869927507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65078961958438162319806685 24404610734414310869927507)
  ·
    refine ⟨36606916101621466304891261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24404610734414310869927507 36606916101621466304891261)
    ·
      refine ⟨13727593538108049864334223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36606916101621466304891261 13727593538108049864334223)
      ·
        refine ⟨20591390307162074796501335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13727593538108049864334223 20591390307162074796501335)
        ·
          refine ⟨30887085460743112194752003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20591390307162074796501335 30887085460743112194752003)
          ·
            refine ⟨46330628191114668292128005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30887085460743112194752003 46330628191114668292128005)
            ·
              refine ⟨8686992785834000304774001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46330628191114668292128005 8686992785834000304774001)
              ·
                refine ⟨6515244589375500228580501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8686992785834000304774001 6515244589375500228580501)
                ·
                  refine ⟨305402090126976573214711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6515244589375500228580501 305402090126976573214711)
                  ·
                    rfl

theorem cell22_2676458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_2676458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676458 prefixEnd_2676458 := by exact prefixLift 2676458
  have htrace : WordTrace (prefixWord ++ tailWord_2676458) baseStart_2676458 baseEnd_2676458 := by
    simpa [prefixWord, tailWord_2676458, baseEnd_2676458] using wordTrace_append hprefix tailTrace_2676458
  have hstable : (prefixWord ++ tailWord_2676458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676458).length < 2 ^ (prefixWord ++ tailWord_2676458).sum := by decide
  have hdescent : baseEnd_2676458 < baseStart_2676458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676468 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2676468 : Nat := 118140960795 + 2676468 * 2 ^ 59
def prefixEnd_2676468 : Nat := 4983230072969 + 3 ^ 40 * 2676468 * 2
def baseEnd_2676468 : Nat := 916209693585293026894103

theorem tailTrace_2676468 : CollatzResearch.WordTrace tailWord_2676468 prefixEnd_2676468 916209693585293026894103 := by
  unfold tailWord_2676468
  simp only [CollatzResearch.WordTrace]
  refine ⟨48809403833810507593787029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65079205111747343458382705 48809403833810507593787029)
  ·
    refine ⟨2287940804709867543458767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48809403833810507593787029 2287940804709867543458767)
    ·
      refine ⟨3431911207064801315188151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287940804709867543458767 3431911207064801315188151)
      ·
        refine ⟨5147866810597201972782227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431911207064801315188151 5147866810597201972782227)
        ·
          refine ⟨7721800215895802959173341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5147866810597201972782227 7721800215895802959173341)
          ·
            refine ⟨2895675080960926109690003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7721800215895802959173341 2895675080960926109690003)
            ·
              refine ⟨4343512621441389164535005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895675080960926109690003 4343512621441389164535005)
              ·
                refine ⟨1628817233040520936700627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343512621441389164535005 1628817233040520936700627)
                ·
                  refine ⟨2443225849560781405050941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628817233040520936700627 2443225849560781405050941)
                  ·
                    refine ⟨916209693585293026894103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443225849560781405050941 916209693585293026894103)
                    ·
                      rfl

theorem cell22_2676468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2676468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676468 prefixEnd_2676468 := by exact prefixLift 2676468
  have htrace : WordTrace (prefixWord ++ tailWord_2676468) baseStart_2676468 baseEnd_2676468 := by
    simpa [prefixWord, tailWord_2676468, baseEnd_2676468] using wordTrace_append hprefix tailTrace_2676468
  have hstable : (prefixWord ++ tailWord_2676468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676468).length < 2 ^ (prefixWord ++ tailWord_2676468).sum := by decide
  have hdescent : baseEnd_2676468 < baseStart_2676468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676490 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_2676490 : Nat := 118140960795 + 2676490 * 2 ^ 59
def prefixEnd_2676490 : Nat := 4983230072969 + 3 ^ 40 * 2676490 * 2
def baseEnd_2676490 : Nat := 916217224634892302844035

theorem tailTrace_2676490 : CollatzResearch.WordTrace tailWord_2676490 prefixEnd_2676490 916217224634892302844035 := by
  unfold tailWord_2676490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24404902518385328236218731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65079740049027541963249949 24404902518385328236218731)
  ·
    refine ⟨36607353777577992354328097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24404902518385328236218731 36607353777577992354328097)
    ·
      refine ⟨27455515333183494265746073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36607353777577992354328097 27455515333183494265746073)
      ·
        refine ⟨20591636499887620699309555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27455515333183494265746073 20591636499887620699309555)
        ·
          refine ⟨30887454749831431048964333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20591636499887620699309555 30887454749831431048964333)
          ·
            refine ⟨11582795531186786643361625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30887454749831431048964333 11582795531186786643361625)
            ·
              refine ⟨8687096648390089982521219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11582795531186786643361625 8687096648390089982521219)
              ·
                refine ⟨13030644972585134973781829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8687096648390089982521219 13030644972585134973781829)
                ·
                  refine ⟨2443245932359712807584093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13030644972585134973781829 2443245932359712807584093)
                  ·
                    refine ⟨916217224634892302844035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443245932359712807584093 916217224634892302844035)
                    ·
                      rfl

theorem cell22_2676490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_2676490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676490 prefixEnd_2676490 := by exact prefixLift 2676490
  have htrace : WordTrace (prefixWord ++ tailWord_2676490) baseStart_2676490 baseEnd_2676490 := by
    simpa [prefixWord, tailWord_2676490, baseEnd_2676490] using wordTrace_append hprefix tailTrace_2676490
  have hstable : (prefixWord ++ tailWord_2676490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676490).length < 2 ^ (prefixWord ++ tailWord_2676490).sum := by decide
  have hdescent : baseEnd_2676490 < baseStart_2676490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676503 : List Nat := [1, 1, 3, 4, 2, 1, 1, 9]
def baseStart_2676503 : Nat := 118140960795 + 2676503 * 2 ^ 59
def prefixEnd_2676503 : Nat := 4983230072969 + 3 ^ 40 * 2676503 * 2
def baseEnd_2676503 : Nat := 101802408311173844696555

theorem tailTrace_2676503 : CollatzResearch.WordTrace tailWord_2676503 prefixEnd_2676503 101802408311173844696555 := by
  unfold tailWord_2676503
  simp only [CollatzResearch.WordTrace]
  refine ⟨97620084222494216165098163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65080056148329477443398775 97620084222494216165098163)
  ·
    refine ⟨146430126333741324247647245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97620084222494216165098163 146430126333741324247647245)
    ·
      refine ⟨54911297375152996592867717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146430126333741324247647245 54911297375152996592867717)
      ·
        refine ⟨10295868257841186861162697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54911297375152996592867717 10295868257841186861162697)
        ·
          refine ⟨7721901193380890145872023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10295868257841186861162697 7721901193380890145872023)
          ·
            refine ⟨11582851790071335218808035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7721901193380890145872023 11582851790071335218808035)
            ·
              refine ⟨17374277685107002828212053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11582851790071335218808035 17374277685107002828212053)
              ·
                refine ⟨101802408311173844696555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17374277685107002828212053 101802408311173844696555)
                ·
                  rfl

theorem cell22_2676503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 9].length) (baseStart_2676503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676503 prefixEnd_2676503 := by exact prefixLift 2676503
  have htrace : WordTrace (prefixWord ++ tailWord_2676503) baseStart_2676503 baseEnd_2676503 := by
    simpa [prefixWord, tailWord_2676503, baseEnd_2676503] using wordTrace_append hprefix tailTrace_2676503
  have hstable : (prefixWord ++ tailWord_2676503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676503).length < 2 ^ (prefixWord ++ tailWord_2676503).sum := by decide
  have hdescent : baseEnd_2676503 < baseStart_2676503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676565 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 5]
def baseStart_2676565 : Nat := 118140960795 + 2676565 * 2 ^ 59
def prefixEnd_2676565 : Nat := 4983230072969 + 3 ^ 40 * 2676565 * 2
def baseEnd_2676565 : Nat := 305414299555872369072935

theorem tailTrace_2676565 : CollatzResearch.WordTrace tailWord_2676565 prefixEnd_2676565 305414299555872369072935 := by
  unfold tailWord_2676565
  simp only [CollatzResearch.WordTrace]
  refine ⟨97622345548269600753855149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65081563698846400502570099 97622345548269600753855149)
  ·
    refine ⟨36608379580601100282695681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97622345548269600753855149 36608379580601100282695681)
    ·
      refine ⟨27456284685450825212021761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36608379580601100282695681 27456284685450825212021761)
      ·
        refine ⟨20592213514088118909016321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27456284685450825212021761 20592213514088118909016321)
        ·
          refine ⟨15444160135566089181762241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20592213514088118909016321 15444160135566089181762241)
          ·
            refine ⟨11583120101674566886321681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15444160135566089181762241 11583120101674566886321681)
            ·
              refine ⟨8687340076255925164741261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11583120101674566886321681 8687340076255925164741261)
              ·
                refine ⟨3257752528595971936777973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8687340076255925164741261 3257752528595971936777973)
                ·
                  refine ⟨305414299555872369072935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3257752528595971936777973 305414299555872369072935)
                  ·
                    rfl

theorem cell22_2676565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_2676565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676565 prefixEnd_2676565 := by exact prefixLift 2676565
  have htrace : WordTrace (prefixWord ++ tailWord_2676565) baseStart_2676565 baseEnd_2676565 := by
    simpa [prefixWord, tailWord_2676565, baseEnd_2676565] using wordTrace_append hprefix tailTrace_2676565
  have hstable : (prefixWord ++ tailWord_2676565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676565).length < 2 ^ (prefixWord ++ tailWord_2676565).sum := by decide
  have hdescent : baseEnd_2676565 < baseStart_2676565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676593 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 8]
def baseStart_2676593 : Nat := 118140960795 + 2676593 * 2 ^ 59
def prefixEnd_2676593 : Nat := 4983230072969 + 3 ^ 40 * 2676593 * 2
def baseEnd_2676593 : Nat := 305417494546611455839573

theorem tailTrace_2676593 : CollatzResearch.WordTrace tailWord_2676593 prefixEnd_2676593 305417494546611455839573 := by
  unfold tailWord_2676593
  simp only [CollatzResearch.WordTrace]
  refine ⟨97623366792168161535874433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65082244528112107690582955 97623366792168161535874433)
  ·
    refine ⟨73217525094126121151905825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97623366792168161535874433 73217525094126121151905825)
    ·
      refine ⟨54913143820594590863929369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73217525094126121151905825 54913143820594590863929369)
      ·
        refine ⟨41184857865445943147947027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54913143820594590863929369 41184857865445943147947027)
        ·
          refine ⟨61777286798168914721920541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41184857865445943147947027 61777286798168914721920541)
          ·
            refine ⟨23166482549313343020720203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61777286798168914721920541 23166482549313343020720203)
            ·
              refine ⟨34749723823970014531080305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23166482549313343020720203 34749723823970014531080305)
              ·
                refine ⟨26062292867977510898310229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34749723823970014531080305 26062292867977510898310229)
                ·
                  refine ⟨305417494546611455839573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26062292867977510898310229 305417494546611455839573)
                  ·
                    rfl

theorem cell22_2676593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_2676593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676593 prefixEnd_2676593 := by exact prefixLift 2676593
  have htrace : WordTrace (prefixWord ++ tailWord_2676593) baseStart_2676593 baseEnd_2676593 := by
    simpa [prefixWord, tailWord_2676593, baseEnd_2676593] using wordTrace_append hprefix tailTrace_2676593
  have hstable : (prefixWord ++ tailWord_2676593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676593).length < 2 ^ (prefixWord ++ tailWord_2676593).sum := by decide
  have hdescent : baseEnd_2676593 < baseStart_2676593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676625 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_2676625 : Nat := 118140960795 + 2676625 * 2 ^ 59
def prefixEnd_2676625 : Nat := 4983230072969 + 3 ^ 40 * 2676625 * 2
def baseEnd_2676625 : Nat := 916263437893796950718621

theorem tailTrace_2676625 : CollatzResearch.WordTrace tailWord_2676625 prefixEnd_2676625 916263437893796950718621 := by
  unfold tailWord_2676625
  simp only [CollatzResearch.WordTrace]
  refine ⟨97624533928052231001039329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65083022618701487334026219 97624533928052231001039329)
  ·
    refine ⟨73218400446039173250779497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97624533928052231001039329 73218400446039173250779497)
    ·
      refine ⟨54913800334529379938084623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73218400446039173250779497 54913800334529379938084623)
      ·
        refine ⟨82370700501794069907126935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54913800334529379938084623 82370700501794069907126935)
        ·
          refine ⟨123556050752691104860690403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82370700501794069907126935 123556050752691104860690403)
          ·
            refine ⟨185334076129036657291035605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123556050752691104860690403 185334076129036657291035605)
            ·
              refine ⟨4343767409274296655258647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 185334076129036657291035605 4343767409274296655258647)
              ·
                refine ⟨6515651113911444982887971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343767409274296655258647 6515651113911444982887971)
                ·
                  refine ⟨9773476670867167474331957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6515651113911444982887971 9773476670867167474331957)
                  ·
                    refine ⟨916263437893796950718621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9773476670867167474331957 916263437893796950718621)
                    ·
                      rfl

theorem cell22_2676625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_2676625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676625 prefixEnd_2676625 := by exact prefixLift 2676625
  have htrace : WordTrace (prefixWord ++ tailWord_2676625) baseStart_2676625 baseEnd_2676625 := by
    simpa [prefixWord, tailWord_2676625, baseEnd_2676625] using wordTrace_append hprefix tailTrace_2676625
  have hstable : (prefixWord ++ tailWord_2676625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676625).length < 2 ^ (prefixWord ++ tailWord_2676625).sum := by decide
  have hdescent : baseEnd_2676625 < baseStart_2676625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676640 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_2676640 : Nat := 118140960795 + 2676640 * 2 ^ 59
def prefixEnd_2676640 : Nat := 4983230072969 + 3 ^ 40 * 2676640 * 2
def baseEnd_2676640 : Nat := 916268572700341911593575

theorem tailTrace_2676640 : CollatzResearch.WordTrace tailWord_2676640 prefixEnd_2676640 916268572700341911593575 := by
  unfold tailWord_2676640
  simp only [CollatzResearch.WordTrace]
  refine ⟨48812540511498944281417687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65083387348665259041890249 48812540511498944281417687)
  ·
    refine ⟨73218810767248416422126531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48812540511498944281417687 73218810767248416422126531)
    ·
      refine ⟨109828216150872624633189797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73218810767248416422126531 109828216150872624633189797)
      ·
        refine ⟨20592790528288617118723087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109828216150872624633189797 20592790528288617118723087)
        ·
          refine ⟨30889185792432925678084631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20592790528288617118723087 30889185792432925678084631)
          ·
            refine ⟨46333778688649388517126947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30889185792432925678084631 46333778688649388517126947)
            ·
              refine ⟨69500668032974082775690421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46333778688649388517126947 69500668032974082775690421)
              ·
                refine ⟨6515687628091320260220977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69500668032974082775690421 6515687628091320260220977)
                ·
                  refine ⟨4886765721068490195165733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6515687628091320260220977 4886765721068490195165733)
                  ·
                    refine ⟨916268572700341911593575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886765721068490195165733 916268572700341911593575)
                    ·
                      rfl

theorem cell22_2676640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_2676640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676640 prefixEnd_2676640 := by exact prefixLift 2676640
  have htrace : WordTrace (prefixWord ++ tailWord_2676640) baseStart_2676640 baseEnd_2676640 := by
    simpa [prefixWord, tailWord_2676640, baseEnd_2676640] using wordTrace_append hprefix tailTrace_2676640
  have hstable : (prefixWord ++ tailWord_2676640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676640).length < 2 ^ (prefixWord ++ tailWord_2676640).sum := by decide
  have hdescent : baseEnd_2676640 < baseStart_2676640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676644 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2676644 : Nat := 118140960795 + 2676644 * 2 ^ 59
def prefixEnd_2676644 : Nat := 4983230072969 + 3 ^ 40 * 2676644 * 2
def baseEnd_2676644 : Nat := 305423313994029078164521

theorem tailTrace_2676644 : CollatzResearch.WordTrace tailWord_2676644 prefixEnd_2676644 305423313994029078164521 := by
  unfold tailWord_2676644
  simp only [CollatzResearch.WordTrace]
  refine ⟨48812613457491698622990493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65083484609988931497320657 48812613457491698622990493)
  ·
    refine ⟨18304730046559386983621435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48812613457491698622990493 18304730046559386983621435)
    ·
      refine ⟨27457095069839080475432153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18304730046559386983621435 27457095069839080475432153)
      ·
        refine ⟨20592821302379310356574115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27457095069839080475432153 20592821302379310356574115)
        ·
          refine ⟨30889231953568965534861173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20592821302379310356574115 30889231953568965534861173)
          ·
            refine ⟨2895865495647090518893235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30889231953568965534861173 2895865495647090518893235)
            ·
              refine ⟨4343798243470635778339853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895865495647090518893235 4343798243470635778339853)
              ·
                refine ⟨1628924341301488416877445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343798243470635778339853 1628924341301488416877445)
                ·
                  refine ⟨305423313994029078164521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628924341301488416877445 305423313994029078164521)
                  ·
                    rfl

theorem cell22_2676644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2676644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676644 prefixEnd_2676644 := by exact prefixLift 2676644
  have htrace : WordTrace (prefixWord ++ tailWord_2676644) baseStart_2676644 baseEnd_2676644 := by
    simpa [prefixWord, tailWord_2676644, baseEnd_2676644] using wordTrace_append hprefix tailTrace_2676644
  have hstable : (prefixWord ++ tailWord_2676644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676644).length < 2 ^ (prefixWord ++ tailWord_2676644).sum := by decide
  have hdescent : baseEnd_2676644 < baseStart_2676644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676657 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2676657 : Nat := 118140960795 + 2676657 * 2 ^ 59
def prefixEnd_2676657 : Nat := 4983230072969 + 3 ^ 40 * 2676657 * 2
def baseEnd_2676657 : Nat := 916274392147759533918523

theorem tailTrace_2676657 : CollatzResearch.WordTrace tailWord_2676657 prefixEnd_2676657 916274392147759533918523 := by
  unfold tailWord_2676657
  simp only [CollatzResearch.WordTrace]
  refine ⟨97625701063936300466204225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65083800709290866977469483 97625701063936300466204225)
  ·
    refine ⟨73219275797952225349653169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97625701063936300466204225 73219275797952225349653169)
    ·
      refine ⟨54914456848464169012239877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73219275797952225349653169 54914456848464169012239877)
      ·
        refine ⟨10296460659087031689794977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54914456848464169012239877 10296460659087031689794977)
        ·
          refine ⟨7722345494315273767346233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10296460659087031689794977 7722345494315273767346233)
          ·
            refine ⟨5791759120736455325509675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7722345494315273767346233 5791759120736455325509675)
            ·
              refine ⟨8687638681104682988264513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791759120736455325509675 8687638681104682988264513)
              ·
                refine ⟨6515729010828512241198385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8687638681104682988264513 6515729010828512241198385)
                ·
                  refine ⟨4886796758121384180898789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6515729010828512241198385 4886796758121384180898789)
                  ·
                    refine ⟨916274392147759533918523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886796758121384180898789 916274392147759533918523)
                    ·
                      rfl

theorem cell22_2676657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2676657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676657 prefixEnd_2676657 := by exact prefixLift 2676657
  have htrace : WordTrace (prefixWord ++ tailWord_2676657) baseStart_2676657 baseEnd_2676657 := by
    simpa [prefixWord, tailWord_2676657, baseEnd_2676657] using wordTrace_append hprefix tailTrace_2676657
  have hstable : (prefixWord ++ tailWord_2676657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676657).length < 2 ^ (prefixWord ++ tailWord_2676657).sum := by decide
  have hdescent : baseEnd_2676657 < baseStart_2676657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676721 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 1, 3]
def baseStart_2676721 : Nat := 118140960795 + 2676721 * 2 ^ 59
def prefixEnd_2676721 : Nat := 4983230072969 + 3 ^ 40 * 2676721 * 2
def baseEnd_2676721 : Nat := 916296300655684700318327

theorem tailTrace_2676721 : CollatzResearch.WordTrace tailWord_2676721 prefixEnd_2676721 916296300655684700318327 := by
  unfold tailWord_2676721
  simp only [CollatzResearch.WordTrace]
  refine ⟨97628035335704439396534017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65085356890469626264356011 97628035335704439396534017)
  ·
    refine ⟨73221026501778329547400513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97628035335704439396534017 73221026501778329547400513)
    ·
      refine ⟨54915769876333747160550385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73221026501778329547400513 54915769876333747160550385)
      ·
        refine ⟨41186827407250310370412789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54915769876333747160550385 41186827407250310370412789)
        ·
          refine ⟨3861265069429716597226199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41186827407250310370412789 3861265069429716597226199)
          ·
            refine ⟨5791897604144574895839299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861265069429716597226199 5791897604144574895839299)
            ·
              refine ⟨8687846406216862343758949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791897604144574895839299 8687846406216862343758949)
              ·
                refine ⟨1628971201165661689454803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8687846406216862343758949 1628971201165661689454803)
                ·
                  refine ⟨2443456801748492534182205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628971201165661689454803 2443456801748492534182205)
                  ·
                    refine ⟨916296300655684700318327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443456801748492534182205 916296300655684700318327)
                    ·
                      rfl

theorem cell22_2676721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_2676721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676721 prefixEnd_2676721 := by exact prefixLift 2676721
  have htrace : WordTrace (prefixWord ++ tailWord_2676721) baseStart_2676721 baseEnd_2676721 := by
    simpa [prefixWord, tailWord_2676721, baseEnd_2676721] using wordTrace_append hprefix tailTrace_2676721
  have hstable : (prefixWord ++ tailWord_2676721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676721).length < 2 ^ (prefixWord ++ tailWord_2676721).sum := by decide
  have hdescent : baseEnd_2676721 < baseStart_2676721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676734 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2676734 : Nat := 118140960795 + 2676734 * 2 ^ 59
def prefixEnd_2676734 : Nat := 4983230072969 + 3 ^ 40 * 2676734 * 2
def baseEnd_2676734 : Nat := 305433583607118999914429

theorem tailTrace_2676734 : CollatzResearch.WordTrace tailWord_2676734 prefixEnd_2676734 305433583607118999914429 := by
  unfold tailWord_2676734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12203563685582167827094657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65085672989771561744504837 12203563685582167827094657)
  ·
    refine ⟨9152672764186625870320993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12203563685582167827094657 9152672764186625870320993)
    ·
      refine ⟨6864504573139969402740745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9152672764186625870320993 6864504573139969402740745)
      ·
        refine ⟨5148378429854977052055559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6864504573139969402740745 5148378429854977052055559)
        ·
          refine ⟨7722567644782465578083339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148378429854977052055559 7722567644782465578083339)
          ·
            refine ⟨11583851467173698367125009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722567644782465578083339 11583851467173698367125009)
            ·
              refine ⟨8687888600380273775343757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11583851467173698367125009 8687888600380273775343757)
              ·
                refine ⟨3257958225142602665753909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8687888600380273775343757 3257958225142602665753909)
                ·
                  refine ⟨305433583607118999914429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3257958225142602665753909 305433583607118999914429)
                  ·
                    rfl

theorem cell22_2676734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2676734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676734 prefixEnd_2676734 := by exact prefixLift 2676734
  have htrace : WordTrace (prefixWord ++ tailWord_2676734) baseStart_2676734 baseEnd_2676734 := by
    simpa [prefixWord, tailWord_2676734, baseEnd_2676734] using wordTrace_append hprefix tailTrace_2676734
  have hstable : (prefixWord ++ tailWord_2676734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676734).length < 2 ^ (prefixWord ++ tailWord_2676734).sum := by decide
  have hdescent : baseEnd_2676734 < baseStart_2676734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676742 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2676742 : Nat := 118140960795 + 2676742 * 2 ^ 59
def prefixEnd_2676742 : Nat := 4983230072969 + 3 ^ 40 * 2676742 * 2
def baseEnd_2676742 : Nat := 916303489384847645543263

theorem tailTrace_2676742 : CollatzResearch.WordTrace tailWord_2676742 prefixEnd_2676742 916303489384847645543263 := by
  unfold tailWord_2676742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050900039644636249470265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65085867512418906655365653 3050900039644636249470265)
  ·
    refine ⟨2288175029733477187102699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3050900039644636249470265 2288175029733477187102699)
    ·
      refine ⟨3432262544600215780654049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288175029733477187102699 3432262544600215780654049)
      ·
        refine ⟨2574196908450161835490537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3432262544600215780654049 2574196908450161835490537)
        ·
          refine ⟨1930647681337621376617903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574196908450161835490537 1930647681337621376617903)
          ·
            refine ⟨2895971522006432064926855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930647681337621376617903 2895971522006432064926855)
            ·
              refine ⟨4343957283009648097390283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895971522006432064926855 4343957283009648097390283)
              ·
                refine ⟨6515935924514472146085425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343957283009648097390283 6515935924514472146085425)
                ·
                  refine ⟨4886951943385854109564069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6515935924514472146085425 4886951943385854109564069)
                  ·
                    refine ⟨916303489384847645543263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886951943385854109564069 916303489384847645543263)
                    ·
                      rfl

theorem cell22_2676742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2676742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676742 prefixEnd_2676742 := by exact prefixLift 2676742
  have htrace : WordTrace (prefixWord ++ tailWord_2676742) baseStart_2676742 baseEnd_2676742 := by
    simpa [prefixWord, tailWord_2676742, baseEnd_2676742] using wordTrace_append hprefix tailTrace_2676742
  have hstable : (prefixWord ++ tailWord_2676742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676742).length < 2 ^ (prefixWord ++ tailWord_2676742).sum := by decide
  have hdescent : baseEnd_2676742 < baseStart_2676742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676747 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 1, 4]
def baseStart_2676747 : Nat := 118140960795 + 2676747 * 2 ^ 59
def prefixEnd_2676747 : Nat := 4983230072969 + 3 ^ 40 * 2676747 * 2
def baseEnd_2676747 : Nat := 916305200987029299168247

theorem tailTrace_2676747 : CollatzResearch.WordTrace tailWord_2676747 prefixEnd_2676747 916305200987029299168247 := by
  unfold tailWord_2676747
  simp only [CollatzResearch.WordTrace]
  refine ⟨97628983633610245836980495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65085989089073497224653663 97628983633610245836980495)
  ·
    refine ⟨146443475450415368755470743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97628983633610245836980495 146443475450415368755470743)
    ·
      refine ⟨219665213175623053133206115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146443475450415368755470743 219665213175623053133206115)
      ·
        refine ⟨329497819763434579699809173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219665213175623053133206115 329497819763434579699809173)
        ·
          refine ⟨15445210301410995923428555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 329497819763434579699809173 15445210301410995923428555)
          ·
            refine ⟨23167815452116493885142833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15445210301410995923428555 23167815452116493885142833)
            ·
              refine ⟨17375861589087370413857125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23167815452116493885142833 17375861589087370413857125)
              ·
                refine ⟨3257974047953881952598211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17375861589087370413857125 3257974047953881952598211)
                ·
                  refine ⟨4886961071930822928897317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257974047953881952598211 4886961071930822928897317)
                  ·
                    refine ⟨916305200987029299168247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886961071930822928897317 916305200987029299168247)
                    ·
                      rfl

theorem cell22_2676747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 4].length) (baseStart_2676747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676747 prefixEnd_2676747 := by exact prefixLift 2676747
  have htrace : WordTrace (prefixWord ++ tailWord_2676747) baseStart_2676747 baseEnd_2676747 := by
    simpa [prefixWord, tailWord_2676747, baseEnd_2676747] using wordTrace_append hprefix tailTrace_2676747
  have hstable : (prefixWord ++ tailWord_2676747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676747).length < 2 ^ (prefixWord ++ tailWord_2676747).sum := by decide
  have hdescent : baseEnd_2676747 < baseStart_2676747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676764 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2676764 : Nat := 118140960795 + 2676764 * 2 ^ 59
def prefixEnd_2676764 : Nat := 4983230072969 + 3 ^ 40 * 2676764 * 2
def baseEnd_2676764 : Nat := 916311020434446921493195

theorem tailTrace_2676764 : CollatzResearch.WordTrace tailWord_2676764 prefixEnd_2676764 916311020434446921493195 := by
  unfold tailWord_2676764
  simp only [CollatzResearch.WordTrace]
  refine ⟨48814801837274328870174673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65086402449699105160232897 48814801837274328870174673)
  ·
    refine ⟨36611101377955746652631005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48814801837274328870174673 36611101377955746652631005)
    ·
      refine ⟨13729163016733404994736627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36611101377955746652631005 13729163016733404994736627)
      ·
        refine ⟨20593744525100107492104941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13729163016733404994736627 20593744525100107492104941)
        ·
          refine ⟨7722654196912540309539353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20593744525100107492104941 7722654196912540309539353)
          ·
            refine ⟨5791990647684405232154515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7722654196912540309539353 5791990647684405232154515)
            ·
              refine ⟨8687985971526607848231773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791990647684405232154515 8687985971526607848231773)
              ·
                refine ⟨3257994739322477943086915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8687985971526607848231773 3257994739322477943086915)
                ·
                  refine ⟨4886992108983716914630373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257994739322477943086915 4886992108983716914630373)
                  ·
                    refine ⟨916311020434446921493195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886992108983716914630373 916311020434446921493195)
                    ·
                      rfl

theorem cell22_2676764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2676764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676764 prefixEnd_2676764 := by exact prefixLift 2676764
  have htrace : WordTrace (prefixWord ++ tailWord_2676764) baseStart_2676764 baseEnd_2676764 := by
    simpa [prefixWord, tailWord_2676764, baseEnd_2676764] using wordTrace_append hprefix tailTrace_2676764
  have hstable : (prefixWord ++ tailWord_2676764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676764).length < 2 ^ (prefixWord ++ tailWord_2676764).sum := by decide
  have hdescent : baseEnd_2676764 < baseStart_2676764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676805 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2676805 : Nat := 118140960795 + 2676805 * 2 ^ 59
def prefixEnd_2676805 : Nat := 4983230072969 + 3 ^ 40 * 2676805 * 2
def baseEnd_2676805 : Nat := 916325055572336481218069

theorem tailTrace_2676805 : CollatzResearch.WordTrace tailWord_2676805 prefixEnd_2676805 916325055572336481218069 := by
  unfold tailWord_2676805
  simp only [CollatzResearch.WordTrace]
  refine ⟨97631099067400121742591869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65087399378266747828394579 97631099067400121742591869)
  ·
    refine ⟨36611662150275045653471951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97631099067400121742591869 36611662150275045653471951)
    ·
      refine ⟨54917493225412568480207927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36611662150275045653471951 54917493225412568480207927)
      ·
        refine ⟨82376239838118852720311891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54917493225412568480207927 82376239838118852720311891)
        ·
          refine ⟨123564359757178279080467837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82376239838118852720311891 123564359757178279080467837)
          ·
            refine ⟨46336634908941854655175439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123564359757178279080467837 46336634908941854655175439)
            ·
              refine ⟨69504952363412781982763159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46336634908941854655175439 69504952363412781982763159)
              ·
                refine ⟨104257428545119172974144739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69504952363412781982763159 104257428545119172974144739)
                ·
                  refine ⟨156386142817678759461217109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104257428545119172974144739 156386142817678759461217109)
                  ·
                    refine ⟨916325055572336481218069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156386142817678759461217109 916325055572336481218069)
                    ·
                      rfl

theorem cell22_2676805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2676805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676805 prefixEnd_2676805 := by exact prefixLift 2676805
  have htrace : WordTrace (prefixWord ++ tailWord_2676805) baseStart_2676805 baseEnd_2676805 := by
    simpa [prefixWord, tailWord_2676805, baseEnd_2676805] using wordTrace_append hprefix tailTrace_2676805
  have hstable : (prefixWord ++ tailWord_2676805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676805).length < 2 ^ (prefixWord ++ tailWord_2676805).sum := by decide
  have hdescent : baseEnd_2676805 < baseStart_2676805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676830 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2676830 : Nat := 118140960795 + 2676830 * 2 ^ 59
def prefixEnd_2676830 : Nat := 4983230072969 + 3 ^ 40 * 2676830 * 2
def baseEnd_2676830 : Nat := 305444537861081583114331

theorem tailTrace_2676830 : CollatzResearch.WordTrace tailWord_2676830 prefixEnd_2676830 305444537861081583114331 := by
  unfold tailWord_2676830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204001361538693876531493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65088007261539700674834629 12204001361538693876531493)
  ·
    refine ⟨2288250255288505101849655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12204001361538693876531493 2288250255288505101849655)
    ·
      refine ⟨3432375382932757652774483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288250255288505101849655 3432375382932757652774483)
      ·
        refine ⟨5148563074399136479161725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432375382932757652774483 5148563074399136479161725)
        ·
          refine ⟨1930711152899676179685647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5148563074399136479161725 1930711152899676179685647)
          ·
            refine ⟨2896066729349514269528471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930711152899676179685647 2896066729349514269528471)
            ·
              refine ⟨4344100094024271404292707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896066729349514269528471 4344100094024271404292707)
              ·
                refine ⟨6516150141036407106439061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344100094024271404292707 6516150141036407106439061)
                ·
                  refine ⟨305444537861081583114331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6516150141036407106439061 305444537861081583114331)
                  ·
                    rfl

theorem cell22_2676830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2676830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676830 prefixEnd_2676830 := by exact prefixLift 2676830
  have htrace : WordTrace (prefixWord ++ tailWord_2676830) baseStart_2676830 baseEnd_2676830 := by
    simpa [prefixWord, tailWord_2676830, baseEnd_2676830] using wordTrace_append hprefix tailTrace_2676830
  have hstable : (prefixWord ++ tailWord_2676830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676830).length < 2 ^ (prefixWord ++ tailWord_2676830).sum := by decide
  have hdescent : baseEnd_2676830 < baseStart_2676830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676946 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2676946 : Nat := 118140960795 + 2676946 * 2 ^ 59
def prefixEnd_2676946 : Nat := 4983230072969 + 3 ^ 40 * 2676946 * 2
def baseEnd_2676946 : Nat := 916373322753859113442637

theorem tailTrace_2676946 : CollatzResearch.WordTrace tailWord_2676946 prefixEnd_2676946 916373322753859113442637 := by
  unfold tailWord_2676946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409060439972325705868673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65090827839926201882316461 24409060439972325705868673)
  ·
    refine ⟨18306795329979244279401505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24409060439972325705868673 18306795329979244279401505)
    ·
      refine ⟨13730096497484433209551129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18306795329979244279401505 13730096497484433209551129)
      ·
        refine ⟨10297572373113324907163347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13730096497484433209551129 10297572373113324907163347)
        ·
          refine ⟨15446358559669987360745021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10297572373113324907163347 15446358559669987360745021)
          ·
            refine ⟨5792384459876245260279383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15446358559669987360745021 5792384459876245260279383)
            ·
              refine ⟨8688576689814367890419075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792384459876245260279383 8688576689814367890419075)
              ·
                refine ⟨13032865034721551835628613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8688576689814367890419075 13032865034721551835628613)
                ·
                  refine ⟨2443662194010290969180365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13032865034721551835628613 2443662194010290969180365)
                  ·
                    refine ⟨916373322753859113442637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443662194010290969180365 916373322753859113442637)
                    ·
                      rfl

theorem cell22_2676946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2676946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676946 prefixEnd_2676946 := by exact prefixLift 2676946
  have htrace : WordTrace (prefixWord ++ tailWord_2676946) baseStart_2676946 baseEnd_2676946 := by
    simpa [prefixWord, tailWord_2676946, baseEnd_2676946] using wordTrace_append hprefix tailTrace_2676946
  have hstable : (prefixWord ++ tailWord_2676946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676946).length < 2 ^ (prefixWord ++ tailWord_2676946).sum := by decide
  have hdescent : baseEnd_2676946 < baseStart_2676946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676963 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 1, 5]
def baseStart_2676963 : Nat := 118140960795 + 2676963 * 2 ^ 59
def prefixEnd_2676963 : Nat := 4983230072969 + 3 ^ 40 * 2676963 * 2
def baseEnd_2676963 : Nat := 916379142201276735767585

theorem tailTrace_2676963 : CollatzResearch.WordTrace tailWord_2676963 prefixEnd_2676963 916379142201276735767585 := by
  unfold tailWord_2676963
  simp only [CollatzResearch.WordTrace]
  refine ⟨97636861800827714726843543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65091241200551809817895695 97636861800827714726843543)
  ·
    refine ⟨146455292701241572090265315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97636861800827714726843543 146455292701241572090265315)
    ·
      refine ⟨219682939051862358135397973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146455292701241572090265315 219682939051862358135397973)
      ·
        refine ⟨2574409442014012009399195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 219682939051862358135397973 2574409442014012009399195)
        ·
          refine ⟨3861614163021018014098793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574409442014012009399195 3861614163021018014098793)
          ·
            refine ⟨2896210622265763510574095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861614163021018014098793 2896210622265763510574095)
            ·
              refine ⟨4344315933398645265861143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896210622265763510574095 4344315933398645265861143)
              ·
                refine ⟨6516473900097967898791715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344315933398645265861143 6516473900097967898791715)
                ·
                  refine ⟨9774710850146951848187573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6516473900097967898791715 9774710850146951848187573)
                  ·
                    refine ⟨916379142201276735767585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9774710850146951848187573 916379142201276735767585)
                    ·
                      rfl

theorem cell22_2676963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 5].length) (baseStart_2676963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2676963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2676963 prefixEnd_2676963 := by exact prefixLift 2676963
  have htrace : WordTrace (prefixWord ++ tailWord_2676963) baseStart_2676963 baseEnd_2676963 := by
    simpa [prefixWord, tailWord_2676963, baseEnd_2676963] using wordTrace_append hprefix tailTrace_2676963
  have hstable : (prefixWord ++ tailWord_2676963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676963).length < 2 ^ (prefixWord ++ tailWord_2676963).sum := by decide
  have hdescent : baseEnd_2676963 < baseStart_2676963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677004 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_2677004 : Nat := 118140960795 + 2677004 * 2 ^ 59
def prefixEnd_2677004 : Nat := 4983230072969 + 3 ^ 40 * 2677004 * 2
def baseEnd_2677004 : Nat := 305464392446388765164153

theorem tailTrace_2677004 : CollatzResearch.WordTrace tailWord_2677004 prefixEnd_2677004 305464392446388765164153 := by
  unfold tailWord_2677004
  simp only [CollatzResearch.WordTrace]
  refine ⟨48819178596839589364543033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65092238129119452486057377 48819178596839589364543033)
  ·
    refine ⟨36614383947629692023407275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48819178596839589364543033 36614383947629692023407275)
    ·
      refine ⟨54921575921444538035110913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36614383947629692023407275 54921575921444538035110913)
      ·
        refine ⟨41191181941083403526333185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54921575921444538035110913 41191181941083403526333185)
        ·
          refine ⟨30893386455812552644749889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41191181941083403526333185 30893386455812552644749889)
          ·
            refine ⟨23170039841859414483562417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30893386455812552644749889 23170039841859414483562417)
            ·
              refine ⟨17377529881394560862671813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23170039841859414483562417 17377529881394560862671813)
              ·
                refine ⟨3258286852761480161750965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17377529881394560862671813 3258286852761480161750965)
                ·
                  refine ⟨305464392446388765164153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3258286852761480161750965 305464392446388765164153)
                  ·
                    rfl

theorem cell22_2677004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_2677004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677004 prefixEnd_2677004 := by exact prefixLift 2677004
  have htrace : WordTrace (prefixWord ++ tailWord_2677004) baseStart_2677004 baseEnd_2677004 := by
    simpa [prefixWord, tailWord_2677004, baseEnd_2677004] using wordTrace_append hprefix tailTrace_2677004
  have hstable : (prefixWord ++ tailWord_2677004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677004).length < 2 ^ (prefixWord ++ tailWord_2677004).sum := by decide
  have hdescent : baseEnd_2677004 < baseStart_2677004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677079 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2677079 : Nat := 118140960795 + 2677079 * 2 ^ 59
def prefixEnd_2677079 : Nat := 4983230072969 + 3 ^ 40 * 2677079 * 2
def baseEnd_2677079 : Nat := 916418851371891099867229

theorem tailTrace_2677079 : CollatzResearch.WordTrace tailWord_2677079 prefixEnd_2677079 916418851371891099867229 := by
  unfold tailWord_2677079
  simp only [CollatzResearch.WordTrace]
  refine ⟨97641092668407466538066291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65094061778938311025377527 97641092668407466538066291)
  ·
    refine ⟨146461639002611199807099437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97641092668407466538066291 146461639002611199807099437)
    ·
      refine ⟨54923114625979199927662289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146461639002611199807099437 54923114625979199927662289)
      ·
        refine ⟨41192335969484399945746717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54923114625979199927662289 41192335969484399945746717)
        ·
          refine ⟨15447125988556649979655019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41192335969484399945746717 15447125988556649979655019)
          ·
            refine ⟨23170688982834974969482529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15447125988556649979655019 23170688982834974969482529)
            ·
              refine ⟨17378016737126231227111897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23170688982834974969482529 17378016737126231227111897)
              ·
                refine ⟨13033512552844673420333923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17378016737126231227111897 13033512552844673420333923)
                ·
                  refine ⟨19550268829267010130500885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033512552844673420333923 19550268829267010130500885)
                  ·
                    refine ⟨916418851371891099867229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19550268829267010130500885 916418851371891099867229)
                    ·
                      rfl

theorem cell22_2677079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2677079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677079 prefixEnd_2677079 := by exact prefixLift 2677079
  have htrace : WordTrace (prefixWord ++ tailWord_2677079) baseStart_2677079 baseEnd_2677079 := by
    simpa [prefixWord, tailWord_2677079, baseEnd_2677079] using wordTrace_append hprefix tailTrace_2677079
  have hstable : (prefixWord ++ tailWord_2677079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677079).length < 2 ^ (prefixWord ++ tailWord_2677079).sum := by decide
  have hdescent : baseEnd_2677079 < baseStart_2677079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677096 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2677096 : Nat := 118140960795 + 2677096 * 2 ^ 59
def prefixEnd_2677096 : Nat := 4983230072969 + 3 ^ 40 * 2677096 * 2
def baseEnd_2677096 : Nat := 916424670819308722192177

theorem tailTrace_2677096 : CollatzResearch.WordTrace tailWord_2677096 prefixEnd_2677096 916424670819308722192177 := by
  unfold tailWord_2677096
  simp only [CollatzResearch.WordTrace]
  refine ⟨48820856354672939220717571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65094475139563918960956761 48820856354672939220717571)
  ·
    refine ⟨73231284532009408831076357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48820856354672939220717571 73231284532009408831076357)
    ·
      refine ⟨13730865849751764155826817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73231284532009408831076357 13730865849751764155826817)
      ·
        refine ⟨10298149387313823116870113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13730865849751764155826817 10298149387313823116870113)
        ·
          refine ⟨7723612040485367337652585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10298149387313823116870113 7723612040485367337652585)
          ·
            refine ⟨5792709030364025503239439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7723612040485367337652585 5792709030364025503239439)
            ·
              refine ⟨8689063545546038254859159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792709030364025503239439 8689063545546038254859159)
              ·
                refine ⟨13033595318319057382288739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689063545546038254859159 13033595318319057382288739)
                ·
                  refine ⟨19550392977478586073433109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033595318319057382288739 19550392977478586073433109)
                  ·
                    refine ⟨916424670819308722192177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19550392977478586073433109 916424670819308722192177)
                    ·
                      rfl

theorem cell22_2677096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2677096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677096 prefixEnd_2677096 := by exact prefixLift 2677096
  have htrace : WordTrace (prefixWord ++ tailWord_2677096) baseStart_2677096 baseEnd_2677096 := by
    simpa [prefixWord, tailWord_2677096, baseEnd_2677096] using wordTrace_append hprefix tailTrace_2677096
  have hstable : (prefixWord ++ tailWord_2677096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677096).length < 2 ^ (prefixWord ++ tailWord_2677096).sum := by decide
  have hdescent : baseEnd_2677096 < baseStart_2677096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677162 : List Nat := [3, 1, 6, 1, 2, 1, 8]
def baseStart_2677162 : Nat := 118140960795 + 2677162 * 2 ^ 59
def prefixEnd_2677162 : Nat := 4983230072969 + 3 ^ 40 * 2677162 * 2
def baseEnd_2677162 : Nat := 33942491258078020371925

theorem tailTrace_2677162 : CollatzResearch.WordTrace tailWord_2677162 prefixEnd_2677162 33942491258078020371925 := by
  unfold tailWord_2677162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411029981776692928334435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65096079951404514475558493 24411029981776692928334435)
  ·
    refine ⟨36616544972665039392501653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24411029981776692928334435 36616544972665039392501653)
    ·
      refine ⟨1716400545593673721523515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36616544972665039392501653 1716400545593673721523515)
      ·
        refine ⟨2574600818390510582285273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716400545593673721523515 2574600818390510582285273)
        ·
          refine ⟨1930950613792882936713955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574600818390510582285273 1930950613792882936713955)
          ·
            refine ⟨2896425920689324405070933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930950613792882936713955 2896425920689324405070933)
            ·
              refine ⟨33942491258078020371925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2896425920689324405070933 33942491258078020371925)
              ·
                rfl

theorem cell22_2677162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 8].length) (baseStart_2677162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677162 prefixEnd_2677162 := by exact prefixLift 2677162
  have htrace : WordTrace (prefixWord ++ tailWord_2677162) baseStart_2677162 baseEnd_2677162 := by
    simpa [prefixWord, tailWord_2677162, baseEnd_2677162] using wordTrace_append hprefix tailTrace_2677162
  have hstable : (prefixWord ++ tailWord_2677162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677162).length < 2 ^ (prefixWord ++ tailWord_2677162).sum := by decide
  have hdescent : baseEnd_2677162 < baseStart_2677162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677177 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 1, 3]
def baseStart_2677177 : Nat := 118140960795 + 2677177 * 2 ^ 59
def prefixEnd_2677177 : Nat := 4983230072969 + 3 ^ 40 * 2677177 * 2
def baseEnd_2677177 : Nat := 916452398774651510916929

theorem tailTrace_2677177 : CollatzResearch.WordTrace tailWord_2677177 prefixEnd_2677177 916452398774651510916929 := by
  unfold tailWord_2677177
  simp only [CollatzResearch.WordTrace]
  refine ⟨97644667022052429275133785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65096444681368286183422523 97644667022052429275133785)
  ·
    refine ⟨73233500266539321956350339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97644667022052429275133785 73233500266539321956350339)
    ·
      refine ⟨109850250399808982934525509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73233500266539321956350339 109850250399808982934525509)
      ·
        refine ⟨20596921949964184300223533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109850250399808982934525509 20596921949964184300223533)
        ·
          refine ⟨7723845731236569112583825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20596921949964184300223533 7723845731236569112583825)
          ·
            refine ⟨5792884298427426834437869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7723845731236569112583825 5792884298427426834437869)
            ·
              refine ⟨2172331611910285062914201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5792884298427426834437869 2172331611910285062914201)
              ·
                refine ⟨1629248708932713797185651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172331611910285062914201 1629248708932713797185651)
                ·
                  refine ⟨2443873063399070695778477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629248708932713797185651 2443873063399070695778477)
                  ·
                    refine ⟨916452398774651510916929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443873063399070695778477 916452398774651510916929)
                    ·
                      rfl

theorem cell22_2677177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_2677177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677177 prefixEnd_2677177 := by exact prefixLift 2677177
  have htrace : WordTrace (prefixWord ++ tailWord_2677177) baseStart_2677177 baseEnd_2677177 := by
    simpa [prefixWord, tailWord_2677177, baseEnd_2677177] using wordTrace_append hprefix tailTrace_2677177
  have hstable : (prefixWord ++ tailWord_2677177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677177).length < 2 ^ (prefixWord ++ tailWord_2677177).sum := by decide
  have hdescent : baseEnd_2677177 < baseStart_2677177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677216 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_2677216 : Nat := 118140960795 + 2677216 * 2 ^ 59
def prefixEnd_2677216 : Nat := 4983230072969 + 3 ^ 40 * 2677216 * 2
def baseEnd_2677216 : Nat := 916465749271668409191809

theorem tailTrace_2677216 : CollatzResearch.WordTrace tailWord_2677216 prefixEnd_2677216 916465749271668409191809 := by
  unfold tailWord_2677216
  simp only [CollatzResearch.WordTrace]
  refine ⟨48823044734455569467901751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65097392979274092623869001 48823044734455569467901751)
  ·
    refine ⟨73234567101683354201852627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48823044734455569467901751 73234567101683354201852627)
    ·
      refine ⟨109851850652525031302778941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73234567101683354201852627 109851850652525031302778941)
      ·
        refine ⟨41194443994696886738542103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109851850652525031302778941 41194443994696886738542103)
        ·
          refine ⟨61791665992045330107813155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41194443994696886738542103 61791665992045330107813155)
          ·
            refine ⟨92687498988067995161719733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61791665992045330107813155 92687498988067995161719733)
            ·
              refine ⟨8689453030131374546411225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92687498988067995161719733 8689453030131374546411225)
              ·
                refine ⟨6517089772598530909808419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8689453030131374546411225 6517089772598530909808419)
                ·
                  refine ⟨9775634658897796364712629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6517089772598530909808419 9775634658897796364712629)
                  ·
                    refine ⟨916465749271668409191809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9775634658897796364712629 916465749271668409191809)
                    ·
                      rfl

theorem cell22_2677216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_2677216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677216 prefixEnd_2677216 := by exact prefixLift 2677216
  have htrace : WordTrace (prefixWord ++ tailWord_2677216) baseStart_2677216 baseEnd_2677216 := by
    simpa [prefixWord, tailWord_2677216, baseEnd_2677216] using wordTrace_append hprefix tailTrace_2677216
  have hstable : (prefixWord ++ tailWord_2677216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677216).length < 2 ^ (prefixWord ++ tailWord_2677216).sum := by decide
  have hdescent : baseEnd_2677216 < baseStart_2677216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677284 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_2677284 : Nat := 118140960795 + 2677284 * 2 ^ 59
def prefixEnd_2677284 : Nat := 4983230072969 + 3 ^ 40 * 2677284 * 2
def baseEnd_2677284 : Nat := 916489027061338898491601

theorem tailTrace_2677284 : CollatzResearch.WordTrace tailWord_2677284 prefixEnd_2677284 916489027061338898491601 := by
  unfold tailWord_2677284
  simp only [CollatzResearch.WordTrace]
  refine ⟨48824284816332393274639453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65099046421776524366185937 48824284816332393274639453)
  ·
    refine ⟨18309106806124647477989795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48824284816332393274639453 18309106806124647477989795)
    ·
      refine ⟨27463660209186971216984693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18309106806124647477989795 27463660209186971216984693)
      ·
        refine ⟨2574718144611278551592315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27463660209186971216984693 2574718144611278551592315)
        ·
          refine ⟨3862077216916917827388473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574718144611278551592315 3862077216916917827388473)
          ·
            refine ⟨2896557912687688370541355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3862077216916917827388473 2896557912687688370541355)
            ·
              refine ⟨4344836869031532555812033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896557912687688370541355 4344836869031532555812033)
              ·
                refine ⟨3258627651773649416859025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344836869031532555812033 3258627651773649416859025)
                ·
                  refine ⟨2443970738830237062644269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258627651773649416859025 2443970738830237062644269)
                  ·
                    refine ⟨916489027061338898491601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443970738830237062644269 916489027061338898491601)
                    ·
                      rfl

theorem cell22_2677284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_2677284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677284 prefixEnd_2677284 := by exact prefixLift 2677284
  have htrace : WordTrace (prefixWord ++ tailWord_2677284) baseStart_2677284 baseEnd_2677284 := by
    simpa [prefixWord, tailWord_2677284, baseEnd_2677284] using wordTrace_append hprefix tailTrace_2677284
  have hstable : (prefixWord ++ tailWord_2677284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677284).length < 2 ^ (prefixWord ++ tailWord_2677284).sum := by decide
  have hdescent : baseEnd_2677284 < baseStart_2677284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677336 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_2677336 : Nat := 118140960795 + 2677336 * 2 ^ 59
def prefixEnd_2677336 : Nat := 4983230072969 + 3 ^ 40 * 2677336 * 2
def baseEnd_2677336 : Nat := 305502275908009365397147

theorem tailTrace_2677336 : CollatzResearch.WordTrace tailWord_2677336 prefixEnd_2677336 305502275908009365397147 := by
  unfold tailWord_2677336
  simp only [CollatzResearch.WordTrace]
  refine ⟨48825233114238199715085931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65100310818984266286781241 48825233114238199715085931)
  ·
    refine ⟨73237849671357299572628897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48825233114238199715085931 73237849671357299572628897)
    ·
      refine ⟨54928387253517974679471673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73237849671357299572628897 54928387253517974679471673)
      ·
        refine ⟨41196290440138481009603755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54928387253517974679471673 41196290440138481009603755)
        ·
          refine ⟨61794435660207721514405633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41196290440138481009603755 61794435660207721514405633)
          ·
            refine ⟨46345826745155791135804225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61794435660207721514405633 46345826745155791135804225)
            ·
              refine ⟨34759370058866843351853169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46345826745155791135804225 34759370058866843351853169)
              ·
                refine ⟨26069527544150132513889877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34759370058866843351853169 26069527544150132513889877)
                ·
                  refine ⟨305502275908009365397147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26069527544150132513889877 305502275908009365397147)
                  ·
                    rfl

theorem cell22_2677336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_2677336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677336 prefixEnd_2677336 := by exact prefixLift 2677336
  have htrace : WordTrace (prefixWord ++ tailWord_2677336) baseStart_2677336 baseEnd_2677336 := by
    simpa [prefixWord, tailWord_2677336, baseEnd_2677336] using wordTrace_append hprefix tailTrace_2677336
  have hstable : (prefixWord ++ tailWord_2677336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677336).length < 2 ^ (prefixWord ++ tailWord_2677336).sum := by decide
  have hdescent : baseEnd_2677336 < baseStart_2677336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677346 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2677346 : Nat := 118140960795 + 2677346 * 2 ^ 59
def prefixEnd_2677346 : Nat := 4983230072969 + 3 ^ 40 * 2677346 * 2
def baseEnd_2677346 : Nat := 916510250928391403441411

theorem tailTrace_2677346 : CollatzResearch.WordTrace tailWord_2677346 prefixEnd_2677346 916510250928391403441411 := by
  unfold tailWord_2677346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24412707739610042784508973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65100553972293447425357261 24412707739610042784508973)
  ·
    refine ⟨9154765402353766044190865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24412707739610042784508973 9154765402353766044190865)
    ·
      refine ⟨6866074051765324533143149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9154765402353766044190865 6866074051765324533143149)
      ·
        refine ⟨2574777769411996699928681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6866074051765324533143149 2574777769411996699928681)
        ·
          refine ⟨1931083327058997524946511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574777769411996699928681 1931083327058997524946511)
          ·
            refine ⟨2896624990588496287419767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931083327058997524946511 2896624990588496287419767)
            ·
              refine ⟨4344937485882744431129651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896624990588496287419767 4344937485882744431129651)
              ·
                refine ⟨6517406228824116646694477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344937485882744431129651 6517406228824116646694477)
                ·
                  refine ⟨2444027335809043742510429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6517406228824116646694477 2444027335809043742510429)
                  ·
                    refine ⟨916510250928391403441411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444027335809043742510429 916510250928391403441411)
                    ·
                      rfl

theorem cell22_2677346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2677346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677346 prefixEnd_2677346 := by exact prefixLift 2677346
  have htrace : WordTrace (prefixWord ++ tailWord_2677346) baseStart_2677346 baseEnd_2677346 := by
    simpa [prefixWord, tailWord_2677346, baseEnd_2677346] using wordTrace_append hprefix tailTrace_2677346
  have hstable : (prefixWord ++ tailWord_2677346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677346).length < 2 ^ (prefixWord ++ tailWord_2677346).sum := by decide
  have hdescent : baseEnd_2677346 < baseStart_2677346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677404 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 4]
def baseStart_2677404 : Nat := 118140960795 + 2677404 * 2 ^ 59
def prefixEnd_2677404 : Nat := 4983230072969 + 3 ^ 40 * 2677404 * 2
def baseEnd_2677404 : Nat := 305510035171232861830411

theorem tailTrace_2677404 : CollatzResearch.WordTrace tailWord_2677404 prefixEnd_2677404 305510035171232861830411 := by
  unfold tailWord_2677404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48826473196115023521823633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65101964261486698029098177 48826473196115023521823633)
  ·
    refine ⟨36619854897086267641367725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48826473196115023521823633 36619854897086267641367725)
    ·
      refine ⟨13732445586407350365512897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36619854897086267641367725 13732445586407350365512897)
      ·
        refine ⟨10299334189805512774134673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13732445586407350365512897 10299334189805512774134673)
        ·
          refine ⟨7724500642354134580601005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10299334189805512774134673 7724500642354134580601005)
          ·
            refine ⟨2896687740882800467725377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7724500642354134580601005 2896687740882800467725377)
            ·
              refine ⟨2172515805662100350794033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2896687740882800467725377 2172515805662100350794033)
              ·
                refine ⟨1629386854246575263095525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172515805662100350794033 1629386854246575263095525)
                ·
                  refine ⟨305510035171232861830411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1629386854246575263095525 305510035171232861830411)
                  ·
                    rfl

theorem cell22_2677404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_2677404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677404 prefixEnd_2677404 := by exact prefixLift 2677404
  have htrace : WordTrace (prefixWord ++ tailWord_2677404) baseStart_2677404 baseEnd_2677404 := by
    simpa [prefixWord, tailWord_2677404, baseEnd_2677404] using wordTrace_append hprefix tailTrace_2677404
  have hstable : (prefixWord ++ tailWord_2677404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677404).length < 2 ^ (prefixWord ++ tailWord_2677404).sum := by decide
  have hdescent : baseEnd_2677404 < baseStart_2677404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677453 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2677453 : Nat := 118140960795 + 2677453 * 2 ^ 59
def prefixEnd_2677453 : Nat := 4983230072969 + 3 ^ 40 * 2677453 * 2
def baseEnd_2677453 : Nat := 916546879215078791016083

theorem tailTrace_2677453 : CollatzResearch.WordTrace tailWord_2677453 prefixEnd_2677453 916546879215078791016083 := by
  unfold tailWord_2677453
  simp only [CollatzResearch.WordTrace]
  refine ⟨97654733569052528412181013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65103155712701685608120675 97654733569052528412181013)
  ·
    refine ⟨4577565636049337269320985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97654733569052528412181013 4577565636049337269320985)
    ·
      refine ⟨3433174227037002951990739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4577565636049337269320985 3433174227037002951990739)
      ·
        refine ⟨5149761340555504427986109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433174227037002951990739 5149761340555504427986109)
        ·
          refine ⟨1931160502708314160494791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5149761340555504427986109 1931160502708314160494791)
          ·
            refine ⟨2896740754062471240742187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931160502708314160494791 2896740754062471240742187)
            ·
              refine ⟨4345111131093706861113281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896740754062471240742187 4345111131093706861113281)
              ·
                refine ⟨3258833348320280145834961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4345111131093706861113281 3258833348320280145834961)
                ·
                  refine ⟨2444125011240210109376221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258833348320280145834961 2444125011240210109376221)
                  ·
                    refine ⟨916546879215078791016083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444125011240210109376221 916546879215078791016083)
                    ·
                      rfl

theorem cell22_2677453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2677453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677453 prefixEnd_2677453 := by exact prefixLift 2677453
  have htrace : WordTrace (prefixWord ++ tailWord_2677453) baseStart_2677453 baseEnd_2677453 := by
    simpa [prefixWord, tailWord_2677453, baseEnd_2677453] using wordTrace_append hprefix tailTrace_2677453
  have hstable : (prefixWord ++ tailWord_2677453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677453).length < 2 ^ (prefixWord ++ tailWord_2677453).sum := by decide
  have hdescent : baseEnd_2677453 < baseStart_2677453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677475 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 2, 5]
def baseStart_2677475 : Nat := 118140960795 + 2677475 * 2 ^ 59
def prefixEnd_2677475 : Nat := 4983230072969 + 3 ^ 40 * 2677475 * 2
def baseEnd_2677475 : Nat := 916554410264678066966015

theorem tailTrace_2677475 : CollatzResearch.WordTrace tailWord_2677475 prefixEnd_2677475 916554410264678066966015 := by
  unfold tailWord_2677475
  simp only [CollatzResearch.WordTrace]
  refine ⟨97655535974972826169481879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65103690649981884112987919 97655535974972826169481879)
  ·
    refine ⟨146483303962459239254222819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97655535974972826169481879 146483303962459239254222819)
    ·
      refine ⟨219724955943688858881334229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146483303962459239254222819 219724955943688858881334229)
      ·
        refine ⟨5149803654930207630031271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 219724955943688858881334229 5149803654930207630031271)
        ·
          refine ⟨7724705482395311445046907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149803654930207630031271 7724705482395311445046907)
          ·
            refine ⟨11587058223592967167570361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724705482395311445046907 11587058223592967167570361)
            ·
              refine ⟨8690293667694725375677771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11587058223592967167570361 8690293667694725375677771)
              ·
                refine ⟨13035440501542088063516657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8690293667694725375677771 13035440501542088063516657)
                ·
                  refine ⟨9776580376156566047637493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13035440501542088063516657 9776580376156566047637493)
                  ·
                    refine ⟨916554410264678066966015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9776580376156566047637493 916554410264678066966015)
                    ·
                      rfl

theorem cell22_2677475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_2677475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677475 prefixEnd_2677475 := by exact prefixLift 2677475
  have htrace : WordTrace (prefixWord ++ tailWord_2677475) baseStart_2677475 baseEnd_2677475 := by
    simpa [prefixWord, tailWord_2677475, baseEnd_2677475] using wordTrace_append hprefix tailTrace_2677475
  have hstable : (prefixWord ++ tailWord_2677475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677475).length < 2 ^ (prefixWord ++ tailWord_2677475).sum := by decide
  have hdescent : baseEnd_2677475 < baseStart_2677475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677477 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 5]
def baseStart_2677477 : Nat := 118140960795 + 2677477 * 2 ^ 59
def prefixEnd_2677477 : Nat := 4983230072969 + 3 ^ 40 * 2677477 * 2
def baseEnd_2677477 : Nat := 305518364968516909472003

theorem tailTrace_2677477 : CollatzResearch.WordTrace tailWord_2677477 prefixEnd_2677477 305518364968516909472003 := by
  unfold tailWord_2677477
  simp only [CollatzResearch.WordTrace]
  refine ⟨97655608920965580511054685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65103739280643720340703123 97655608920965580511054685)
  ·
    refine ⟨36620853345362092691645507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97655608920965580511054685 36620853345362092691645507)
    ·
      refine ⟨54931280018043139037468261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36620853345362092691645507 54931280018043139037468261)
      ·
        refine ⟨10299615003383088569525299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54931280018043139037468261 10299615003383088569525299)
        ·
          refine ⟨15449422505074632854287949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10299615003383088569525299 15449422505074632854287949)
          ·
            refine ⟨5793533439402987320357981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15449422505074632854287949 5793533439402987320357981)
            ·
              refine ⟨2172575039776120245134243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5793533439402987320357981 2172575039776120245134243)
              ·
                refine ⟨3258862559664180367701365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172575039776120245134243 3258862559664180367701365)
                ·
                  refine ⟨305518364968516909472003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3258862559664180367701365 305518364968516909472003)
                  ·
                    rfl

theorem cell22_2677477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_2677477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677477 prefixEnd_2677477 := by exact prefixLift 2677477
  have htrace : WordTrace (prefixWord ++ tailWord_2677477) baseStart_2677477 baseEnd_2677477 := by
    simpa [prefixWord, tailWord_2677477, baseEnd_2677477] using wordTrace_append hprefix tailTrace_2677477
  have hstable : (prefixWord ++ tailWord_2677477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677477).length < 2 ^ (prefixWord ++ tailWord_2677477).sum := by decide
  have hdescent : baseEnd_2677477 < baseStart_2677477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677488 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_2677488 : Nat := 118140960795 + 2677488 * 2 ^ 59
def prefixEnd_2677488 : Nat := 4983230072969 + 3 ^ 40 * 2677488 * 2
def baseEnd_2677488 : Nat := 305519620143450122130325

theorem tailTrace_2677488 : CollatzResearch.WordTrace tailWord_2677488 prefixEnd_2677488 305519620143450122130325 := by
  unfold tailWord_2677488
  simp only [CollatzResearch.WordTrace]
  refine ⟨48828005061962864694852559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65104006749283819593136745 48828005061962864694852559)
  ·
    refine ⟨73242007592944297042278839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48828005061962864694852559 73242007592944297042278839)
    ·
      refine ⟨109863011389416445563418259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73242007592944297042278839 109863011389416445563418259)
      ·
        refine ⟨164794517084124668345127389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109863011389416445563418259 164794517084124668345127389)
        ·
          refine ⟨61797943906546750629422771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164794517084124668345127389 61797943906546750629422771)
          ·
            refine ⟨92696915859820125944134157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61797943906546750629422771 92696915859820125944134157)
            ·
              refine ⟨34761343447432547229050309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92696915859820125944134157 34761343447432547229050309)
              ·
                refine ⟨6517751896393602605446933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34761343447432547229050309 6517751896393602605446933)
                ·
                  refine ⟨305519620143450122130325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6517751896393602605446933 305519620143450122130325)
                  ·
                    rfl

theorem cell22_2677488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_2677488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677488 prefixEnd_2677488 := by exact prefixLift 2677488
  have htrace : WordTrace (prefixWord ++ tailWord_2677488) baseStart_2677488 baseEnd_2677488 := by
    simpa [prefixWord, tailWord_2677488, baseEnd_2677488] using wordTrace_append hprefix tailTrace_2677488
  have hstable : (prefixWord ++ tailWord_2677488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677488).length < 2 ^ (prefixWord ++ tailWord_2677488).sum := by decide
  have hdescent : baseEnd_2677488 < baseStart_2677488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677503 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_2677503 : Nat := 118140960795 + 2677503 * 2 ^ 59
def prefixEnd_2677503 : Nat := 4983230072969 + 3 ^ 40 * 2677503 * 2
def baseEnd_2677503 : Nat := 916563995236895327265929

theorem tailTrace_2677503 : CollatzResearch.WordTrace tailWord_2677503 prefixEnd_2677503 916563995236895327265929 := by
  unfold tailWord_2677503
  simp only [CollatzResearch.WordTrace]
  refine ⟨97656557218871386951501163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65104371479247591301000775 97656557218871386951501163)
  ·
    refine ⟨146484835828307080427251745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97656557218871386951501163 146484835828307080427251745)
    ·
      refine ⟨109863626871230310320438809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146484835828307080427251745 109863626871230310320438809)
      ·
        refine ⟨82397720153422732740329107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109863626871230310320438809 82397720153422732740329107)
        ·
          refine ⟨123596580230134099110493661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82397720153422732740329107 123596580230134099110493661)
          ·
            refine ⟨46348717586300287166435123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123596580230134099110493661 46348717586300287166435123)
            ·
              refine ⟨69523076379450430749652685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46348717586300287166435123 69523076379450430749652685)
              ·
                refine ⟨26071153642293911531119757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69523076379450430749652685 26071153642293911531119757)
                ·
                  refine ⟨9776682615860216824169909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26071153642293911531119757 9776682615860216824169909)
                  ·
                    refine ⟨916563995236895327265929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9776682615860216824169909 916563995236895327265929)
                    ·
                      rfl

theorem cell22_2677503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_2677503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677503 prefixEnd_2677503 := by exact prefixLift 2677503
  have htrace : WordTrace (prefixWord ++ tailWord_2677503) baseStart_2677503 baseEnd_2677503 := by
    simpa [prefixWord, tailWord_2677503, baseEnd_2677503] using wordTrace_append hprefix tailTrace_2677503
  have hstable : (prefixWord ++ tailWord_2677503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677503).length < 2 ^ (prefixWord ++ tailWord_2677503).sum := by decide
  have hdescent : baseEnd_2677503 < baseStart_2677503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677537 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_2677537 : Nat := 118140960795 + 2677537 * 2 ^ 59
def prefixEnd_2677537 : Nat := 4983230072969 + 3 ^ 40 * 2677537 * 2
def baseEnd_2677537 : Nat := 916575634131730571915825

theorem tailTrace_2677537 : CollatzResearch.WordTrace tailWord_2677537 prefixEnd_2677537 916575634131730571915825 := by
  unfold tailWord_2677537
  simp only [CollatzResearch.WordTrace]
  refine ⟨97657797300748210758238865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65105198200498807172159243 97657797300748210758238865)
  ·
    refine ⟨73243347975561158068679149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97657797300748210758238865 73243347975561158068679149)
    ·
      refine ⟨27466255490835434275754681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73243347975561158068679149 27466255490835434275754681)
      ·
        refine ⟨20599691618126575706816011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27466255490835434275754681 20599691618126575706816011)
        ·
          refine ⟨30899537427189863560224017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20599691618126575706816011 30899537427189863560224017)
          ·
            refine ⟨23174653070392397670168013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30899537427189863560224017 23174653070392397670168013)
            ·
              refine ⟨8690494901397149126313005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23174653070392397670168013 8690494901397149126313005)
              ·
                refine ⟨3258935588023930922367377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8690494901397149126313005 3258935588023930922367377)
                ·
                  refine ⟨2444201691017948191775533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258935588023930922367377 2444201691017948191775533)
                  ·
                    refine ⟨916575634131730571915825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444201691017948191775533 916575634131730571915825)
                    ·
                      rfl

theorem cell22_2677537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_2677537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677537 prefixEnd_2677537 := by exact prefixLift 2677537
  have htrace : WordTrace (prefixWord ++ tailWord_2677537) baseStart_2677537 baseEnd_2677537 := by
    simpa [prefixWord, tailWord_2677537, baseEnd_2677537] using wordTrace_append hprefix tailTrace_2677537
  have hstable : (prefixWord ++ tailWord_2677537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677537).length < 2 ^ (prefixWord ++ tailWord_2677537).sum := by decide
  have hdescent : baseEnd_2677537 < baseStart_2677537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677580 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_2677580 : Nat := 118140960795 + 2677580 * 2 ^ 59
def prefixEnd_2677580 : Nat := 4983230072969 + 3 ^ 40 * 2677580 * 2
def baseEnd_2677580 : Nat := 916590353910492793090693

theorem tailTrace_2677580 : CollatzResearch.WordTrace tailWord_2677580 prefixEnd_2677580 916590353910492793090693 := by
  unfold tailWord_2677580
  simp only [CollatzResearch.WordTrace]
  refine ⟨48829682819796214551027097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65106243759728286068036129 48829682819796214551027097)
  ·
    refine ⟨36622262114847160913270323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48829682819796214551027097 36622262114847160913270323)
    ·
      refine ⟨54933393172270741369905485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36622262114847160913270323 54933393172270741369905485)
      ·
        refine ⟨20600022439601528013714557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54933393172270741369905485 20600022439601528013714557)
        ·
          refine ⟨7725008414850573005142959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20600022439601528013714557 7725008414850573005142959)
          ·
            refine ⟨11587512622275859507714439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7725008414850573005142959 11587512622275859507714439)
            ·
              refine ⟨17381268933413789261571659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11587512622275859507714439 17381268933413789261571659)
              ·
                refine ⟨26071903400120683892357489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17381268933413789261571659 26071903400120683892357489)
                ·
                  refine ⟨19553927550090512919268117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26071903400120683892357489 19553927550090512919268117)
                  ·
                    refine ⟨916590353910492793090693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19553927550090512919268117 916590353910492793090693)
                    ·
                      rfl

theorem cell22_2677580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_2677580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677580 prefixEnd_2677580 := by exact prefixLift 2677580
  have htrace : WordTrace (prefixWord ++ tailWord_2677580) baseStart_2677580 baseEnd_2677580 := by
    simpa [prefixWord, tailWord_2677580, baseEnd_2677580] using wordTrace_append hprefix tailTrace_2677580
  have hstable : (prefixWord ++ tailWord_2677580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677580).length < 2 ^ (prefixWord ++ tailWord_2677580).sum := by decide
  have hdescent : baseEnd_2677580 < baseStart_2677580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677809 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 4]
def baseStart_2677809 : Nat := 118140960795 + 2677809 * 2 ^ 59
def prefixEnd_2677809 : Nat := 4983230072969 + 3 ^ 40 * 2677809 * 2
def baseEnd_2677809 : Nat := 305556248430137509704997

theorem tailTrace_2677809 : CollatzResearch.WordTrace tailWord_2677809 prefixEnd_2677809 305556248430137509704997 := by
  unfold tailWord_2677809
  simp only [CollatzResearch.WordTrace]
  refine ⟨97667717955762801212140481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65111811970508534141426987 97667717955762801212140481)
  ·
    refine ⟨73250788466822100909105361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97667717955762801212140481 73250788466822100909105361)
    ·
      refine ⟨54938091350116575681829021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73250788466822100909105361 54938091350116575681829021)
      ·
        refine ⟨20601784256293715880685883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54938091350116575681829021 20601784256293715880685883)
        ·
          refine ⟨30902676384440573821028825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20601784256293715880685883 30902676384440573821028825)
          ·
            refine ⟨23177007288330430365771619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30902676384440573821028825 23177007288330430365771619)
            ·
              refine ⟨34765510932495645548657429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23177007288330430365771619 34765510932495645548657429)
              ·
                refine ⟨1629633324960733385093317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34765510932495645548657429 1629633324960733385093317)
                ·
                  refine ⟨305556248430137509704997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1629633324960733385093317 305556248430137509704997)
                  ·
                    rfl

theorem cell22_2677809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_2677809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677809 prefixEnd_2677809 := by exact prefixLift 2677809
  have htrace : WordTrace (prefixWord ++ tailWord_2677809) baseStart_2677809 baseEnd_2677809 := by
    simpa [prefixWord, tailWord_2677809, baseEnd_2677809] using wordTrace_append hprefix tailTrace_2677809
  have hstable : (prefixWord ++ tailWord_2677809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677809).length < 2 ^ (prefixWord ++ tailWord_2677809).sum := by decide
  have hdescent : baseEnd_2677809 < baseStart_2677809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677916 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_2677916 : Nat := 118140960795 + 2677916 * 2 ^ 59
def prefixEnd_2677916 : Nat := 4983230072969 + 3 ^ 40 * 2677916 * 2
def baseEnd_2677916 : Nat := 305568457859033305563221

theorem tailTrace_2677916 : CollatzResearch.WordTrace tailWord_2677916 prefixEnd_2677916 305568457859033305563221 := by
  unfold tailWord_2677916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48835810283187579243142801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65114413710916772324190401 48835810283187579243142801)
  ·
    refine ⟨36626857712390684432357101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48835810283187579243142801 36626857712390684432357101)
    ·
      refine ⟨13735071642146506662133913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36626857712390684432357101 13735071642146506662133913)
      ·
        refine ⟨10301303731609879996600435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13735071642146506662133913 10301303731609879996600435)
        ·
          refine ⟨15451955597414819994900653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10301303731609879996600435 15451955597414819994900653)
          ·
            refine ⟨5794483349030557498087745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15451955597414819994900653 5794483349030557498087745)
            ·
              refine ⟨4345862511772918123565809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5794483349030557498087745 4345862511772918123565809)
              ·
                refine ⟨3259396883829688592674357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4345862511772918123565809 3259396883829688592674357)
                ·
                  refine ⟨305568457859033305563221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259396883829688592674357 305568457859033305563221)
                  ·
                    rfl

theorem cell22_2677916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_2677916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677916 prefixEnd_2677916 := by exact prefixLift 2677916
  have htrace : WordTrace (prefixWord ++ tailWord_2677916) baseStart_2677916 baseEnd_2677916 := by
    simpa [prefixWord, tailWord_2677916, baseEnd_2677916] using wordTrace_append hprefix tailTrace_2677916
  have hstable : (prefixWord ++ tailWord_2677916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677916).length < 2 ^ (prefixWord ++ tailWord_2677916).sum := by decide
  have hdescent : baseEnd_2677916 < baseStart_2677916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2677954 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2677954 : Nat := 118140960795 + 2677954 * 2 ^ 59
def prefixEnd_2677954 : Nat := 4983230072969 + 3 ^ 40 * 2677954 * 2
def baseEnd_2677954 : Nat := 916718381753680484239547

theorem tailTrace_2677954 : CollatzResearch.WordTrace tailWord_2677954 prefixEnd_2677954 916718381753680484239547 := by
  unfold tailWord_2677954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24418251635059372744042229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65115337693491660650779277 24418251635059372744042229)
  ·
    refine ⟨2289211090786816194753959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24418251635059372744042229 2289211090786816194753959)
    ·
      refine ⟨3433816636180224292130939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289211090786816194753959 3433816636180224292130939)
      ·
        refine ⟨5150724954270336438196409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433816636180224292130939 5150724954270336438196409)
        ·
          refine ⟨3863043715702752328647307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5150724954270336438196409 3863043715702752328647307)
          ·
            refine ⟨5794565573554128492970961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863043715702752328647307 5794565573554128492970961)
            ·
              refine ⟨4345924180165596369728221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5794565573554128492970961 4345924180165596369728221)
              ·
                refine ⟨1629721567562098638648083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4345924180165596369728221 1629721567562098638648083)
                ·
                  refine ⟨2444582351343147957972125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629721567562098638648083 2444582351343147957972125)
                  ·
                    refine ⟨916718381753680484239547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444582351343147957972125 916718381753680484239547)
                    ·
                      rfl

theorem cell22_2677954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2677954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2677954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2677954 prefixEnd_2677954 := by exact prefixLift 2677954
  have htrace : WordTrace (prefixWord ++ tailWord_2677954) baseStart_2677954 baseEnd_2677954 := by
    simpa [prefixWord, tailWord_2677954, baseEnd_2677954] using wordTrace_append hprefix tailTrace_2677954
  have hstable : (prefixWord ++ tailWord_2677954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2677954).length < 2 ^ (prefixWord ++ tailWord_2677954).sum := by decide
  have hdescent : baseEnd_2677954 < baseStart_2677954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2677954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678049 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2678049 : Nat := 118140960795 + 2678049 * 2 ^ 59
def prefixEnd_2678049 : Nat := 4983230072969 + 3 ^ 40 * 2678049 * 2
def baseEnd_2678049 : Nat := 916750902195131903114255

theorem tailTrace_2678049 : CollatzResearch.WordTrace tailWord_2678049 prefixEnd_2678049 916750902195131903114255 := by
  unfold tailWord_2678049
  simp only [CollatzResearch.WordTrace]
  refine ⟨97676471474893322200877201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65117647649928881467251467 97676471474893322200877201)
  ·
    refine ⟨73257353606169991650657901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97676471474893322200877201 73257353606169991650657901)
    ·
      refine ⟨27471507602313746868996713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73257353606169991650657901 27471507602313746868996713)
      ·
        refine ⟨20603630701735310151747535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27471507602313746868996713 20603630701735310151747535)
        ·
          refine ⟨30905446052602965227621303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20603630701735310151747535 30905446052602965227621303)
          ·
            refine ⟨46358169078904447841431955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30905446052602965227621303 46358169078904447841431955)
            ·
              refine ⟨69537253618356671762147933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46358169078904447841431955 69537253618356671762147933)
              ·
                refine ⟨26076470106883751910805475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69537253618356671762147933 26076470106883751910805475)
                ·
                  refine ⟨39114705160325627866208213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26076470106883751910805475 39114705160325627866208213)
                  ·
                    refine ⟨916750902195131903114255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39114705160325627866208213 916750902195131903114255)
                    ·
                      rfl

theorem cell22_2678049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2678049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678049 prefixEnd_2678049 := by exact prefixLift 2678049
  have htrace : WordTrace (prefixWord ++ tailWord_2678049) baseStart_2678049 baseEnd_2678049 := by
    simpa [prefixWord, tailWord_2678049, baseEnd_2678049] using wordTrace_append hprefix tailTrace_2678049
  have hstable : (prefixWord ++ tailWord_2678049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678049).length < 2 ^ (prefixWord ++ tailWord_2678049).sum := by decide
  have hdescent : baseEnd_2678049 < baseStart_2678049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678051 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 5]
def baseStart_2678051 : Nat := 118140960795 + 2678051 * 2 ^ 59
def prefixEnd_2678051 : Nat := 4983230072969 + 3 ^ 40 * 2678051 * 2
def baseEnd_2678051 : Nat := 305583862278668188188083

theorem tailTrace_2678051 : CollatzResearch.WordTrace tailWord_2678051 prefixEnd_2678051 305583862278668188188083 := by
  unfold tailWord_2678051
  simp only [CollatzResearch.WordTrace]
  refine ⟨97676544420886076542450007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65117696280590717694966671 97676544420886076542450007)
  ·
    refine ⟨146514816631329114813675011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97676544420886076542450007 146514816631329114813675011)
    ·
      refine ⟨219772224946993672220512517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146514816631329114813675011 219772224946993672220512517)
      ·
        refine ⟨41207292177561313541346097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219772224946993672220512517 41207292177561313541346097)
        ·
          refine ⟨30905469133170985156009573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41207292177561313541346097 30905469133170985156009573)
          ·
            refine ⟨5794775462469559716751795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30905469133170985156009573 5794775462469559716751795)
            ·
              refine ⟨8692163193704339575127693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794775462469559716751795 8692163193704339575127693)
              ·
                refine ⟨3259561197639127340672885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8692163193704339575127693 3259561197639127340672885)
                ·
                  refine ⟨305583862278668188188083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259561197639127340672885 305583862278668188188083)
                  ·
                    rfl

theorem cell22_2678051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 5].length) (baseStart_2678051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678051 prefixEnd_2678051 := by exact prefixLift 2678051
  have htrace : WordTrace (prefixWord ++ tailWord_2678051) baseStart_2678051 baseEnd_2678051 := by
    simpa [prefixWord, tailWord_2678051, baseEnd_2678051] using wordTrace_append hprefix tailTrace_2678051
  have hstable : (prefixWord ++ tailWord_2678051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678051).length < 2 ^ (prefixWord ++ tailWord_2678051).sum := by decide
  have hdescent : baseEnd_2678051 < baseStart_2678051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678111 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 6, 3]
def baseStart_2678111 : Nat := 118140960795 + 2678111 * 2 ^ 59
def prefixEnd_2678111 : Nat := 4983230072969 + 3 ^ 40 * 2678111 * 2
def baseEnd_2678111 : Nat := 916772126062184408064065

theorem tailTrace_2678111 : CollatzResearch.WordTrace tailWord_2678111 prefixEnd_2678111 916772126062184408064065 := by
  unfold tailWord_2678111
  simp only [CollatzResearch.WordTrace]
  refine ⟨97678732800668706789634187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65119155200445804526422791 97678732800668706789634187)
  ·
    refine ⟨146518099201003060184451281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97678732800668706789634187 146518099201003060184451281)
    ·
      refine ⟨109888574400752295138338461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146518099201003060184451281 109888574400752295138338461)
      ·
        refine ⟨41208215400282110676876923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109888574400752295138338461 41208215400282110676876923)
        ·
          refine ⟨61812323100423166015315385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41208215400282110676876923 61812323100423166015315385)
          ·
            refine ⟨46359242325317374511486539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61812323100423166015315385 46359242325317374511486539)
            ·
              refine ⟨69538863487976061767229809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46359242325317374511486539 69538863487976061767229809)
              ·
                refine ⟨52154147615982046325422357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69538863487976061767229809 52154147615982046325422357)
                ·
                  refine ⟨2444725669499158421504173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52154147615982046325422357 2444725669499158421504173)
                  ·
                    refine ⟨916772126062184408064065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444725669499158421504173 916772126062184408064065)
                    ·
                      rfl

theorem cell22_2678111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_2678111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678111 prefixEnd_2678111 := by exact prefixLift 2678111
  have htrace : WordTrace (prefixWord ++ tailWord_2678111) baseStart_2678111 baseEnd_2678111 := by
    simpa [prefixWord, tailWord_2678111, baseEnd_2678111] using wordTrace_append hprefix tailTrace_2678111
  have hstable : (prefixWord ++ tailWord_2678111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678111).length < 2 ^ (prefixWord ++ tailWord_2678111).sum := by decide
  have hdescent : baseEnd_2678111 < baseStart_2678111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678145 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2678145 : Nat := 118140960795 + 2678145 * 2 ^ 59
def prefixEnd_2678145 : Nat := 4983230072969 + 3 ^ 40 * 2678145 * 2
def baseEnd_2678145 : Nat := 916783764957019652713961

theorem tailTrace_2678145 : CollatzResearch.WordTrace tailWord_2678145 prefixEnd_2678145 916783764957019652713961 := by
  unfold tailWord_2678145
  simp only [CollatzResearch.WordTrace]
  refine ⟨97679972882545530596371889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65119981921697020397581259 97679972882545530596371889)
  ·
    refine ⟨73259979661909147947278917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97679972882545530596371889 73259979661909147947278917)
    ·
      refine ⟨13736246186607965240114797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73259979661909147947278917 13736246186607965240114797)
      ·
        refine ⟨5151092319977986965043049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13736246186607965240114797 5151092319977986965043049)
        ·
          refine ⟨3863319239983490223782287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5151092319977986965043049 3863319239983490223782287)
          ·
            refine ⟨5794978859975235335673431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863319239983490223782287 5794978859975235335673431)
            ·
              refine ⟨8692468289962853003510147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794978859975235335673431 8692468289962853003510147)
              ·
                refine ⟨13038702434944279505265221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8692468289962853003510147 13038702434944279505265221)
                ·
                  refine ⟨2444756706552052407237229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13038702434944279505265221 2444756706552052407237229)
                  ·
                    refine ⟨916783764957019652713961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444756706552052407237229 916783764957019652713961)
                    ·
                      rfl

theorem cell22_2678145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2678145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678145 prefixEnd_2678145 := by exact prefixLift 2678145
  have htrace : WordTrace (prefixWord ++ tailWord_2678145) baseStart_2678145 baseEnd_2678145 := by
    simpa [prefixWord, tailWord_2678145, baseEnd_2678145] using wordTrace_append hprefix tailTrace_2678145
  have hstable : (prefixWord ++ tailWord_2678145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678145).length < 2 ^ (prefixWord ++ tailWord_2678145).sum := by decide
  have hdescent : baseEnd_2678145 < baseStart_2678145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678162 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2678162 : Nat := 118140960795 + 2678162 * 2 ^ 59
def prefixEnd_2678162 : Nat := 4983230072969 + 3 ^ 40 * 2678162 * 2
def baseEnd_2678162 : Nat := 916789584404437275038909

theorem tailTrace_2678162 : CollatzResearch.WordTrace tailWord_2678162 prefixEnd_2678162 916789584404437275038909 := by
  unfold tailWord_2678162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420148230870985624935185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65120395282322628333160493 24420148230870985624935185)
  ·
    refine ⟨18315111173153239218701389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24420148230870985624935185 18315111173153239218701389)
    ·
      refine ⟨6868166689932464707013021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18315111173153239218701389 6868166689932464707013021)
      ·
        refine ⟨2575562508724674265129883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6868166689932464707013021 2575562508724674265129883)
        ·
          refine ⟨3863343763087011397694825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575562508724674265129883 3863343763087011397694825)
          ·
            refine ⟨2897507822315258548271119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3863343763087011397694825 2897507822315258548271119)
            ·
              refine ⟨4346261733472887822406679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897507822315258548271119 4346261733472887822406679)
              ·
                refine ⟨6519392600209331733610019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346261733472887822406679 6519392600209331733610019)
                ·
                  refine ⟨9779088900313997600415029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519392600209331733610019 9779088900313997600415029)
                  ·
                    refine ⟨916789584404437275038909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9779088900313997600415029 916789584404437275038909)
                    ·
                      rfl

theorem cell22_2678162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2678162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678162 prefixEnd_2678162 := by exact prefixLift 2678162
  have htrace : WordTrace (prefixWord ++ tailWord_2678162) baseStart_2678162 baseEnd_2678162 := by
    simpa [prefixWord, tailWord_2678162, baseEnd_2678162] using wordTrace_append hprefix tailTrace_2678162
  have hstable : (prefixWord ++ tailWord_2678162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678162).length < 2 ^ (prefixWord ++ tailWord_2678162).sum := by decide
  have hdescent : baseEnd_2678162 < baseStart_2678162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678220 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 5]
def baseStart_2678220 : Nat := 118140960795 + 2678220 * 2 ^ 59
def prefixEnd_2678220 : Nat := 4983230072969 + 3 ^ 40 * 2678220 * 2
def baseEnd_2678220 : Nat := 305603146329914819029577

theorem tailTrace_2678220 : CollatzResearch.WordTrace tailWord_2678220 prefixEnd_2678220 305603146329914819029577 := by
  unfold tailWord_2678220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48841354178636909202676057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65121805571515878936901409 48841354178636909202676057)
  ·
    refine ⟨36631015633977681902007043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48841354178636909202676057 36631015633977681902007043)
    ·
      refine ⟨54946523450966522853010565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36631015633977681902007043 54946523450966522853010565)
      ·
        refine ⟨10302473147056223034939481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54946523450966522853010565 10302473147056223034939481)
        ·
          refine ⟨7726854860292167276204611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10302473147056223034939481 7726854860292167276204611)
          ·
            refine ⟨11590282290438250914306917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726854860292167276204611 11590282290438250914306917)
            ·
              refine ⟨2173177929457172046432547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11590282290438250914306917 2173177929457172046432547)
              ·
                refine ⟨3259766894185758069648821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173177929457172046432547 3259766894185758069648821)
                ·
                  refine ⟨305603146329914819029577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259766894185758069648821 305603146329914819029577)
                  ·
                    rfl

theorem cell22_2678220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_2678220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678220 prefixEnd_2678220 := by exact prefixLift 2678220
  have htrace : WordTrace (prefixWord ++ tailWord_2678220) baseStart_2678220 baseEnd_2678220 := by
    simpa [prefixWord, tailWord_2678220, baseEnd_2678220] using wordTrace_append hprefix tailTrace_2678220
  have hstable : (prefixWord ++ tailWord_2678220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678220).length < 2 ^ (prefixWord ++ tailWord_2678220).sum := by decide
  have hdescent : baseEnd_2678220 < baseStart_2678220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678231 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 6]
def baseStart_2678231 : Nat := 118140960795 + 2678231 * 2 ^ 59
def prefixEnd_2678231 : Nat := 4983230072969 + 3 ^ 40 * 2678231 * 2
def baseEnd_2678231 : Nat := 305604401504848031687899

theorem tailTrace_2678231 : CollatzResearch.WordTrace tailWord_2678231 prefixEnd_2678231 305604401504848031687899 := by
  unfold tailWord_2678231
  simp only [CollatzResearch.WordTrace]
  refine ⟨97683109560233967284002547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65122073040155978189335031 97683109560233967284002547)
  ·
    refine ⟨146524664340350950926003821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97683109560233967284002547 146524664340350950926003821)
    ·
      refine ⟨54946749127631606597251433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146524664340350950926003821 54946749127631606597251433)
      ·
        refine ⟨41210061845723704947938575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54946749127631606597251433 41210061845723704947938575)
        ·
          refine ⟨61815092768585557421907863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41210061845723704947938575 61815092768585557421907863)
          ·
            refine ⟨92722639152878336132861795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61815092768585557421907863 92722639152878336132861795)
            ·
              refine ⟨139083958729317504199292693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92722639152878336132861795 139083958729317504199292693)
              ·
                refine ⟨6519560565436758009341845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139083958729317504199292693 6519560565436758009341845)
                ·
                  refine ⟨305604401504848031687899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6519560565436758009341845 305604401504848031687899)
                  ·
                    rfl

theorem cell22_2678231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 6].length) (baseStart_2678231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678231 prefixEnd_2678231 := by exact prefixLift 2678231
  have htrace : WordTrace (prefixWord ++ tailWord_2678231) baseStart_2678231 baseEnd_2678231 := by
    simpa [prefixWord, tailWord_2678231, baseEnd_2678231] using wordTrace_append hprefix tailTrace_2678231
  have hstable : (prefixWord ++ tailWord_2678231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678231).length < 2 ^ (prefixWord ++ tailWord_2678231).sum := by decide
  have hdescent : baseEnd_2678231 < baseStart_2678231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678233 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_2678233 : Nat := 118140960795 + 2678233 * 2 ^ 59
def prefixEnd_2678233 : Nat := 4983230072969 + 3 ^ 40 * 2678233 * 2
def baseEnd_2678233 : Nat := 916813889155416756513691

theorem tailTrace_2678233 : CollatzResearch.WordTrace tailWord_2678233 prefixEnd_2678233 916813889155416756513691 := by
  unfold tailWord_2678233
  simp only [CollatzResearch.WordTrace]
  refine ⟨97683182506226721625575353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65122121670817814417050235 97683182506226721625575353)
  ·
    refine ⟨73262386879670041219181515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97683182506226721625575353 73262386879670041219181515)
    ·
      refine ⟨109893580319505061828772273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73262386879670041219181515 109893580319505061828772273)
      ·
        refine ⟨82420185239628796371579205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109893580319505061828772273 82420185239628796371579205)
        ·
          refine ⟨15453784732430399319671101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82420185239628796371579205 15453784732430399319671101)
          ·
            refine ⟨5795169274661399744876663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15453784732430399319671101 5795169274661399744876663)
            ·
              refine ⟨8692753911992099617314995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795169274661399744876663 8692753911992099617314995)
              ·
                refine ⟨13039130867988149425972493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8692753911992099617314995 13039130867988149425972493)
                ·
                  refine ⟨4889674075495556034739685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13039130867988149425972493 4889674075495556034739685)
                  ·
                    refine ⟨916813889155416756513691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889674075495556034739685 916813889155416756513691)
                    ·
                      rfl

theorem cell22_2678233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_2678233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678233 prefixEnd_2678233 := by exact prefixLift 2678233
  have htrace : WordTrace (prefixWord ++ tailWord_2678233) baseStart_2678233 baseEnd_2678233 := by
    simpa [prefixWord, tailWord_2678233, baseEnd_2678233] using wordTrace_append hprefix tailTrace_2678233
  have hstable : (prefixWord ++ tailWord_2678233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678233).length < 2 ^ (prefixWord ++ tailWord_2678233).sum := by decide
  have hdescent : baseEnd_2678233 < baseStart_2678233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678280 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_2678280 : Nat := 118140960795 + 2678280 * 2 ^ 59
def prefixEnd_2678280 : Nat := 4983230072969 + 3 ^ 40 * 2678280 * 2
def baseEnd_2678280 : Nat := 916829978215924300588547

theorem tailTrace_2678280 : CollatzResearch.WordTrace tailWord_2678280 prefixEnd_2678280 916829978215924300588547 := by
  unfold tailWord_2678280
  simp only [CollatzResearch.WordTrace]
  refine ⟨48842448368528224326268147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65123264491370965768357529 48842448368528224326268147)
  ·
    refine ⟨73263672552792336489402221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48842448368528224326268147 73263672552792336489402221)
    ·
      refine ⟨27473877207297126183525833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73263672552792336489402221 27473877207297126183525833)
      ·
        refine ⟨20605407905472844637644375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27473877207297126183525833 20605407905472844637644375)
        ·
          refine ⟨30908111858209266956466563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20605407905472844637644375 30908111858209266956466563)
          ·
            refine ⟨46362167787313900434699845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30908111858209266956466563 46362167787313900434699845)
            ·
              refine ⟨8692906460121356331506221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46362167787313900434699845 8692906460121356331506221)
              ·
                refine ⟨3259839922545508624314833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8692906460121356331506221 3259839922545508624314833)
                ·
                  refine ⟨2444879941909131468236125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3259839922545508624314833 2444879941909131468236125)
                  ·
                    refine ⟨916829978215924300588547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444879941909131468236125 916829978215924300588547)
                    ·
                      rfl

theorem cell22_2678280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_2678280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678280 prefixEnd_2678280 := by exact prefixLift 2678280
  have htrace : WordTrace (prefixWord ++ tailWord_2678280) baseStart_2678280 baseEnd_2678280 := by
    simpa [prefixWord, tailWord_2678280, baseEnd_2678280] using wordTrace_append hprefix tailTrace_2678280
  have hstable : (prefixWord ++ tailWord_2678280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678280).length < 2 ^ (prefixWord ++ tailWord_2678280).sum := by decide
  have hdescent : baseEnd_2678280 < baseStart_2678280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678325 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2678325 : Nat := 118140960795 + 2678325 * 2 ^ 59
def prefixEnd_2678325 : Nat := 4983230072969 + 3 ^ 40 * 2678325 * 2
def baseEnd_2678325 : Nat := 916845382635559183213409

theorem tailTrace_2678325 : CollatzResearch.WordTrace tailWord_2678325 prefixEnd_2678325 916845382635559183213409 := by
  unfold tailWord_2678325
  simp only [CollatzResearch.WordTrace]
  refine ⟨97686538021893421337924429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65124358681262280891949619 97686538021893421337924429)
  ·
    refine ⟨36632451758210033001721661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97686538021893421337924429 36632451758210033001721661)
    ·
      refine ⟨13737169409328762375645623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36632451758210033001721661 13737169409328762375645623)
      ·
        refine ⟨20605754113993143563468435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13737169409328762375645623 20605754113993143563468435)
        ·
          refine ⟨30908631170989715345202653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20605754113993143563468435 30908631170989715345202653)
          ·
            refine ⟨11590736689121143254450995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30908631170989715345202653 11590736689121143254450995)
            ·
              refine ⟨17386105033681714881676493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11590736689121143254450995 17386105033681714881676493)
              ·
                refine ⟨6519789387630643080628685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17386105033681714881676493 6519789387630643080628685)
                ·
                  refine ⟨2444921020361491155235757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6519789387630643080628685 2444921020361491155235757)
                  ·
                    refine ⟨916845382635559183213409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444921020361491155235757 916845382635559183213409)
                    ·
                      rfl

theorem cell22_2678325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2678325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678325 prefixEnd_2678325 := by exact prefixLift 2678325
  have htrace : WordTrace (prefixWord ++ tailWord_2678325) baseStart_2678325 baseEnd_2678325 := by
    simpa [prefixWord, tailWord_2678325, baseEnd_2678325] using wordTrace_append hprefix tailTrace_2678325
  have hstable : (prefixWord ++ tailWord_2678325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678325).length < 2 ^ (prefixWord ++ tailWord_2678325).sum := by decide
  have hdescent : baseEnd_2678325 < baseStart_2678325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678359 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 1, 3]
def baseStart_2678359 : Nat := 118140960795 + 2678359 * 2 ^ 59
def prefixEnd_2678359 : Nat := 4983230072969 + 3 ^ 40 * 2678359 * 2
def baseEnd_2678359 : Nat := 916857021530394427863305

theorem tailTrace_2678359 : CollatzResearch.WordTrace tailWord_2678359 prefixEnd_2678359 916857021530394427863305 := by
  unfold tailWord_2678359
  simp only [CollatzResearch.WordTrace]
  refine ⟨97687778103770245144662131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65125185402513496763108087 97687778103770245144662131)
  ·
    refine ⟨146531667155655367716993197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97687778103770245144662131 146531667155655367716993197)
    ·
      refine ⟨54949375183370762893872449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146531667155655367716993197 54949375183370762893872449)
      ·
        refine ⟨41212031387528072170404337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54949375183370762893872449 41212031387528072170404337)
        ·
          refine ⟨30909023540646054127803253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41212031387528072170404337 30909023540646054127803253)
          ·
            refine ⟨2897720956935567574481555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30909023540646054127803253 2897720956935567574481555)
            ·
              refine ⟨4346581435403351361722333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897720956935567574481555 4346581435403351361722333)
              ·
                refine ⟨1629968038276256760645875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4346581435403351361722333 1629968038276256760645875)
                ·
                  refine ⟨2444952057414385140968813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629968038276256760645875 2444952057414385140968813)
                  ·
                    refine ⟨916857021530394427863305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444952057414385140968813 916857021530394427863305)
                    ·
                      rfl

theorem cell22_2678359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_2678359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678359 prefixEnd_2678359 := by exact prefixLift 2678359
  have htrace : WordTrace (prefixWord ++ tailWord_2678359) baseStart_2678359 baseEnd_2678359 := by
    simpa [prefixWord, tailWord_2678359, baseEnd_2678359] using wordTrace_append hprefix tailTrace_2678359
  have hstable : (prefixWord ++ tailWord_2678359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678359).length < 2 ^ (prefixWord ++ tailWord_2678359).sum := by decide
  have hdescent : baseEnd_2678359 < baseStart_2678359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678368 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_2678368 : Nat := 118140960795 + 2678368 * 2 ^ 59
def prefixEnd_2678368 : Nat := 4983230072969 + 3 ^ 40 * 2678368 * 2
def baseEnd_2678368 : Nat := 916860102414321404388277

theorem tailTrace_2678368 : CollatzResearch.WordTrace tailWord_2678368 prefixEnd_2678368 916860102414321404388277 := by
  unfold tailWord_2678368
  simp only [CollatzResearch.WordTrace]
  refine ⟨48844053180368819840869879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65125404240491759787826505 48844053180368819840869879)
  ·
    refine ⟨73266079770553229761304819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48844053180368819840869879 73266079770553229761304819)
    ·
      refine ⟨109899119655829844641957229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73266079770553229761304819 109899119655829844641957229)
      ·
        refine ⟨41212169870936191740733961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109899119655829844641957229 41212169870936191740733961)
        ·
          refine ⟨30909127403202143805550471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41212169870936191740733961 30909127403202143805550471)
          ·
            refine ⟨46363691104803215708325707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30909127403202143805550471 46363691104803215708325707)
            ·
              refine ⟨69545536657204823562488561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46363691104803215708325707 69545536657204823562488561)
              ·
                refine ⟨52159152492903617671866421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69545536657204823562488561 52159152492903617671866421)
                ·
                  refine ⟨4889920546209714156737477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52159152492903617671866421 4889920546209714156737477)
                  ·
                    refine ⟨916860102414321404388277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889920546209714156737477 916860102414321404388277)
                    ·
                      rfl

theorem cell22_2678368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_2678368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678368 prefixEnd_2678368 := by exact prefixLift 2678368
  have htrace : WordTrace (prefixWord ++ tailWord_2678368) baseStart_2678368 baseEnd_2678368 := by
    simpa [prefixWord, tailWord_2678368, baseEnd_2678368] using wordTrace_append hprefix tailTrace_2678368
  have hstable : (prefixWord ++ tailWord_2678368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678368).length < 2 ^ (prefixWord ++ tailWord_2678368).sum := by decide
  have hdescent : baseEnd_2678368 < baseStart_2678368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678376 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 1, 3]
def baseStart_2678376 : Nat := 118140960795 + 2678376 * 2 ^ 59
def prefixEnd_2678376 : Nat := 4983230072969 + 3 ^ 40 * 2678376 * 2
def baseEnd_2678376 : Nat := 916862840977812050188253

theorem tailTrace_2678376 : CollatzResearch.WordTrace tailWord_2678376 prefixEnd_2678376 916862840977812050188253 := by
  unfold tailWord_2678376
  simp only [CollatzResearch.WordTrace]
  refine ⟨48844199072354328524015491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65125598763139104698687321 48844199072354328524015491)
  ·
    refine ⟨73266298608531492786023237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48844199072354328524015491 73266298608531492786023237)
    ·
      refine ⟨13737430989099654897379357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73266298608531492786023237 13737430989099654897379357)
      ·
        refine ⟨5151536620912370586517259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13737430989099654897379357 5151536620912370586517259)
        ·
          refine ⟨7727304931368555879775889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151536620912370586517259 7727304931368555879775889)
          ·
            refine ⟨5795478698526416909831917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7727304931368555879775889 5795478698526416909831917)
            ·
              refine ⟨2173304511947406341186969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5795478698526416909831917 2173304511947406341186969)
              ·
                refine ⟨1629978383960554755890227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173304511947406341186969 1629978383960554755890227)
                ·
                  refine ⟨2444967575940832133835341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629978383960554755890227 2444967575940832133835341)
                  ·
                    refine ⟨916862840977812050188253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444967575940832133835341 916862840977812050188253)
                    ·
                      rfl

theorem cell22_2678376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_2678376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678376 prefixEnd_2678376 := by exact prefixLift 2678376
  have htrace : WordTrace (prefixWord ++ tailWord_2678376) baseStart_2678376 baseEnd_2678376 := by
    simpa [prefixWord, tailWord_2678376, baseEnd_2678376] using wordTrace_append hprefix tailTrace_2678376
  have hstable : (prefixWord ++ tailWord_2678376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678376).length < 2 ^ (prefixWord ++ tailWord_2678376).sum := by decide
  have hdescent : baseEnd_2678376 < baseStart_2678376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678389 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 5]
def baseStart_2678389 : Nat := 118140960795 + 2678389 * 2 ^ 59
def prefixEnd_2678389 : Nat := 4983230072969 + 3 ^ 40 * 2678389 * 2
def baseEnd_2678389 : Nat := 305622430381161449871071

theorem tailTrace_2678389 : CollatzResearch.WordTrace tailWord_2678389 prefixEnd_2678389 305622430381161449871071 := by
  unfold tailWord_2678389
  simp only [CollatzResearch.WordTrace]
  refine ⟨97688872293661560268254221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65125914862441040178836147 97688872293661560268254221)
  ·
    refine ⟨36633327110123085100595333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97688872293661560268254221 36633327110123085100595333)
    ·
      refine ⟨6868748833148078456361625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36633327110123085100595333 6868748833148078456361625)
      ·
        refine ⟨5151561624861058842271219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6868748833148078456361625 5151561624861058842271219)
        ·
          refine ⟨7727342437291588263406829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151561624861058842271219 7727342437291588263406829)
          ·
            refine ⟨2897753413984345598777561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7727342437291588263406829 2897753413984345598777561)
            ·
              refine ⟨2173315060488259199083171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897753413984345598777561 2173315060488259199083171)
              ·
                refine ⟨3259972590732388798624757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173315060488259199083171 3259972590732388798624757)
                ·
                  refine ⟨305622430381161449871071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259972590732388798624757 305622430381161449871071)
                  ·
                    rfl

theorem cell22_2678389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_2678389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678389 prefixEnd_2678389 := by exact prefixLift 2678389
  have htrace : WordTrace (prefixWord ++ tailWord_2678389) baseStart_2678389 baseEnd_2678389 := by
    simpa [prefixWord, tailWord_2678389, baseEnd_2678389] using wordTrace_append hprefix tailTrace_2678389
  have hstable : (prefixWord ++ tailWord_2678389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678389).length < 2 ^ (prefixWord ++ tailWord_2678389).sum := by decide
  have hdescent : baseEnd_2678389 < baseStart_2678389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678428 : List Nat := [2, 2, 3, 2, 13]
def baseStart_2678428 : Nat := 118140960795 + 2678428 * 2 ^ 59
def prefixEnd_2678428 : Nat := 4983230072969 + 3 ^ 40 * 2678428 * 2
def baseEnd_2678428 : Nat := 3773171364775725299951

theorem tailTrace_2678428 : CollatzResearch.WordTrace tailWord_2678428 prefixEnd_2678428 3773171364775725299951 := by
  unfold tailWord_2678428
  simp only [CollatzResearch.WordTrace]
  refine ⟨48845147370260134964461969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65126863160346846619282625 48845147370260134964461969)
  ·
    refine ⟨36633860527695101223346477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48845147370260134964461969 36633860527695101223346477)
    ·
      refine ⟨13737697697885662958754929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36633860527695101223346477 13737697697885662958754929)
      ·
        refine ⟨10303273273414247219066197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13737697697885662958754929 10303273273414247219066197)
        ·
          refine ⟨3773171364775725299951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10303273273414247219066197 3773171364775725299951)
          ·
            rfl

theorem cell22_2678428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 13].length) (baseStart_2678428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678428 prefixEnd_2678428 := by exact prefixLift 2678428
  have htrace : WordTrace (prefixWord ++ tailWord_2678428) baseStart_2678428 baseEnd_2678428 := by
    simpa [prefixWord, tailWord_2678428, baseEnd_2678428] using wordTrace_append hprefix tailTrace_2678428
  have hstable : (prefixWord ++ tailWord_2678428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678428).length < 2 ^ (prefixWord ++ tailWord_2678428).sum := by decide
  have hdescent : baseEnd_2678428 < baseStart_2678428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678432 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_2678432 : Nat := 118140960795 + 2678432 * 2 ^ 59
def prefixEnd_2678432 : Nat := 4983230072969 + 3 ^ 40 * 2678432 * 2
def baseEnd_2678432 : Nat := 916882010922246570788081

theorem tailTrace_2678432 : CollatzResearch.WordTrace tailWord_2678432 prefixEnd_2678432 916882010922246570788081 := by
  unfold tailWord_2678432
  simp only [CollatzResearch.WordTrace]
  refine ⟨48845220316252889306034775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65126960421670519074713033 48845220316252889306034775)
  ·
    refine ⟨73267830474379333959052163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48845220316252889306034775 73267830474379333959052163)
    ·
      refine ⟨109901745711569000938578245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73267830474379333959052163 109901745711569000938578245)
      ·
        refine ⟨20606577320919187675983421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109901745711569000938578245 20606577320919187675983421)
        ·
          refine ⟨7727466495344695378493783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20606577320919187675983421 7727466495344695378493783)
          ·
            refine ⟨11591199743017043067740675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727466495344695378493783 11591199743017043067740675)
            ·
              refine ⟨17386799614525564601611013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11591199743017043067740675 17386799614525564601611013)
              ·
                refine ⟨3260024927723543362802065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17386799614525564601611013 3260024927723543362802065)
                ·
                  refine ⟨2445018695792657522101549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260024927723543362802065 2445018695792657522101549)
                  ·
                    refine ⟨916882010922246570788081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445018695792657522101549 916882010922246570788081)
                    ·
                      rfl

theorem cell22_2678432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_2678432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678432 prefixEnd_2678432 := by exact prefixLift 2678432
  have htrace : WordTrace (prefixWord ++ tailWord_2678432) baseStart_2678432 baseEnd_2678432 := by
    simpa [prefixWord, tailWord_2678432, baseEnd_2678432] using wordTrace_append hprefix tailTrace_2678432
  have hstable : (prefixWord ++ tailWord_2678432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678432).length < 2 ^ (prefixWord ++ tailWord_2678432).sum := by decide
  have hdescent : baseEnd_2678432 < baseStart_2678432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678462 : List Nat := [4, 2, 1, 1, 2, 3, 3, 6]
def baseStart_2678462 : Nat := 118140960795 + 2678462 * 2 ^ 59
def prefixEnd_2678462 : Nat := 4983230072969 + 3 ^ 40 * 2678462 * 2
def baseEnd_2678462 : Nat := 101876920059481832504221

theorem tailTrace_2678462 : CollatzResearch.WordTrace tailWord_2678462 prefixEnd_2678462 101876920059481832504221 := by
  unfold tailWord_2678462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211441852799636716957705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65127689881598062490441093 12211441852799636716957705)
  ·
    refine ⟨9158581389599727537718279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12211441852799636716957705 9158581389599727537718279)
    ·
      refine ⟨13737872084399591306577419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9158581389599727537718279 13737872084399591306577419)
      ·
        refine ⟨20606808126599386959866129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13737872084399591306577419 20606808126599386959866129)
        ·
          refine ⟨15455106094949540219899597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20606808126599386959866129 15455106094949540219899597)
          ·
            refine ⟨5795664785606077582462349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15455106094949540219899597 5795664785606077582462349)
            ·
              refine ⟨2173374294602279093423381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5795664785606077582462349 2173374294602279093423381)
              ·
                refine ⟨101876920059481832504221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2173374294602279093423381 101876920059481832504221)
                ·
                  rfl

theorem cell22_2678462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_2678462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678462 prefixEnd_2678462 := by exact prefixLift 2678462
  have htrace : WordTrace (prefixWord ++ tailWord_2678462) baseStart_2678462 baseEnd_2678462 := by
    simpa [prefixWord, tailWord_2678462, baseEnd_2678462] using wordTrace_append hprefix tailTrace_2678462
  have hstable : (prefixWord ++ tailWord_2678462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678462).length < 2 ^ (prefixWord ++ tailWord_2678462).sum := by decide
  have hdescent : baseEnd_2678462 < baseStart_2678462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678490 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_2678490 : Nat := 118140960795 + 2678490 * 2 ^ 59
def prefixEnd_2678490 : Nat := 4983230072969 + 3 ^ 40 * 2678490 * 2
def baseEnd_2678490 : Nat := 305633955169184584279301

theorem tailTrace_2678490 : CollatzResearch.WordTrace tailWord_2678490 prefixEnd_2678490 305633955169184584279301 := by
  unfold tailWord_2678490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24423139016573913629420231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65128370710863769678453949 24423139016573913629420231)
  ·
    refine ⟨36634708524860870444130347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24423139016573913629420231 36634708524860870444130347)
    ·
      refine ⟨54952062787291305666195521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36634708524860870444130347 54952062787291305666195521)
      ·
        refine ⟨41214047090468479249646641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54952062787291305666195521 41214047090468479249646641)
        ·
          refine ⟨30910535317851359437234981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41214047090468479249646641 30910535317851359437234981)
          ·
            refine ⟨5795725372097129894481559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30910535317851359437234981 5795725372097129894481559)
            ·
              refine ⟨8693588058145694841722339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795725372097129894481559 8693588058145694841722339)
              ·
                refine ⟨13040382087218542262583509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8693588058145694841722339 13040382087218542262583509)
                ·
                  refine ⟨305633955169184584279301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13040382087218542262583509 305633955169184584279301)
                  ·
                    rfl

theorem cell22_2678490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_2678490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678490 prefixEnd_2678490 := by exact prefixLift 2678490
  have htrace : WordTrace (prefixWord ++ tailWord_2678490) baseStart_2678490 baseEnd_2678490 := by
    simpa [prefixWord, tailWord_2678490, baseEnd_2678490] using wordTrace_append hprefix tailTrace_2678490
  have hstable : (prefixWord ++ tailWord_2678490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678490).length < 2 ^ (prefixWord ++ tailWord_2678490).sum := by decide
  have hdescent : baseEnd_2678490 < baseStart_2678490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678552 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 4]
def baseStart_2678552 : Nat := 118140960795 + 2678552 * 2 ^ 59
def prefixEnd_2678552 : Nat := 4983230072969 + 3 ^ 40 * 2678552 * 2
def baseEnd_2678552 : Nat := 305641029791535419262571

theorem tailTrace_2678552 : CollatzResearch.WordTrace tailWord_2678552 prefixEnd_2678552 305641029791535419262571 := by
  unfold tailWord_2678552
  simp only [CollatzResearch.WordTrace]
  refine ⟨48847408696035519553218955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65129878261380692737625273 48847408696035519553218955)
  ·
    refine ⟨73271113044053279329828433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48847408696035519553218955 73271113044053279329828433)
    ·
      refine ⟨54953334783039959497371325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73271113044053279329828433 54953334783039959497371325)
      ·
        refine ⟨20607500543639984811514247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54953334783039959497371325 20607500543639984811514247)
        ·
          refine ⟨30911250815459977217271371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20607500543639984811514247 30911250815459977217271371)
          ·
            refine ⟨46366876223189965825907057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30911250815459977217271371 46366876223189965825907057)
            ·
              refine ⟨34775157167392474369430293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46366876223189965825907057 34775157167392474369430293)
              ·
                refine ⟨1630085492221522236067045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34775157167392474369430293 1630085492221522236067045)
                ·
                  refine ⟨305641029791535419262571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630085492221522236067045 305641029791535419262571)
                  ·
                    rfl

theorem cell22_2678552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_2678552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678552 prefixEnd_2678552 := by exact prefixLift 2678552
  have htrace : WordTrace (prefixWord ++ tailWord_2678552) baseStart_2678552 baseEnd_2678552 := by
    simpa [prefixWord, tailWord_2678552, baseEnd_2678552] using wordTrace_append hprefix tailTrace_2678552
  have hstable : (prefixWord ++ tailWord_2678552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678552).length < 2 ^ (prefixWord ++ tailWord_2678552).sum := by decide
  have hdescent : baseEnd_2678552 < baseStart_2678552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678640 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_2678640 : Nat := 118140960795 + 2678640 * 2 ^ 59
def prefixEnd_2678640 : Nat := 4983230072969 + 3 ^ 40 * 2678640 * 2
def baseEnd_2678640 : Nat := 916953213573003361587443

theorem tailTrace_2678640 : CollatzResearch.WordTrace tailWord_2678640 prefixEnd_2678640 916953213573003361587443 := by
  unfold tailWord_2678640
  simp only [CollatzResearch.WordTrace]
  refine ⟨48849013507876115067820687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65132018010501486757094249 48849013507876115067820687)
  ·
    refine ⟨73273520261814172601731031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48849013507876115067820687 73273520261814172601731031)
    ·
      refine ⟨109910280392721258902596547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73273520261814172601731031 109910280392721258902596547)
      ·
        refine ⟨164865420589081888353894821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109910280392721258902596547 164865420589081888353894821)
        ·
          refine ⟨30912266360452854066355279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164865420589081888353894821 30912266360452854066355279)
          ·
            refine ⟨46368399540679281099532919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30912266360452854066355279 46368399540679281099532919)
            ·
              refine ⟨69552599311018921649299379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46368399540679281099532919 69552599311018921649299379)
              ·
                refine ⟨104328898966528382473949069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69552599311018921649299379 104328898966528382473949069)
                ·
                  refine ⟨39123337112448143427730901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104328898966528382473949069 39123337112448143427730901)
                  ·
                    refine ⟨916953213573003361587443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39123337112448143427730901 916953213573003361587443)
                    ·
                      rfl

theorem cell22_2678640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_2678640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678640 prefixEnd_2678640 := by exact prefixLift 2678640
  have htrace : WordTrace (prefixWord ++ tailWord_2678640) baseStart_2678640 baseEnd_2678640 := by
    simpa [prefixWord, tailWord_2678640, baseEnd_2678640] using wordTrace_append hprefix tailTrace_2678640
  have hstable : (prefixWord ++ tailWord_2678640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678640).length < 2 ^ (prefixWord ++ tailWord_2678640).sum := by decide
  have hdescent : baseEnd_2678640 < baseStart_2678640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678659 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 5]
def baseStart_2678659 : Nat := 118140960795 + 2678659 * 2 ^ 59
def prefixEnd_2678659 : Nat := 4983230072969 + 3 ^ 40 * 2678659 * 2
def baseEnd_2678659 : Nat := 305653239220431215120795

theorem tailTrace_2678659 : CollatzResearch.WordTrace tailWord_2678659 prefixEnd_2678659 305653239220431215120795 := by
  unfold tailWord_2678659
  simp only [CollatzResearch.WordTrace]
  refine ⟨97698720002683396380583031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65132480001788930920388687 97698720002683396380583031)
  ·
    refine ⟨146548080004025094570874547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97698720002683396380583031 146548080004025094570874547)
    ·
      refine ⟨219822120006037641856311821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146548080004025094570874547 219822120006037641856311821)
      ·
        refine ⟨82433295002264115696116933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219822120006037641856311821 82433295002264115696116933)
        ·
          refine ⟨15456242812924521693021925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82433295002264115696116933 15456242812924521693021925)
          ·
            refine ⟨2898045527423347817441611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15456242812924521693021925 2898045527423347817441611)
            ·
              refine ⟨4347068291135021726162417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898045527423347817441611 4347068291135021726162417)
              ·
                refine ⟨3260301218351266294621813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347068291135021726162417 3260301218351266294621813)
                ·
                  refine ⟨305653239220431215120795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3260301218351266294621813 305653239220431215120795)
                  ·
                    rfl

theorem cell22_2678659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 5].length) (baseStart_2678659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678659 prefixEnd_2678659 := by exact prefixLift 2678659
  have htrace : WordTrace (prefixWord ++ tailWord_2678659) baseStart_2678659 baseEnd_2678659 := by
    simpa [prefixWord, tailWord_2678659, baseEnd_2678659] using wordTrace_append hprefix tailTrace_2678659
  have hstable : (prefixWord ++ tailWord_2678659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678659).length < 2 ^ (prefixWord ++ tailWord_2678659).sum := by decide
  have hdescent : baseEnd_2678659 < baseStart_2678659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678674 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2678674 : Nat := 118140960795 + 2678674 * 2 ^ 59
def prefixEnd_2678674 : Nat := 4983230072969 + 3 ^ 40 * 2678674 * 2
def baseEnd_2678674 : Nat := 916964852467838606237339

theorem tailTrace_2678674 : CollatzResearch.WordTrace tailWord_2678674 prefixEnd_2678674 916964852467838606237339 := by
  unfold tailWord_2678674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24424816774407263485594769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65132844731752702628252717 24424816774407263485594769)
  ·
    refine ⟨18318612580805447614196077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24424816774407263485594769 18318612580805447614196077)
    ·
      refine ⟨6869479717802042855323529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18318612580805447614196077 6869479717802042855323529)
      ·
        refine ⟨5152109788351532141492647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6869479717802042855323529 5152109788351532141492647)
        ·
          refine ⟨7728164682527298212238971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152109788351532141492647 7728164682527298212238971)
          ·
            refine ⟨11592247023790947318358457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7728164682527298212238971 11592247023790947318358457)
            ·
              refine ⟨8694185267843210488768843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11592247023790947318358457 8694185267843210488768843)
              ·
                refine ⟨13041277901764815733153265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8694185267843210488768843 13041277901764815733153265)
                ·
                  refine ⟨9780958426323611799864949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13041277901764815733153265 9780958426323611799864949)
                  ·
                    refine ⟨916964852467838606237339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9780958426323611799864949 916964852467838606237339)
                    ·
                      rfl

theorem cell22_2678674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2678674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678674 prefixEnd_2678674 := by exact prefixLift 2678674
  have htrace : WordTrace (prefixWord ++ tailWord_2678674) baseStart_2678674 baseEnd_2678674 := by
    simpa [prefixWord, tailWord_2678674, baseEnd_2678674] using wordTrace_append hprefix tailTrace_2678674
  have hstable : (prefixWord ++ tailWord_2678674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678674).length < 2 ^ (prefixWord ++ tailWord_2678674).sum := by decide
  have hdescent : baseEnd_2678674 < baseStart_2678674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678676 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 5]
def baseStart_2678676 : Nat := 118140960795 + 2678676 * 2 ^ 59
def prefixEnd_2678676 : Nat := 4983230072969 + 3 ^ 40 * 2678676 * 2
def baseEnd_2678676 : Nat := 305655179036237089229111

theorem tailTrace_2678676 : CollatzResearch.WordTrace tailWord_2678676 prefixEnd_2678676 305655179036237089229111 := by
  unfold tailWord_2678676
  simp only [CollatzResearch.WordTrace]
  refine ⟨48849670021810904141975941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65132893362414538855967921 48849670021810904141975941)
  ·
    refine ⟨9159313129089544526620489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48849670021810904141975941 9159313129089544526620489)
    ·
      refine ⟨6869484846817158394965367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9159313129089544526620489 6869484846817158394965367)
      ·
        refine ⟨10304227270225737592448051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869484846817158394965367 10304227270225737592448051)
        ·
          refine ⟨15456340905338606388672077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10304227270225737592448051 15456340905338606388672077)
          ·
            refine ⟨5796127839501977395752029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15456340905338606388672077 5796127839501977395752029)
            ·
              refine ⟨2173547939813241523407011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5796127839501977395752029 2173547939813241523407011)
              ·
                refine ⟨3260321909719862285110517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173547939813241523407011 3260321909719862285110517)
                ·
                  refine ⟨305655179036237089229111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3260321909719862285110517 305655179036237089229111)
                  ·
                    rfl

theorem cell22_2678676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_2678676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678676 prefixEnd_2678676 := by exact prefixLift 2678676
  have htrace : WordTrace (prefixWord ++ tailWord_2678676) baseStart_2678676 baseEnd_2678676 := by
    simpa [prefixWord, tailWord_2678676, baseEnd_2678676] using wordTrace_append hprefix tailTrace_2678676
  have hstable : (prefixWord ++ tailWord_2678676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678676).length < 2 ^ (prefixWord ++ tailWord_2678676).sum := by decide
  have hdescent : baseEnd_2678676 < baseStart_2678676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678719 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 2, 3]
def baseStart_2678719 : Nat := 118140960795 + 2678719 * 2 ^ 59
def prefixEnd_2678719 : Nat := 4983230072969 + 3 ^ 40 * 2678719 * 2
def baseEnd_2678719 : Nat := 916980256887473488862201

theorem tailTrace_2678719 : CollatzResearch.WordTrace tailWord_2678719 prefixEnd_2678719 916980256887473488862201 := by
  unfold tailWord_2678719
  simp only [CollatzResearch.WordTrace]
  refine ⟨97700908382466026627767211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65133938921644017751844807 97700908382466026627767211)
  ·
    refine ⟨146551362573699039941650817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97700908382466026627767211 146551362573699039941650817)
    ·
      refine ⟨109913521930274279956238113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146551362573699039941650817 109913521930274279956238113)
      ·
        refine ⟨82435141447705709967178585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109913521930274279956238113 82435141447705709967178585)
        ·
          refine ⟨61826356085779282475383939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82435141447705709967178585 61826356085779282475383939)
          ·
            refine ⟨92739534128668923713075909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61826356085779282475383939 92739534128668923713075909)
            ·
              refine ⟨17388662649125423196201733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92739534128668923713075909 17388662649125423196201733)
              ·
                refine ⟨3260374246711016849287825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17388662649125423196201733 3260374246711016849287825)
                ·
                  refine ⟨2445280685033262636965869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260374246711016849287825 2445280685033262636965869)
                  ·
                    refine ⟨916980256887473488862201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445280685033262636965869 916980256887473488862201)
                    ·
                      rfl

theorem cell22_2678719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_2678719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678719 prefixEnd_2678719 := by exact prefixLift 2678719
  have htrace : WordTrace (prefixWord ++ tailWord_2678719) baseStart_2678719 baseEnd_2678719 := by
    simpa [prefixWord, tailWord_2678719, baseEnd_2678719] using wordTrace_append hprefix tailTrace_2678719
  have hstable : (prefixWord ++ tailWord_2678719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678719).length < 2 ^ (prefixWord ++ tailWord_2678719).sum := by decide
  have hdescent : baseEnd_2678719 < baseStart_2678719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678732 : List Nat := [2, 2, 1, 4, 1, 2, 1, 9]
def baseStart_2678732 : Nat := 118140960795 + 2678732 * 2 ^ 59
def prefixEnd_2678732 : Nat := 4983230072969 + 3 ^ 40 * 2678732 * 2
def baseEnd_2678732 : Nat := 101887189672571754254129

theorem tailTrace_2678732 : CollatzResearch.WordTrace tailWord_2678732 prefixEnd_2678732 101887189672571754254129 := by
  unfold tailWord_2678732
  simp only [CollatzResearch.WordTrace]
  refine ⟨48850691265709464923995225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65134255020945953231993633 48850691265709464923995225)
  ·
    refine ⟨36638018449282098692996419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48850691265709464923995225 36638018449282098692996419)
    ·
      refine ⟨54957027673923148039494629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36638018449282098692996419 54957027673923148039494629)
      ·
        refine ⟨10304442688860590257405243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54957027673923148039494629 10304442688860590257405243)
        ·
          refine ⟨15456664033290885386107865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10304442688860590257405243 15456664033290885386107865)
          ·
            refine ⟨11592498024968164039580899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15456664033290885386107865 11592498024968164039580899)
            ·
              refine ⟨17388747037452246059371349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11592498024968164039580899 17388747037452246059371349)
              ·
                refine ⟨101887189672571754254129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17388747037452246059371349 101887189672571754254129)
                ·
                  rfl

theorem cell22_2678732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_2678732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678732 prefixEnd_2678732 := by exact prefixLift 2678732
  have htrace : WordTrace (prefixWord ++ tailWord_2678732) baseStart_2678732 baseEnd_2678732 := by
    simpa [prefixWord, tailWord_2678732, baseEnd_2678732] using wordTrace_append hprefix tailTrace_2678732
  have hstable : (prefixWord ++ tailWord_2678732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678732).length < 2 ^ (prefixWord ++ tailWord_2678732).sum := by decide
  have hdescent : baseEnd_2678732 < baseStart_2678732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678736 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 2, 3]
def baseStart_2678736 : Nat := 118140960795 + 2678736 * 2 ^ 59
def prefixEnd_2678736 : Nat := 4983230072969 + 3 ^ 40 * 2678736 * 2
def baseEnd_2678736 : Nat := 916986076334891111187149

theorem tailTrace_2678736 : CollatzResearch.WordTrace tailWord_2678736 prefixEnd_2678736 916986076334891111187149 := by
  unfold tailWord_2678736
  simp only [CollatzResearch.WordTrace]
  refine ⟨48850764211702219265568031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65134352282269625687424041 48850764211702219265568031)
  ·
    refine ⟨73276146317553328898352047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48850764211702219265568031 73276146317553328898352047)
    ·
      refine ⟨109914219476329993347528071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73276146317553328898352047 109914219476329993347528071)
      ·
        refine ⟨164871329214494990021292107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109914219476329993347528071 164871329214494990021292107)
        ·
          refine ⟨247306993821742485031938161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164871329214494990021292107 247306993821742485031938161)
          ·
            refine ⟨185480245366306863773953621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247306993821742485031938161 185480245366306863773953621)
            ·
              refine ⟨2173596625386408559851019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 185480245366306863773953621 2173596625386408559851019)
              ·
                refine ⟨3260394938079612839776529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173596625386408559851019 3260394938079612839776529)
                ·
                  refine ⟨2445296203559709629832397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260394938079612839776529 2445296203559709629832397)
                  ·
                    refine ⟨916986076334891111187149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445296203559709629832397 916986076334891111187149)
                    ·
                      rfl

theorem cell22_2678736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_2678736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678736 prefixEnd_2678736 := by exact prefixLift 2678736
  have htrace : WordTrace (prefixWord ++ tailWord_2678736) baseStart_2678736 baseEnd_2678736 := by
    simpa [prefixWord, tailWord_2678736, baseEnd_2678736] using wordTrace_append hprefix tailTrace_2678736
  have hstable : (prefixWord ++ tailWord_2678736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678736).length < 2 ^ (prefixWord ++ tailWord_2678736).sum := by decide
  have hdescent : baseEnd_2678736 < baseStart_2678736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678869 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2678869 : Nat := 118140960795 + 2678869 * 2 ^ 59
def prefixEnd_2678869 : Nat := 4983230072969 + 3 ^ 40 * 2678869 * 2
def baseEnd_2678869 : Nat := 917031604952923097611741

theorem tailTrace_2678869 : CollatzResearch.WordTrace tailWord_2678869 prefixEnd_2678869 917031604952923097611741 := by
  unfold tailWord_2678869
  simp only [CollatzResearch.WordTrace]
  refine ⟨97706379331922602245727661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65137586221281734830485107 97706379331922602245727661)
  ·
    refine ⟨36639892249470975842147873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97706379331922602245727661 36639892249470975842147873)
    ·
      refine ⟨27479919187103231881610905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36639892249470975842147873 27479919187103231881610905)
      ·
        refine ⟨20609939390327423911208179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27479919187103231881610905 20609939390327423911208179)
        ·
          refine ⟨30914909085491135866812269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20609939390327423911208179 30914909085491135866812269)
          ·
            refine ⟨11593090907059175950054601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30914909085491135866812269 11593090907059175950054601)
            ·
              refine ⟨8694818180294381962540951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11593090907059175950054601 8694818180294381962540951)
              ·
                refine ⟨13042227270441572943811427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8694818180294381962540951 13042227270441572943811427)
                ·
                  refine ⟨19563340905662359415717141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13042227270441572943811427 19563340905662359415717141)
                  ·
                    refine ⟨917031604952923097611741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19563340905662359415717141 917031604952923097611741)
                    ·
                      rfl

theorem cell22_2678869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2678869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678869 prefixEnd_2678869 := by exact prefixLift 2678869
  have htrace : WordTrace (prefixWord ++ tailWord_2678869) baseStart_2678869 baseEnd_2678869 := by
    simpa [prefixWord, tailWord_2678869, baseEnd_2678869] using wordTrace_append hprefix tailTrace_2678869
  have hstable : (prefixWord ++ tailWord_2678869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678869).length < 2 ^ (prefixWord ++ tailWord_2678869).sum := by decide
  have hdescent : baseEnd_2678869 < baseStart_2678869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678890 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_2678890 : Nat := 118140960795 + 2678890 * 2 ^ 59
def prefixEnd_2678890 : Nat := 4983230072969 + 3 ^ 40 * 2678890 * 2
def baseEnd_2678890 : Nat := 305679597894028680945559

theorem tailTrace_2678890 : CollatzResearch.WordTrace tailWord_2678890 prefixEnd_2678890 305679597894028680945559 := by
  unfold tailWord_2678890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24426786316211630708060531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65138096843231015221494749 24426786316211630708060531)
  ·
    refine ⟨36640179474317446062090797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24426786316211630708060531 36640179474317446062090797)
    ·
      refine ⟨13740067302869042273284049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36640179474317446062090797 13740067302869042273284049)
      ·
        refine ⟨10305050477151781704963037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13740067302869042273284049 10305050477151781704963037)
        ·
          refine ⟨3864393928931918139361139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10305050477151781704963037 3864393928931918139361139)
          ·
            refine ⟨5796590893397877209041709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864393928931918139361139 5796590893397877209041709)
            ·
              refine ⟨2173721585024203953390641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5796590893397877209041709 2173721585024203953390641)
              ·
                refine ⟨1630291188768152965042981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173721585024203953390641 1630291188768152965042981)
                ·
                  refine ⟨305679597894028680945559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630291188768152965042981 305679597894028680945559)
                  ·
                    rfl

theorem cell22_2678890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_2678890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678890 prefixEnd_2678890 := by exact prefixLift 2678890
  have htrace : WordTrace (prefixWord ++ tailWord_2678890) baseStart_2678890 baseEnd_2678890 := by
    simpa [prefixWord, tailWord_2678890, baseEnd_2678890] using wordTrace_append hprefix tailTrace_2678890
  have hstable : (prefixWord ++ tailWord_2678890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678890).length < 2 ^ (prefixWord ++ tailWord_2678890).sum := by decide
  have hdescent : baseEnd_2678890 < baseStart_2678890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678905 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 2, 3]
def baseStart_2678905 : Nat := 118140960795 + 2678905 * 2 ^ 59
def prefixEnd_2678905 : Nat := 4983230072969 + 3 ^ 40 * 2678905 * 2
def baseEnd_2678905 : Nat := 917043928488631003711631

theorem tailTrace_2678905 : CollatzResearch.WordTrace tailWord_2678905 prefixEnd_2678905 917043928488631003711631 := by
  unfold tailWord_2678905
  simp only [CollatzResearch.WordTrace]
  refine ⟨97707692359792180394038169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65138461573194786929358779 97707692359792180394038169)
  ·
    refine ⟨73280769269844135295528627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97707692359792180394038169 73280769269844135295528627)
    ·
      refine ⟨109921153904766202943292941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73280769269844135295528627 109921153904766202943292941)
      ·
        refine ⟨41220432714287326103734853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109921153904766202943292941 41220432714287326103734853)
        ·
          refine ⟨7728831133928873644450285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41220432714287326103734853 7728831133928873644450285)
          ·
            refine ⟨2898311675223327616668857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7728831133928873644450285 2898311675223327616668857)
            ·
              refine ⟨2173733756417495712501643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2898311675223327616668857 2173733756417495712501643)
              ·
                refine ⟨3260600634626243568752465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173733756417495712501643 3260600634626243568752465)
                ·
                  refine ⟨2445450475969682676564349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260600634626243568752465 2445450475969682676564349)
                  ·
                    refine ⟨917043928488631003711631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445450475969682676564349 917043928488631003711631)
                    ·
                      rfl

theorem cell22_2678905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_2678905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678905 prefixEnd_2678905 := by exact prefixLift 2678905
  have htrace : WordTrace (prefixWord ++ tailWord_2678905) baseStart_2678905 baseEnd_2678905 := by
    simpa [prefixWord, tailWord_2678905, baseEnd_2678905] using wordTrace_append hprefix tailTrace_2678905
  have hstable : (prefixWord ++ tailWord_2678905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678905).length < 2 ^ (prefixWord ++ tailWord_2678905).sum := by decide
  have hdescent : baseEnd_2678905 < baseStart_2678905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678916 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_2678916 : Nat := 118140960795 + 2678916 * 2 ^ 59
def prefixEnd_2678916 : Nat := 4983230072969 + 3 ^ 40 * 2678916 * 2
def baseEnd_2678916 : Nat := 917047694013430641686597

theorem tailTrace_2678916 : CollatzResearch.WordTrace tailWord_2678916 prefixEnd_2678916 917047694013430641686597 := by
  unfold tailWord_2678916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48854046781376164636344301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65138729041834886181792401 48854046781376164636344301)
  ·
    refine ⟨18320267543016061738629113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48854046781376164636344301 18320267543016061738629113)
    ·
      refine ⟨13740200657262046303971835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18320267543016061738629113 13740200657262046303971835)
      ·
        refine ⟨20610300985893069455957753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13740200657262046303971835 20610300985893069455957753)
        ·
          refine ⟨15457725739419802091968315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20610300985893069455957753 15457725739419802091968315)
          ·
            refine ⟨23186588609129703137952473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15457725739419802091968315 23186588609129703137952473)
            ·
              refine ⟨17389941456847277353464355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23186588609129703137952473 17389941456847277353464355)
              ·
                refine ⟨26084912185270916030196533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17389941456847277353464355 26084912185270916030196533)
                ·
                  refine ⟨2445460517369148377830925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26084912185270916030196533 2445460517369148377830925)
                  ·
                    refine ⟨917047694013430641686597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445460517369148377830925 917047694013430641686597)
                    ·
                      rfl

theorem cell22_2678916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_2678916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678916 prefixEnd_2678916 := by exact prefixLift 2678916
  have htrace : WordTrace (prefixWord ++ tailWord_2678916) baseStart_2678916 baseEnd_2678916 := by
    simpa [prefixWord, tailWord_2678916, baseEnd_2678916] using wordTrace_append hprefix tailTrace_2678916
  have hstable : (prefixWord ++ tailWord_2678916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678916).length < 2 ^ (prefixWord ++ tailWord_2678916).sum := by decide
  have hdescent : baseEnd_2678916 < baseStart_2678916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678933 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_2678933 : Nat := 118140960795 + 2678933 * 2 ^ 59
def prefixEnd_2678933 : Nat := 4983230072969 + 3 ^ 40 * 2678933 * 2
def baseEnd_2678933 : Nat := 917053513460848264011545

theorem tailTrace_2678933 : CollatzResearch.WordTrace tailWord_2678933 prefixEnd_2678933 917053513460848264011545 := by
  unfold tailWord_2678933
  simp only [CollatzResearch.WordTrace]
  refine ⟨97708713603690741176057453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65139142402460494117371635 97708713603690741176057453)
  ·
    refine ⟨36640767601384027941021545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97708713603690741176057453 36640767601384027941021545)
    ·
      refine ⟨27480575701038020955766159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36640767601384027941021545 27480575701038020955766159)
      ·
        refine ⟨41220863551557031433649239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27480575701038020955766159 41220863551557031433649239)
        ·
          refine ⟨61831295327335547150473859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41220863551557031433649239 61831295327335547150473859)
          ·
            refine ⟨92746942991003320725710789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61831295327335547150473859 92746942991003320725710789)
            ·
              refine ⟨17390051810813122636070773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92746942991003320725710789 17390051810813122636070773)
              ·
                refine ⟨1630317357263730247131635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17390051810813122636070773 1630317357263730247131635)
                ·
                  refine ⟨2445476035895595370697453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630317357263730247131635 2445476035895595370697453)
                  ·
                    refine ⟨917053513460848264011545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445476035895595370697453 917053513460848264011545)
                    ·
                      rfl

theorem cell22_2678933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_2678933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678933 prefixEnd_2678933 := by exact prefixLift 2678933
  have htrace : WordTrace (prefixWord ++ tailWord_2678933) baseStart_2678933 baseEnd_2678933 := by
    simpa [prefixWord, tailWord_2678933, baseEnd_2678933] using wordTrace_append hprefix tailTrace_2678933
  have hstable : (prefixWord ++ tailWord_2678933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678933).length < 2 ^ (prefixWord ++ tailWord_2678933).sum := by decide
  have hdescent : baseEnd_2678933 < baseStart_2678933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678976 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_2678976 : Nat := 118140960795 + 2678976 * 2 ^ 59
def prefixEnd_2678976 : Nat := 4983230072969 + 3 ^ 40 * 2678976 * 2
def baseEnd_2678976 : Nat := 917068233239610485186413

theorem tailTrace_2678976 : CollatzResearch.WordTrace tailWord_2678976 prefixEnd_2678976 917068233239610485186413 := by
  unfold tailWord_2678976
  simp only [CollatzResearch.WordTrace]
  refine ⟨48855140971267479759936391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65140187961689973013248521 48855140971267479759936391)
  ·
    refine ⟨73282711456901219639904587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48855140971267479759936391 73282711456901219639904587)
    ·
      refine ⟨109924067185351829459856881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73282711456901219639904587 109924067185351829459856881)
      ·
        refine ⟨82443050389013872094892661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109924067185351829459856881 82443050389013872094892661)
        ·
          refine ⟨7729035973970050508896187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82443050389013872094892661 7729035973970050508896187)
          ·
            refine ⟨11593553960955075763344281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729035973970050508896187 11593553960955075763344281)
            ·
              refine ⟨8695165470716306822508211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11593553960955075763344281 8695165470716306822508211)
              ·
                refine ⟨13042748206074460233762317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695165470716306822508211 13042748206074460233762317)
                ·
                  refine ⟨4891030577277922587660869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13042748206074460233762317 4891030577277922587660869)
                  ·
                    refine ⟨917068233239610485186413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4891030577277922587660869 917068233239610485186413)
                    ·
                      rfl

theorem cell22_2678976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_2678976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678976 prefixEnd_2678976 := by exact prefixLift 2678976
  have htrace : WordTrace (prefixWord ++ tailWord_2678976) baseStart_2678976 baseEnd_2678976 := by
    simpa [prefixWord, tailWord_2678976, baseEnd_2678976] using wordTrace_append hprefix tailTrace_2678976
  have hstable : (prefixWord ++ tailWord_2678976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678976).length < 2 ^ (prefixWord ++ tailWord_2678976).sum := by decide
  have hdescent : baseEnd_2678976 < baseStart_2678976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2678993 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 1, 4]
def baseStart_2678993 : Nat := 118140960795 + 2678993 * 2 ^ 59
def prefixEnd_2678993 : Nat := 4983230072969 + 3 ^ 40 * 2678993 * 2
def baseEnd_2678993 : Nat := 917074052687028107511361

theorem tailTrace_2678993 : CollatzResearch.WordTrace tailWord_2678993 prefixEnd_2678993 917074052687028107511361 := by
  unfold tailWord_2678993
  simp only [CollatzResearch.WordTrace]
  refine ⟨97710901983473371423241633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65140601322315580948827755 97710901983473371423241633)
  ·
    refine ⟨73283176487605028567431225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97710901983473371423241633 73283176487605028567431225)
    ·
      refine ⟨54962382365703771425573419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73283176487605028567431225 54962382365703771425573419)
      ·
        refine ⟨82443573548555657138360129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54962382365703771425573419 82443573548555657138360129)
        ·
          refine ⟨61832680161416742853770097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82443573548555657138360129 61832680161416742853770097)
          ·
            refine ⟨46374510121062557140327573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61832680161416742853770097 46374510121062557140327573)
            ·
              refine ⟨2173805161924807365952855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46374510121062557140327573 2173805161924807365952855)
              ·
                refine ⟨3260707742887211048929283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173805161924807365952855 3260707742887211048929283)
                ·
                  refine ⟨4891061614330816573393925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260707742887211048929283 4891061614330816573393925)
                  ·
                    refine ⟨917074052687028107511361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4891061614330816573393925 917074052687028107511361)
                    ·
                      rfl

theorem cell22_2678993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_2678993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2678993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2678993 prefixEnd_2678993 := by exact prefixLift 2678993
  have htrace : WordTrace (prefixWord ++ tailWord_2678993) baseStart_2678993 baseEnd_2678993 := by
    simpa [prefixWord, tailWord_2678993, baseEnd_2678993] using wordTrace_append hprefix tailTrace_2678993
  have hstable : (prefixWord ++ tailWord_2678993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2678993).length < 2 ^ (prefixWord ++ tailWord_2678993).sum := by decide
  have hdescent : baseEnd_2678993 < baseStart_2678993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2678993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679019 : List Nat := [1, 1, 1, 1, 2, 5, 2, 9]
def baseStart_2679019 : Nat := 118140960795 + 2679019 * 2 ^ 59
def prefixEnd_2679019 : Nat := 4983230072969 + 3 ^ 40 * 2679019 * 2
def baseEnd_2679019 : Nat := 101898105890930300706809

theorem tailTrace_2679019 : CollatzResearch.WordTrace tailWord_2679019 prefixEnd_2679019 101898105890930300706809 := by
  unfold tailWord_2679019
  simp only [CollatzResearch.WordTrace]
  refine ⟨97711850281379177863688111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65141233520919451909125407 97711850281379177863688111)
  ·
    refine ⟨146567775422068766795532167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97711850281379177863688111 146567775422068766795532167)
    ·
      refine ⟨219851663133103150193298251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146567775422068766795532167 219851663133103150193298251)
      ·
        refine ⟨329777494699654725289947377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219851663133103150193298251 329777494699654725289947377)
        ·
          refine ⟨247333121024741043967460533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329777494699654725289947377 247333121024741043967460533)
          ·
            refine ⟨23187480096069472871949425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247333121024741043967460533 23187480096069472871949425)
            ·
              refine ⟨17390610072052104653962069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23187480096069472871949425 17390610072052104653962069)
              ·
                refine ⟨101898105890930300706809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17390610072052104653962069 101898105890930300706809)
                ·
                  rfl

theorem cell22_2679019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 9].length) (baseStart_2679019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679019 prefixEnd_2679019 := by exact prefixLift 2679019
  have htrace : WordTrace (prefixWord ++ tailWord_2679019) baseStart_2679019 baseEnd_2679019 := by
    simpa [prefixWord, tailWord_2679019, baseEnd_2679019] using wordTrace_append hprefix tailTrace_2679019
  have hstable : (prefixWord ++ tailWord_2679019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679019).length < 2 ^ (prefixWord ++ tailWord_2679019).sum := by decide
  have hdescent : baseEnd_2679019 < baseStart_2679019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679023 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 1, 5]
def baseStart_2679023 : Nat := 118140960795 + 2679023 * 2 ^ 59
def prefixEnd_2679023 : Nat := 4983230072969 + 3 ^ 40 * 2679023 * 2
def baseEnd_2679023 : Nat := 917084322300118029261269

theorem tailTrace_2679023 : CollatzResearch.WordTrace tailWord_2679023 prefixEnd_2679023 917084322300118029261269 := by
  unfold tailWord_2679023
  simp only [CollatzResearch.WordTrace]
  refine ⟨97711996173364686546833723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65141330782243124364555815 97711996173364686546833723)
  ·
    refine ⟨146567994260047029820250585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97711996173364686546833723 146567994260047029820250585)
    ·
      refine ⟨109925995695035272365187939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146567994260047029820250585 109925995695035272365187939)
      ·
        refine ⟨164888993542552908547781909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109925995695035272365187939 164888993542552908547781909)
        ·
          refine ⟨7729171572307167588177277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164888993542552908547781909 7729171572307167588177277)
          ·
            refine ⟨2898439339615187845566479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7729171572307167588177277 2898439339615187845566479)
            ·
              refine ⟨4347659009422781768349719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898439339615187845566479 4347659009422781768349719)
              ·
                refine ⟨6521488514134172652524579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347659009422781768349719 6521488514134172652524579)
                ·
                  refine ⟨9782232771201258978786869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6521488514134172652524579 9782232771201258978786869)
                  ·
                    refine ⟨917084322300118029261269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9782232771201258978786869 917084322300118029261269)
                    ·
                      rfl

theorem cell22_2679023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_2679023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679023 prefixEnd_2679023 := by exact prefixLift 2679023
  have htrace : WordTrace (prefixWord ++ tailWord_2679023) baseStart_2679023 baseEnd_2679023 := by
    simpa [prefixWord, tailWord_2679023, baseEnd_2679023] using wordTrace_append hprefix tailTrace_2679023
  have hstable : (prefixWord ++ tailWord_2679023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679023).length < 2 ^ (prefixWord ++ tailWord_2679023).sum := by decide
  have hdescent : baseEnd_2679023 < baseStart_2679023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679036 : List Nat := [2, 2, 2, 1, 4, 2, 1, 8]
def baseStart_2679036 : Nat := 118140960795 + 2679036 * 2 ^ 59
def prefixEnd_2679036 : Nat := 4983230072969 + 3 ^ 40 * 2679036 * 2
def baseEnd_2679036 : Nat := 101898752496198925409581

theorem tailTrace_2679036 : CollatzResearch.WordTrace tailWord_2679036 prefixEnd_2679036 101898752496198925409581 := by
  unfold tailWord_2679036
  simp only [CollatzResearch.WordTrace]
  refine ⟨48856235161158794883528481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65141646881545059844704641 48856235161158794883528481)
  ·
    refine ⟨36642176370869096162646361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48856235161158794883528481 36642176370869096162646361)
    ·
      refine ⟨27481632278151822121984771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36642176370869096162646361 27481632278151822121984771)
      ·
        refine ⟨41222448417227733182977157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27481632278151822121984771 41222448417227733182977157)
        ·
          refine ⟨7729209078230199971808217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41222448417227733182977157 7729209078230199971808217)
          ·
            refine ⟨5796906808672649978856163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7729209078230199971808217 5796906808672649978856163)
            ·
              refine ⟨8695360213008974968284245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796906808672649978856163 8695360213008974968284245)
              ·
                refine ⟨101898752496198925409581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8695360213008974968284245 101898752496198925409581)
                ·
                  rfl

theorem cell22_2679036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_2679036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679036 prefixEnd_2679036 := by exact prefixLift 2679036
  have htrace : WordTrace (prefixWord ++ tailWord_2679036) baseStart_2679036 baseEnd_2679036 := by
    simpa [prefixWord, tailWord_2679036, baseEnd_2679036] using wordTrace_append hprefix tailTrace_2679036
  have hstable : (prefixWord ++ tailWord_2679036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679036).length < 2 ^ (prefixWord ++ tailWord_2679036).sum := by decide
  have hdescent : baseEnd_2679036 < baseStart_2679036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679038 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2679038 : Nat := 118140960795 + 2679038 * 2 ^ 59
def prefixEnd_2679038 : Nat := 4983230072969 + 3 ^ 40 * 2679038 * 2
def baseEnd_2679038 : Nat := 917089457106662990136223

theorem tailTrace_2679038 : CollatzResearch.WordTrace tailWord_2679038 prefixEnd_2679038 917089457106662990136223 := by
  unfold tailWord_2679038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214067908538793013578721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65141695512206896072419845 12214067908538793013578721)
  ·
    refine ⟨9160550931404094760184041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12214067908538793013578721 9160550931404094760184041)
    ·
      refine ⟨6870413198553071070138031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9160550931404094760184041 6870413198553071070138031)
      ·
        refine ⟨10305619797829606605207047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6870413198553071070138031 10305619797829606605207047)
        ·
          refine ⟨15458429696744409907810571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10305619797829606605207047 15458429696744409907810571)
          ·
            refine ⟨23187644545116614861715857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15458429696744409907810571 23187644545116614861715857)
            ·
              refine ⟨17390733408837461146286893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23187644545116614861715857 17390733408837461146286893)
              ·
                refine ⟨6521525028314047929857585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17390733408837461146286893 6521525028314047929857585)
                ·
                  refine ⟨4891143771235535947393189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6521525028314047929857585 4891143771235535947393189)
                  ·
                    refine ⟨917089457106662990136223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4891143771235535947393189 917089457106662990136223)
                    ·
                      rfl

theorem cell22_2679038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2679038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679038 prefixEnd_2679038 := by exact prefixLift 2679038
  have htrace : WordTrace (prefixWord ++ tailWord_2679038) baseStart_2679038 baseEnd_2679038 := by
    simpa [prefixWord, tailWord_2679038, baseEnd_2679038] using wordTrace_append hprefix tailTrace_2679038
  have hstable : (prefixWord ++ tailWord_2679038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679038).length < 2 ^ (prefixWord ++ tailWord_2679038).sum := by decide
  have hdescent : baseEnd_2679038 < baseStart_2679038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679042 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2679042 : Nat := 118140960795 + 2679042 * 2 ^ 59
def prefixEnd_2679042 : Nat := 4983230072969 + 3 ^ 40 * 2679042 * 2
def baseEnd_2679042 : Nat := 305696942129469437678737

theorem tailTrace_2679042 : CollatzResearch.WordTrace tailWord_2679042 prefixEnd_2679042 305696942129469437678737 := by
  unfold tailWord_2679042
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428172290073963197943845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65141792773530568527850253 24428172290073963197943845)
  ·
    refine ⟨4580282304388868099614471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24428172290073963197943845 4580282304388868099614471)
    ·
      refine ⟨6870423456583302149421707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580282304388868099614471 6870423456583302149421707)
      ·
        refine ⟨10305635184874953224132561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6870423456583302149421707 10305635184874953224132561)
        ·
          refine ⟨7729226388656214918099421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10305635184874953224132561 7729226388656214918099421)
          ·
            refine ⟨2898459895746080594287283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7729226388656214918099421 2898459895746080594287283)
            ·
              refine ⟨4347689843619120891430925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898459895746080594287283 4347689843619120891430925)
              ·
                refine ⟨1630383691357170334286597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4347689843619120891430925 1630383691357170334286597)
                ·
                  refine ⟨305696942129469437678737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630383691357170334286597 305696942129469437678737)
                  ·
                    rfl

theorem cell22_2679042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2679042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679042 prefixEnd_2679042 := by exact prefixLift 2679042
  have htrace : WordTrace (prefixWord ++ tailWord_2679042) baseStart_2679042 baseEnd_2679042 := by
    simpa [prefixWord, tailWord_2679042, baseEnd_2679042] using wordTrace_append hprefix tailTrace_2679042
  have hstable : (prefixWord ++ tailWord_2679042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679042).length < 2 ^ (prefixWord ++ tailWord_2679042).sum := by decide
  have hdescent : baseEnd_2679042 < baseStart_2679042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679070 : List Nat := [4, 3, 2, 1, 1, 2, 2, 7]
def baseStart_2679070 : Nat := 118140960795 + 2679070 * 2 ^ 59
def prefixEnd_2679070 : Nat := 4983230072969 + 3 ^ 40 * 2679070 * 2
def baseEnd_2679070 : Nat := 101900045706736174815125

theorem tailTrace_2679070 : CollatzResearch.WordTrace tailWord_2679070 prefixEnd_2679070 101900045706736174815125 := by
  unfold tailWord_2679070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214213800524301696724333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65142473602796275715863109 12214213800524301696724333)
  ·
    refine ⟨4580330175196613136271625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12214213800524301696724333 4580330175196613136271625)
    ·
      refine ⟨3435247631397459852203719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4580330175196613136271625 3435247631397459852203719)
      ·
        refine ⟨5152871447096189778305579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435247631397459852203719 5152871447096189778305579)
        ·
          refine ⟨7729307170644284667458369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152871447096189778305579 7729307170644284667458369)
          ·
            refine ⟨5796980377983213500593777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7729307170644284667458369 5796980377983213500593777)
            ·
              refine ⟨4347735283487410125445333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5796980377983213500593777 4347735283487410125445333)
              ·
                refine ⟨101900045706736174815125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4347735283487410125445333 101900045706736174815125)
                ·
                  rfl

theorem cell22_2679070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_2679070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679070 prefixEnd_2679070 := by exact prefixLift 2679070
  have htrace : WordTrace (prefixWord ++ tailWord_2679070) baseStart_2679070 baseEnd_2679070 := by
    simpa [prefixWord, tailWord_2679070, baseEnd_2679070] using wordTrace_append hprefix tailTrace_2679070
  have hstable : (prefixWord ++ tailWord_2679070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679070).length < 2 ^ (prefixWord ++ tailWord_2679070).sum := by decide
  have hdescent : baseEnd_2679070 < baseStart_2679070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679143 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 6]
def baseStart_2679143 : Nat := 118140960795 + 2679143 * 2 ^ 59
def prefixEnd_2679143 : Nat := 4983230072969 + 3 ^ 40 * 2679143 * 2
def baseEnd_2679143 : Nat := 305708466917492572086967

theorem tailTrace_2679143 : CollatzResearch.WordTrace tailWord_2679143 prefixEnd_2679143 305708466917492572086967 := by
  unfold tailWord_2679143
  simp only [CollatzResearch.WordTrace]
  refine ⟨97716372932929947041202083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65144248621953298027468055 97716372932929947041202083)
  ·
    refine ⟨146574559399394920561803125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97716372932929947041202083 146574559399394920561803125)
    ·
      refine ⟨13741364943693273802669043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146574559399394920561803125 13741364943693273802669043)
      ·
        refine ⟨20612047415539910704003565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13741364943693273802669043 20612047415539910704003565)
        ·
          refine ⟨7729517780827466514001337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20612047415539910704003565 7729517780827466514001337)
          ·
            refine ⟨5797138335620599885501003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7729517780827466514001337 5797138335620599885501003)
            ·
              refine ⟨8695707503430899828251505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797138335620599885501003 8695707503430899828251505)
              ·
                refine ⟨6521780627573174871188629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8695707503430899828251505 6521780627573174871188629)
                ·
                  refine ⟨305708466917492572086967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6521780627573174871188629 305708466917492572086967)
                  ·
                    rfl

theorem cell22_2679143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 6].length) (baseStart_2679143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679143 prefixEnd_2679143 := by exact prefixLift 2679143
  have htrace : WordTrace (prefixWord ++ tailWord_2679143) baseStart_2679143 baseEnd_2679143 := by
    simpa [prefixWord, tailWord_2679143, baseEnd_2679143] using wordTrace_append hprefix tailTrace_2679143
  have hstable : (prefixWord ++ tailWord_2679143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679143).length < 2 ^ (prefixWord ++ tailWord_2679143).sum := by decide
  have hdescent : baseEnd_2679143 < baseStart_2679143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679293 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2679293 : Nat := 118140960795 + 2679293 * 2 ^ 59
def prefixEnd_2679293 : Nat := 4983230072969 + 3 ^ 40 * 2679293 * 2
def baseEnd_2679293 : Nat := 917176748817927325010441

theorem tailTrace_2679293 : CollatzResearch.WordTrace tailWord_2679293 prefixEnd_2679293 917176748817927325010441 := by
  unfold tailWord_2679293
  simp only [CollatzResearch.WordTrace]
  refine ⟨97721843882386522659162533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65147895921591015106108355 97721843882386522659162533)
  ·
    refine ⟨18322845727947472998592975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97721843882386522659162533 18322845727947472998592975)
    ·
      refine ⟨27484268591921209497889463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18322845727947472998592975 27484268591921209497889463)
      ·
        refine ⟨41226402887881814246834195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27484268591921209497889463 41226402887881814246834195)
        ·
          refine ⟨61839604331822721370251293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41226402887881814246834195 61839604331822721370251293)
          ·
            refine ⟨23189851624433520513844235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61839604331822721370251293 23189851624433520513844235)
            ·
              refine ⟨34784777436650280770766353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23189851624433520513844235 34784777436650280770766353)
              ·
                refine ⟨26088583077487710578074765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34784777436650280770766353 26088583077487710578074765)
                ·
                  refine ⟨9783218654057891466778037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26088583077487710578074765 9783218654057891466778037)
                  ·
                    refine ⟨917176748817927325010441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9783218654057891466778037 917176748817927325010441)
                    ·
                      rfl

theorem cell22_2679293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2679293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679293 prefixEnd_2679293 := by exact prefixLift 2679293
  have htrace : WordTrace (prefixWord ++ tailWord_2679293) baseStart_2679293 baseEnd_2679293 := by
    simpa [prefixWord, tailWord_2679293, baseEnd_2679293] using wordTrace_append hprefix tailTrace_2679293
  have hstable : (prefixWord ++ tailWord_2679293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679293).length < 2 ^ (prefixWord ++ tailWord_2679293).sum := by decide
  have hdescent : baseEnd_2679293 < baseStart_2679293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679295 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 4]
def baseStart_2679295 : Nat := 118140960795 + 2679295 * 2 ^ 59
def prefixEnd_2679295 : Nat := 4983230072969 + 3 ^ 40 * 2679295 * 2
def baseEnd_2679295 : Nat := 305725811152933328820145

theorem tailTrace_2679295 : CollatzResearch.WordTrace tailWord_2679295 prefixEnd_2679295 305725811152933328820145 := by
  unfold tailWord_2679295
  simp only [CollatzResearch.WordTrace]
  refine ⟨97721916828379277000735339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65147944552252851333823559 97721916828379277000735339)
  ·
    refine ⟨146582875242568915501103009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97721916828379277000735339 146582875242568915501103009)
    ·
      refine ⟨109937156431926686625827257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146582875242568915501103009 109937156431926686625827257)
      ·
        refine ⟨82452867323945014969370443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109937156431926686625827257 82452867323945014969370443)
        ·
          refine ⟨123679300985917522454055665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82452867323945014969370443 123679300985917522454055665)
          ·
            refine ⟨92759475739438141840541749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123679300985917522454055665 92759475739438141840541749)
            ·
              refine ⟨8696200850572325797550789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92759475739438141840541749 8696200850572325797550789)
              ·
                refine ⟨1630537659482311087040773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8696200850572325797550789 1630537659482311087040773)
                ·
                  refine ⟨305725811152933328820145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630537659482311087040773 305725811152933328820145)
                  ·
                    rfl

theorem cell22_2679295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 4].length) (baseStart_2679295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679295 prefixEnd_2679295 := by exact prefixLift 2679295
  have htrace : WordTrace (prefixWord ++ tailWord_2679295) baseStart_2679295 baseEnd_2679295 := by
    simpa [prefixWord, tailWord_2679295, baseEnd_2679295] using wordTrace_append hprefix tailTrace_2679295
  have hstable : (prefixWord ++ tailWord_2679295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679295).length < 2 ^ (prefixWord ++ tailWord_2679295).sum := by decide
  have hdescent : baseEnd_2679295 < baseStart_2679295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679310 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2679310 : Nat := 118140960795 + 2679310 * 2 ^ 59
def prefixEnd_2679310 : Nat := 4983230072969 + 3 ^ 40 * 2679310 * 2
def baseEnd_2679310 : Nat := 917182568265344947335389

theorem tailTrace_2679310 : CollatzResearch.WordTrace tailWord_2679310 prefixEnd_2679310 917182568265344947335389 := by
  unfold tailWord_2679310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215307990415616820316423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65148309282216623041687589 12215307990415616820316423)
  ·
    refine ⟨18322961985623425230474635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215307990415616820316423 18322961985623425230474635)
    ·
      refine ⟨27484442978435137845711953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18322961985623425230474635 27484442978435137845711953)
      ·
        refine ⟨20613332233826353384283965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27484442978435137845711953 20613332233826353384283965)
        ·
          refine ⟨7729999587684882519106487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20613332233826353384283965 7729999587684882519106487)
          ·
            refine ⟨11594999381527323778659731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729999587684882519106487 11594999381527323778659731)
            ·
              refine ⟨17392499072290985667989597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11594999381527323778659731 17392499072290985667989597)
              ·
                refine ⟨6522187152109119625496099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17392499072290985667989597 6522187152109119625496099)
                ·
                  refine ⟨9783280728163679438244149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6522187152109119625496099 9783280728163679438244149)
                  ·
                    refine ⟨917182568265344947335389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9783280728163679438244149 917182568265344947335389)
                    ·
                      rfl

theorem cell22_2679310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2679310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679310 prefixEnd_2679310 := by exact prefixLift 2679310
  have htrace : WordTrace (prefixWord ++ tailWord_2679310) baseStart_2679310 baseEnd_2679310 := by
    simpa [prefixWord, tailWord_2679310, baseEnd_2679310] using wordTrace_append hprefix tailTrace_2679310
  have hstable : (prefixWord ++ tailWord_2679310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679310).length < 2 ^ (prefixWord ++ tailWord_2679310).sum := by decide
  have hdescent : baseEnd_2679310 < baseStart_2679310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679325 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2679325 : Nat := 118140960795 + 2679325 * 2 ^ 59
def prefixEnd_2679325 : Nat := 4983230072969 + 3 ^ 40 * 2679325 * 2
def baseEnd_2679325 : Nat := 917187703071889908210343

theorem tailTrace_2679325 : CollatzResearch.WordTrace tailWord_2679325 prefixEnd_2679325 917187703071889908210343 := by
  unfold tailWord_2679325
  simp only [CollatzResearch.WordTrace]
  refine ⟨97723011018270592124327429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65148674012180394749551619 97723011018270592124327429)
  ·
    refine ⟨18323064565925736023311393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97723011018270592124327429 18323064565925736023311393)
    ·
      refine ⟨13742298424444302017483545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18323064565925736023311393 13742298424444302017483545)
      ·
        refine ⟨10306723818333226513112659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13742298424444302017483545 10306723818333226513112659)
        ·
          refine ⟨15460085727499839769668989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306723818333226513112659 15460085727499839769668989)
          ·
            refine ⟨5797532147812439913625871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15460085727499839769668989 5797532147812439913625871)
            ·
              refine ⟨8696298221718659870438807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797532147812439913625871 8696298221718659870438807)
              ·
                refine ⟨13044447332577989805658211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696298221718659870438807 13044447332577989805658211)
                ·
                  refine ⟨19566670998866984708487317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13044447332577989805658211 19566670998866984708487317)
                  ·
                    refine ⟨917187703071889908210343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19566670998866984708487317 917187703071889908210343)
                    ·
                      rfl

theorem cell22_2679325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2679325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679325 prefixEnd_2679325 := by exact prefixLift 2679325
  have htrace : WordTrace (prefixWord ++ tailWord_2679325) baseStart_2679325 baseEnd_2679325 := by
    simpa [prefixWord, tailWord_2679325, baseEnd_2679325] using wordTrace_append hprefix tailTrace_2679325
  have hstable : (prefixWord ++ tailWord_2679325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679325).length < 2 ^ (prefixWord ++ tailWord_2679325).sum := by decide
  have hdescent : baseEnd_2679325 < baseStart_2679325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679447 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 4]
def baseStart_2679447 : Nat := 118140960795 + 2679447 * 2 ^ 59
def prefixEnd_2679447 : Nat := 4983230072969 + 3 ^ 40 * 2679447 * 2
def baseEnd_2679447 : Nat := 305743155388374085553323

theorem tailTrace_2679447 : CollatzResearch.WordTrace tailWord_2679447 prefixEnd_2679447 305743155388374085553323 := by
  unfold tailWord_2679447
  simp only [CollatzResearch.WordTrace]
  refine ⟨97727460723828606960268595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65151640482552404640179063 97727460723828606960268595)
  ·
    refine ⟨146591191085742910440402893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97727460723828606960268595 146591191085742910440402893)
    ·
      refine ⟨54971696657153591415151085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146591191085742910440402893 54971696657153591415151085)
      ·
        refine ⟨20614386246432596780681657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54971696657153591415151085 20614386246432596780681657)
        ·
          refine ⟨15460789684824447585511243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20614386246432596780681657 15460789684824447585511243)
          ·
            refine ⟨23191184527236671378266865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15460789684824447585511243 23191184527236671378266865)
            ·
              refine ⟨17393388395427503533700149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23191184527236671378266865 17393388395427503533700149)
              ·
                refine ⟨1630630162071328456284389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17393388395427503533700149 1630630162071328456284389)
                ·
                  refine ⟨305743155388374085553323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630630162071328456284389 305743155388374085553323)
                  ·
                    rfl

theorem cell22_2679447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 4].length) (baseStart_2679447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679447 prefixEnd_2679447 := by exact prefixLift 2679447
  have htrace : WordTrace (prefixWord ++ tailWord_2679447) baseStart_2679447 baseEnd_2679447 := by
    simpa [prefixWord, tailWord_2679447, baseEnd_2679447] using wordTrace_append hprefix tailTrace_2679447
  have hstable : (prefixWord ++ tailWord_2679447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679447).length < 2 ^ (prefixWord ++ tailWord_2679447).sum := by decide
  have hdescent : baseEnd_2679447 < baseStart_2679447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679475 : List Nat := [1, 1, 1, 2, 3, 4, 3, 7]
def baseStart_2679475 : Nat := 118140960795 + 2679475 * 2 ^ 59
def prefixEnd_2679475 : Nat := 4983230072969 + 3 ^ 40 * 2679475 * 2
def baseEnd_2679475 : Nat := 101915450126371057439987

theorem tailTrace_2679475 : CollatzResearch.WordTrace tailWord_2679475 prefixEnd_2679475 101915450126371057439987 := by
  unfold tailWord_2679475
  simp only [CollatzResearch.WordTrace]
  refine ⟨97728481967727167742287879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65152321311818111828191919 97728481967727167742287879)
  ·
    refine ⟨146592722951590751613431819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97728481967727167742287879 146592722951590751613431819)
    ·
      refine ⟨219889084427386127420147729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146592722951590751613431819 219889084427386127420147729)
      ·
        refine ⟨164916813320539595565110797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219889084427386127420147729 164916813320539595565110797)
        ·
          refine ⟨61843804995202348336916549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164916813320539595565110797 61843804995202348336916549)
          ·
            refine ⟨11595713436600440313171853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61843804995202348336916549 11595713436600440313171853)
            ·
              refine ⟨4348392538725165117439445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11595713436600440313171853 4348392538725165117439445)
              ·
                refine ⟨101915450126371057439987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4348392538725165117439445 101915450126371057439987)
                ·
                  rfl

theorem cell22_2679475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 7].length) (baseStart_2679475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679475 prefixEnd_2679475 := by exact prefixLift 2679475
  have htrace : WordTrace (prefixWord ++ tailWord_2679475) baseStart_2679475 baseEnd_2679475 := by
    simpa [prefixWord, tailWord_2679475, baseEnd_2679475] using wordTrace_append hprefix tailTrace_2679475
  have hstable : (prefixWord ++ tailWord_2679475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679475).length < 2 ^ (prefixWord ++ tailWord_2679475).sum := by decide
  have hdescent : baseEnd_2679475 < baseStart_2679475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679524 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_2679524 : Nat := 118140960795 + 2679524 * 2 ^ 59
def prefixEnd_2679524 : Nat := 4983230072969 + 3 ^ 40 * 2679524 * 2
def baseEnd_2679524 : Nat := 917255824838719722484733

theorem tailTrace_2679524 : CollatzResearch.WordTrace tailWord_2679524 prefixEnd_2679524 917255824838719722484733 := by
  unfold tailWord_2679524
  simp only [CollatzResearch.WordTrace]
  refine ⟨48865134572274824555410813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65153512763033099407214417 48865134572274824555410813)
  ·
    refine ⟨18324425464603059208279055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48865134572274824555410813 18324425464603059208279055)
    ·
      refine ⟨27486638196904588812418583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18324425464603059208279055 27486638196904588812418583)
      ·
        refine ⟨41229957295356883218627875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27486638196904588812418583 41229957295356883218627875)
        ·
          refine ⟨61844935943035324827941813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41229957295356883218627875 61844935943035324827941813)
          ·
            refine ⟨5797962744659561702619545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61844935943035324827941813 5797962744659561702619545)
            ·
              refine ⟨4348472058494671276964659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5797962744659561702619545 4348472058494671276964659)
              ·
                refine ⟨6522708087742006915446989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348472058494671276964659 6522708087742006915446989)
                ·
                  refine ⟨2446015532903252593292621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6522708087742006915446989 2446015532903252593292621)
                  ·
                    refine ⟨917255824838719722484733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446015532903252593292621 917255824838719722484733)
                    ·
                      rfl

theorem cell22_2679524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_2679524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679524 prefixEnd_2679524 := by exact prefixLift 2679524
  have htrace : WordTrace (prefixWord ++ tailWord_2679524) baseStart_2679524 baseEnd_2679524 := by
    simpa [prefixWord, tailWord_2679524, baseEnd_2679524] using wordTrace_append hprefix tailTrace_2679524
  have hstable : (prefixWord ++ tailWord_2679524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679524).length < 2 ^ (prefixWord ++ tailWord_2679524).sum := by decide
  have hdescent : baseEnd_2679524 < baseStart_2679524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679567 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 1, 4]
def baseStart_2679567 : Nat := 118140960795 + 2679567 * 2 ^ 59
def prefixEnd_2679567 : Nat := 4983230072969 + 3 ^ 40 * 2679567 * 2
def baseEnd_2679567 : Nat := 917270544617481943659601

theorem tailTrace_2679567 : CollatzResearch.WordTrace tailWord_2679567 prefixEnd_2679567 917270544617481943659601 := by
  unfold tailWord_2679567
  simp only [CollatzResearch.WordTrace]
  refine ⟨97731837483393867454636955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65154558322262578303091303 97731837483393867454636955)
  ·
    refine ⟨146597756225090801181955433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97731837483393867454636955 146597756225090801181955433)
    ·
      refine ⟨109948317168818100886466575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146597756225090801181955433 109948317168818100886466575)
      ·
        refine ⟨164922475753227151329699863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109948317168818100886466575 164922475753227151329699863)
        ·
          refine ⟨247383713629840726994549795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164922475753227151329699863 247383713629840726994549795)
          ·
            refine ⟨371075570444761090491824693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247383713629840726994549795 371075570444761090491824693)
            ·
              refine ⟨34788334729196352233608565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 371075570444761090491824693 34788334729196352233608565)
              ·
                refine ⟨3261406380862158021900803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34788334729196352233608565 3261406380862158021900803)
                ·
                  refine ⟨4892109571293237032851205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261406380862158021900803 4892109571293237032851205)
                  ·
                    refine ⟨917270544617481943659601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4892109571293237032851205 917270544617481943659601)
                    ·
                      rfl

theorem cell22_2679567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_2679567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679567 prefixEnd_2679567 := by exact prefixLift 2679567
  have htrace : WordTrace (prefixWord ++ tailWord_2679567) baseStart_2679567 baseEnd_2679567 := by
    simpa [prefixWord, tailWord_2679567, baseEnd_2679567] using wordTrace_append hprefix tailTrace_2679567
  have hstable : (prefixWord ++ tailWord_2679567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679567).length < 2 ^ (prefixWord ++ tailWord_2679567).sum := by decide
  have hdescent : baseEnd_2679567 < baseStart_2679567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679588 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 5]
def baseStart_2679588 : Nat := 118140960795 + 2679588 * 2 ^ 59
def prefixEnd_2679588 : Nat := 4983230072969 + 3 ^ 40 * 2679588 * 2
def baseEnd_2679588 : Nat := 305759244448881629628179

theorem tailTrace_2679588 : CollatzResearch.WordTrace tailWord_2679588 prefixEnd_2679588 305759244448881629628179 := by
  unfold tailWord_2679588
  simp only [CollatzResearch.WordTrace]
  refine ⟨48866301708158894020575709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65155068944211858694100945 48866301708158894020575709)
  ·
    refine ⟨18324863140559585257715891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48866301708158894020575709 18324863140559585257715891)
    ·
      refine ⟨27487294710839377886573837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18324863140559585257715891 27487294710839377886573837)
      ·
        refine ⟨10307735516564766707465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27487294710839377886573837 10307735516564766707465189)
        ·
          refine ⟨1932700409355893757649723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10307735516564766707465189 1932700409355893757649723)
          ·
            refine ⟨2899050614033840636474585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932700409355893757649723 2899050614033840636474585)
            ·
              refine ⟨2174287960525380477355939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899050614033840636474585 2174287960525380477355939)
              ·
                refine ⟨3261431940788070716033909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174287960525380477355939 3261431940788070716033909)
                ·
                  refine ⟨305759244448881629628179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3261431940788070716033909 305759244448881629628179)
                  ·
                    rfl

theorem cell22_2679588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_2679588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679588 prefixEnd_2679588 := by exact prefixLift 2679588
  have htrace : WordTrace (prefixWord ++ tailWord_2679588) baseStart_2679588 baseEnd_2679588 := by
    simpa [prefixWord, tailWord_2679588, baseEnd_2679588] using wordTrace_append hprefix tailTrace_2679588
  have hstable : (prefixWord ++ tailWord_2679588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679588).length < 2 ^ (prefixWord ++ tailWord_2679588).sum := by decide
  have hdescent : baseEnd_2679588 < baseStart_2679588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679633 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 4]
def baseStart_2679633 : Nat := 118140960795 + 2679633 * 2 ^ 59
def prefixEnd_2679633 : Nat := 4983230072969 + 3 ^ 40 * 2679633 * 2
def baseEnd_2679633 : Nat := 305764379255426590503133

theorem tailTrace_2679633 : CollatzResearch.WordTrace tailWord_2679633 prefixEnd_2679633 305764379255426590503133 := by
  unfold tailWord_2679633
  simp only [CollatzResearch.WordTrace]
  refine ⟨97734244701154760726539553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65156163134103173817693035 97734244701154760726539553)
  ·
    refine ⟨73300683525866070544904665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97734244701154760726539553 73300683525866070544904665)
    ·
      refine ⟨54975512644399552908678499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73300683525866070544904665 54975512644399552908678499)
      ·
        refine ⟨82463268966599329363017749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54975512644399552908678499 82463268966599329363017749)
        ·
          refine ⟨3865465732809343563891457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82463268966599329363017749 3865465732809343563891457)
          ·
            refine ⟨2899099299607007672918593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865465732809343563891457 2899099299607007672918593)
            ·
              refine ⟨2174324474705255754688945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899099299607007672918593 2174324474705255754688945)
              ·
                refine ⟨1630743356028941816016709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174324474705255754688945 1630743356028941816016709)
                ·
                  refine ⟨305764379255426590503133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630743356028941816016709 305764379255426590503133)
                  ·
                    rfl

theorem cell22_2679633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_2679633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679633 prefixEnd_2679633 := by exact prefixLift 2679633
  have htrace : WordTrace (prefixWord ++ tailWord_2679633) baseStart_2679633 baseEnd_2679633 := by
    simpa [prefixWord, tailWord_2679633, baseEnd_2679633] using wordTrace_append hprefix tailTrace_2679633
  have hstable : (prefixWord ++ tailWord_2679633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679633).length < 2 ^ (prefixWord ++ tailWord_2679633).sum := by decide
  have hdescent : baseEnd_2679633 < baseStart_2679633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679644 : List Nat := [2, 2, 4, 2, 1, 1, 3, 7]
def baseStart_2679644 : Nat := 118140960795 + 2679644 * 2 ^ 59
def prefixEnd_2679644 : Nat := 4983230072969 + 3 ^ 40 * 2679644 * 2
def baseEnd_2679644 : Nat := 101921878143453267720485

theorem tailTrace_2679644 : CollatzResearch.WordTrace tailWord_2679644 prefixEnd_2679644 101921878143453267720485 := by
  unfold tailWord_2679644
  simp only [CollatzResearch.WordTrace]
  refine ⟨48867322952057454802594993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65156430602743273070126657 48867322952057454802594993)
  ·
    refine ⟨36650492214043091101946245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48867322952057454802594993 36650492214043091101946245)
    ·
      refine ⟨6871967290133079581614921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36650492214043091101946245 6871967290133079581614921)
      ·
        refine ⟨5153975467599809686211191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6871967290133079581614921 5153975467599809686211191)
        ·
          refine ⟨7730963201399714529316787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153975467599809686211191 7730963201399714529316787)
          ·
            refine ⟨11596444802099571793975181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7730963201399714529316787 11596444802099571793975181)
            ·
              refine ⟨4348666800787339422740693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11596444802099571793975181 4348666800787339422740693)
              ·
                refine ⟨101921878143453267720485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4348666800787339422740693 101921878143453267720485)
                ·
                  rfl

theorem cell22_2679644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_2679644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679644 prefixEnd_2679644 := by exact prefixLift 2679644
  have htrace : WordTrace (prefixWord ++ tailWord_2679644) baseStart_2679644 baseEnd_2679644 := by
    simpa [prefixWord, tailWord_2679644, baseEnd_2679644] using wordTrace_append hprefix tailTrace_2679644
  have hstable : (prefixWord ++ tailWord_2679644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679644).length < 2 ^ (prefixWord ++ tailWord_2679644).sum := by decide
  have hdescent : baseEnd_2679644 < baseStart_2679644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679682 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2679682 : Nat := 118140960795 + 2679682 * 2 ^ 59
def prefixEnd_2679682 : Nat := 4983230072969 + 3 ^ 40 * 2679682 * 2
def baseEnd_2679682 : Nat := 917309911467659977034249

theorem tailTrace_2679682 : CollatzResearch.WordTrace tailWord_2679682 prefixEnd_2679682 917309911467659977034249 := by
  unfold tailWord_2679682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24434007969494310523768325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65157354585318161396715533 24434007969494310523768325)
  ·
    refine ⟨4581376494280183223206561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24434007969494310523768325 4581376494280183223206561)
    ·
      refine ⟨3436032370710137417404921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4581376494280183223206561 3436032370710137417404921)
      ·
        refine ⟨2577024278032603063053691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3436032370710137417404921 2577024278032603063053691)
        ·
          refine ⟨3865536417048904594580537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577024278032603063053691 3865536417048904594580537)
          ·
            refine ⟨2899152312786678445935403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865536417048904594580537 2899152312786678445935403)
            ·
              refine ⟨4348728469180017668903105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899152312786678445935403 4348728469180017668903105)
              ·
                refine ⟨3261546351885013251677329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4348728469180017668903105 3261546351885013251677329)
                ·
                  refine ⟨2446159763913759938757997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261546351885013251677329 2446159763913759938757997)
                  ·
                    refine ⟨917309911467659977034249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446159763913759938757997 917309911467659977034249)
                    ·
                      rfl

theorem cell22_2679682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2679682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679682 prefixEnd_2679682 := by exact prefixLift 2679682
  have htrace : WordTrace (prefixWord ++ tailWord_2679682) baseStart_2679682 baseEnd_2679682 := by
    simpa [prefixWord, tailWord_2679682, baseEnd_2679682] using wordTrace_append hprefix tailTrace_2679682
  have hstable : (prefixWord ++ tailWord_2679682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679682).length < 2 ^ (prefixWord ++ tailWord_2679682).sum := by decide
  have hdescent : baseEnd_2679682 < baseStart_2679682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679689 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 5]
def baseStart_2679689 : Nat := 118140960795 + 2679689 * 2 ^ 59
def prefixEnd_2679689 : Nat := 4983230072969 + 3 ^ 40 * 2679689 * 2
def baseEnd_2679689 : Nat := 305770769236904764036409

theorem tailTrace_2679689 : CollatzResearch.WordTrace tailWord_2679689 prefixEnd_2679689 305770769236904764036409 := by
  unfold tailWord_2679689
  simp only [CollatzResearch.WordTrace]
  refine ⟨97736287188951882290578121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65157524792634588193718747 97736287188951882290578121)
  ·
    refine ⟨73302215391713911717933591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97736287188951882290578121 73302215391713911717933591)
    ·
      refine ⟨109953323087570867576900387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73302215391713911717933591 109953323087570867576900387)
      ·
        refine ⟨164929984631356301365350581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109953323087570867576900387 164929984631356301365350581)
        ·
          refine ⟨15462186059189653253001617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164929984631356301365350581 15462186059189653253001617)
          ·
            refine ⟨11596639544392239939751213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15462186059189653253001617 11596639544392239939751213)
            ·
              refine ⟨4348739829147089977406705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11596639544392239939751213 4348739829147089977406705)
              ·
                refine ⟨3261554871860317483055029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4348739829147089977406705 3261554871860317483055029)
                ·
                  refine ⟨305770769236904764036409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3261554871860317483055029 305770769236904764036409)
                  ·
                    rfl

theorem cell22_2679689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_2679689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679689 prefixEnd_2679689 := by exact prefixLift 2679689
  have htrace : WordTrace (prefixWord ++ tailWord_2679689) baseStart_2679689 baseEnd_2679689 := by
    simpa [prefixWord, tailWord_2679689, baseEnd_2679689] using wordTrace_append hprefix tailTrace_2679689
  have hstable : (prefixWord ++ tailWord_2679689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679689).length < 2 ^ (prefixWord ++ tailWord_2679689).sum := by decide
  have hdescent : baseEnd_2679689 < baseStart_2679689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679809 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2679809 : Nat := 118140960795 + 2679809 * 2 ^ 59
def prefixEnd_2679809 : Nat := 4983230072969 + 3 ^ 40 * 2679809 * 2
def baseEnd_2679809 : Nat := 917353386163073979108859

theorem tailTrace_2679809 : CollatzResearch.WordTrace tailWord_2679809 prefixEnd_2679809 917353386163073979108859 := by
  unfold tailWord_2679809
  simp only [CollatzResearch.WordTrace]
  refine ⟨97740663948517142784946481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65160442632344761856630987 97740663948517142784946481)
  ·
    refine ⟨73305497961387857088709861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97740663948517142784946481 73305497961387857088709861)
    ·
      refine ⟨13744780867760223204133099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73305497961387857088709861 13744780867760223204133099)
      ·
        refine ⟨20617171301640334806199649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13744780867760223204133099 20617171301640334806199649)
        ·
          refine ⟨15462878476230251104649737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20617171301640334806199649 15462878476230251104649737)
          ·
            refine ⟨11597158857172688328487303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15462878476230251104649737 11597158857172688328487303)
            ·
              refine ⟨17395738285759032492730955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11597158857172688328487303 17395738285759032492730955)
              ·
                refine ⟨26093607428638548739096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17395738285759032492730955 26093607428638548739096433)
                ·
                  refine ⟨19570205571478911554322325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26093607428638548739096433 19570205571478911554322325)
                  ·
                    refine ⟨917353386163073979108859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19570205571478911554322325 917353386163073979108859)
                    ·
                      rfl

theorem cell22_2679809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2679809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679809 prefixEnd_2679809 := by exact prefixLift 2679809
  have htrace : WordTrace (prefixWord ++ tailWord_2679809) baseStart_2679809 baseEnd_2679809 := by
    simpa [prefixWord, tailWord_2679809, baseEnd_2679809] using wordTrace_append hprefix tailTrace_2679809
  have hstable : (prefixWord ++ tailWord_2679809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679809).length < 2 ^ (prefixWord ++ tailWord_2679809).sum := by decide
  have hdescent : baseEnd_2679809 < baseStart_2679809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679916 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_2679916 : Nat := 118140960795 + 2679916 * 2 ^ 59
def prefixEnd_2679916 : Nat := 4983230072969 + 3 ^ 40 * 2679916 * 2
def baseEnd_2679916 : Nat := 917390014449761366683531

theorem tailTrace_2679916 : CollatzResearch.WordTrace tailWord_2679916 prefixEnd_2679916 917390014449761366683531 := by
  unfold tailWord_2679916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48872283279564750029545801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65163044372753000039394401 48872283279564750029545801)
  ·
    refine ⟨36654212459673562522159351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48872283279564750029545801 36654212459673562522159351)
    ·
      refine ⟨54981318689510343783239027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36654212459673562522159351 54981318689510343783239027)
      ·
        refine ⟨82471978034265515674858541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54981318689510343783239027 82471978034265515674858541)
        ·
          refine ⟨30926991762849568378071953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82471978034265515674858541 30926991762849568378071953)
          ·
            refine ⟨23195243822137176283553965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30926991762849568378071953 23195243822137176283553965)
            ·
              refine ⟨8698216433301441106332737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23195243822137176283553965 8698216433301441106332737)
              ·
                refine ⟨6523662324976080829749553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8698216433301441106332737 6523662324976080829749553)
                ·
                  refine ⟨4892746743732060622312165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6523662324976080829749553 4892746743732060622312165)
                  ·
                    refine ⟨917390014449761366683531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4892746743732060622312165 917390014449761366683531)
                    ·
                      rfl

theorem cell22_2679916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_2679916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679916 prefixEnd_2679916 := by exact prefixLift 2679916
  have htrace : WordTrace (prefixWord ++ tailWord_2679916) baseStart_2679916 baseEnd_2679916 := by
    simpa [prefixWord, tailWord_2679916, baseEnd_2679916] using wordTrace_append hprefix tailTrace_2679916
  have hstable : (prefixWord ++ tailWord_2679916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679916).length < 2 ^ (prefixWord ++ tailWord_2679916).sum := by decide
  have hdescent : baseEnd_2679916 < baseStart_2679916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679918 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2679918 : Nat := 118140960795 + 2679918 * 2 ^ 59
def prefixEnd_2679918 : Nat := 4983230072969 + 3 ^ 40 * 2679918 * 2
def baseEnd_2679918 : Nat := 917390699090634028133525

theorem tailTrace_2679918 : CollatzResearch.WordTrace tailWord_2679918 prefixEnd_2679918 917390699090634028133525 := by
  unfold tailWord_2679918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12218079938140281800083051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65163093003414836267109605 12218079938140281800083051)
  ·
    refine ⟨18327119907210422700124577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12218079938140281800083051 18327119907210422700124577)
    ·
      refine ⟨13745339930407817025093433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18327119907210422700124577 13745339930407817025093433)
      ·
        refine ⟨10309004947805862768820075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13745339930407817025093433 10309004947805862768820075)
        ·
          refine ⟨15463507421708794153230113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10309004947805862768820075 15463507421708794153230113)
          ·
            refine ⟨11597630566281595614922585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15463507421708794153230113 11597630566281595614922585)
            ·
              refine ⟨8698222924711196711191939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11597630566281595614922585 8698222924711196711191939)
              ·
                refine ⟨13047334387066795066787909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8698222924711196711191939 13047334387066795066787909)
                ·
                  refine ⟨2446375197575024075022733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13047334387066795066787909 2446375197575024075022733)
                  ·
                    refine ⟨917390699090634028133525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446375197575024075022733 917390699090634028133525)
                    ·
                      rfl

theorem cell22_2679918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2679918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679918 prefixEnd_2679918 := by exact prefixLift 2679918
  have htrace : WordTrace (prefixWord ++ tailWord_2679918) baseStart_2679918 baseEnd_2679918 := by
    simpa [prefixWord, tailWord_2679918, baseEnd_2679918] using wordTrace_append hprefix tailTrace_2679918
  have hstable : (prefixWord ++ tailWord_2679918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679918).length < 2 ^ (prefixWord ++ tailWord_2679918).sum := by decide
  have hdescent : baseEnd_2679918 < baseStart_2679918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679978 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2679978 : Nat := 118140960795 + 2679978 * 2 ^ 59
def prefixEnd_2679978 : Nat := 4983230072969 + 3 ^ 40 * 2679978 * 2
def baseEnd_2679978 : Nat := 917411238316813871633341

theorem tailTrace_2679978 : CollatzResearch.WordTrace tailWord_2679978 prefixEnd_2679978 917411238316813871633341 := by
  unfold tailWord_2679978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24436706971226221161962147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65164551923269923098565725 24436706971226221161962147)
  ·
    refine ⟨36655060456839331742943221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24436706971226221161962147 36655060456839331742943221)
    ·
      refine ⟨3436411917828687350900927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36655060456839331742943221 3436411917828687350900927)
      ·
        refine ⟨5154617876743031026351391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436411917828687350900927 5154617876743031026351391)
        ·
          refine ⟨7731926815114546539527087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5154617876743031026351391 7731926815114546539527087)
          ·
            refine ⟨11597890222671819809290631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7731926815114546539527087 11597890222671819809290631)
            ·
              refine ⟨17396835334007729713935947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11597890222671819809290631 17396835334007729713935947)
              ·
                refine ⟨26095253001011594570903921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17396835334007729713935947 26095253001011594570903921)
                ·
                  refine ⟨19571439750758695928177941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26095253001011594570903921 19571439750758695928177941)
                  ·
                    refine ⟨917411238316813871633341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19571439750758695928177941 917411238316813871633341)
                    ·
                      rfl

theorem cell22_2679978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2679978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679978 prefixEnd_2679978 := by exact prefixLift 2679978
  have htrace : WordTrace (prefixWord ++ tailWord_2679978) baseStart_2679978 baseEnd_2679978 := by
    simpa [prefixWord, tailWord_2679978, baseEnd_2679978] using wordTrace_append hprefix tailTrace_2679978
  have hstable : (prefixWord ++ tailWord_2679978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679978).length < 2 ^ (prefixWord ++ tailWord_2679978).sum := by decide
  have hdescent : baseEnd_2679978 < baseStart_2679978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2679991 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2679991 : Nat := 118140960795 + 2679991 * 2 ^ 59
def prefixEnd_2679991 : Nat := 4983230072969 + 3 ^ 40 * 2679991 * 2
def baseEnd_2679991 : Nat := 917415688482486171058301

theorem tailTrace_2679991 : CollatzResearch.WordTrace tailWord_2679991 prefixEnd_2679991 917415688482486171058301 := by
  unfold tailWord_2679991
  simp only [CollatzResearch.WordTrace]
  refine ⟨97747302033857787868071827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65164868022571858578714551 97747302033857787868071827)
  ·
    refine ⟨146620953050786681802107741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97747302033857787868071827 146620953050786681802107741)
    ·
      refine ⟨54982857394045005675790403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146620953050786681802107741 54982857394045005675790403)
      ·
        refine ⟨82474286091067508513685605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54982857394045005675790403 82474286091067508513685605)
        ·
          refine ⟨15463928642075157846316051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82474286091067508513685605 15463928642075157846316051)
          ·
            refine ⟨23195892963112736769474077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15463928642075157846316051 23195892963112736769474077)
            ·
              refine ⟨8698459861167276288552779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23195892963112736769474077 8698459861167276288552779)
              ·
                refine ⟨13047689791750914432829169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8698459861167276288552779 13047689791750914432829169)
                ·
                  refine ⟨9785767343813185824621877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13047689791750914432829169 9785767343813185824621877)
                  ·
                    refine ⟨917415688482486171058301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9785767343813185824621877 917415688482486171058301)
                    ·
                      rfl

theorem cell22_2679991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2679991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2679991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2679991 prefixEnd_2679991 := by exact prefixLift 2679991
  have htrace : WordTrace (prefixWord ++ tailWord_2679991) baseStart_2679991 baseEnd_2679991 := by
    simpa [prefixWord, tailWord_2679991, baseEnd_2679991] using wordTrace_append hprefix tailTrace_2679991
  have hstable : (prefixWord ++ tailWord_2679991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2679991).length < 2 ^ (prefixWord ++ tailWord_2679991).sum := by decide
  have hdescent : baseEnd_2679991 < baseStart_2679991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2679991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680036 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_2680036 : Nat := 118140960795 + 2680036 * 2 ^ 59
def prefixEnd_2680036 : Nat := 4983230072969 + 3 ^ 40 * 2680036 * 2
def baseEnd_2680036 : Nat := 917431092902121053683163

theorem tailTrace_2680036 : CollatzResearch.WordTrace tailWord_2680036 prefixEnd_2680036 917431092902121053683163 := by
  unfold tailWord_2680036
  simp only [CollatzResearch.WordTrace]
  refine ⟨48874471659347380276729981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65165962212463173702306641 48874471659347380276729981)
  ·
    refine ⟨18327926872255267603773743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48874471659347380276729981 18327926872255267603773743)
    ·
      refine ⟨27491890308382901405660615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18327926872255267603773743 27491890308382901405660615)
      ·
        refine ⟨41237835462574352108490923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27491890308382901405660615 41237835462574352108490923)
        ·
          refine ⟨61856753193861528162736385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41237835462574352108490923 61856753193861528162736385)
          ·
            refine ⟨46392564895396146122052289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61856753193861528162736385 46392564895396146122052289)
            ·
              refine ⟨34794423671547109591539217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46392564895396146122052289 34794423671547109591539217)
              ·
                refine ⟨26095817753660332193654413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34794423671547109591539217 26095817753660332193654413)
                ·
                  refine ⟨9785931657622624572620405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26095817753660332193654413 9785931657622624572620405)
                  ·
                    refine ⟨917431092902121053683163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9785931657622624572620405 917431092902121053683163)
                    ·
                      rfl

theorem cell22_2680036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_2680036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680036 prefixEnd_2680036 := by exact prefixLift 2680036
  have htrace : WordTrace (prefixWord ++ tailWord_2680036) baseStart_2680036 baseEnd_2680036 := by
    simpa [prefixWord, tailWord_2680036, baseEnd_2680036] using wordTrace_append hprefix tailTrace_2680036
  have hstable : (prefixWord ++ tailWord_2680036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680036).length < 2 ^ (prefixWord ++ tailWord_2680036).sum := by decide
  have hdescent : baseEnd_2680036 < baseStart_2680036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680051 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_2680051 : Nat := 118140960795 + 2680051 * 2 ^ 59
def prefixEnd_2680051 : Nat := 4983230072969 + 3 ^ 40 * 2680051 * 2
def baseEnd_2680051 : Nat := 917436227708666014558117

theorem tailTrace_2680051 : CollatzResearch.WordTrace tailWord_2680051 prefixEnd_2680051 917436227708666014558117 := by
  unfold tailWord_2680051
  simp only [CollatzResearch.WordTrace]
  refine ⟨97749490413640418115256007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65166326942426945410170671 97749490413640418115256007)
  ·
    refine ⟨146624235620460627172884011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97749490413640418115256007 146624235620460627172884011)
    ·
      refine ⟨219936353430690940759326017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146624235620460627172884011 219936353430690940759326017)
      ·
        refine ⟨164952265073018205569494513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219936353430690940759326017 164952265073018205569494513)
        ·
          refine ⟨123714198804763654177120885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164952265073018205569494513 123714198804763654177120885)
          ·
            refine ⟨11598206137946592579105083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123714198804763654177120885 11598206137946592579105083)
            ·
              refine ⟨17397309206919888868657625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11598206137946592579105083 17397309206919888868657625)
              ·
                refine ⟨13047981905189916651493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17397309206919888868657625 13047981905189916651493219)
                ·
                  refine ⟨19571972857784874977239829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13047981905189916651493219 19571972857784874977239829)
                  ·
                    refine ⟨917436227708666014558117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19571972857784874977239829 917436227708666014558117)
                    ·
                      rfl

theorem cell22_2680051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_2680051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680051 prefixEnd_2680051 := by exact prefixLift 2680051
  have htrace : WordTrace (prefixWord ++ tailWord_2680051) baseStart_2680051 baseEnd_2680051 := by
    simpa [prefixWord, tailWord_2680051, baseEnd_2680051] using wordTrace_append hprefix tailTrace_2680051
  have hstable : (prefixWord ++ tailWord_2680051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680051).length < 2 ^ (prefixWord ++ tailWord_2680051).sum := by decide
  have hdescent : baseEnd_2680051 < baseStart_2680051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680068 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2680068 : Nat := 118140960795 + 2680068 * 2 ^ 59
def prefixEnd_2680068 : Nat := 4983230072969 + 3 ^ 40 * 2680068 * 2
def baseEnd_2680068 : Nat := 917442047156083636883065

theorem tailTrace_2680068 : CollatzResearch.WordTrace tailWord_2680068 prefixEnd_2680068 917442047156083636883065 := by
  unfold tailWord_2680068
  simp only [CollatzResearch.WordTrace]
  refine ⟨48875055227289415009312429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65166740303052553345749905 48875055227289415009312429)
  ·
    refine ⟨18328145710233530628492161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48875055227289415009312429 18328145710233530628492161)
    ·
      refine ⟨13746109282675147971369121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18328145710233530628492161 13746109282675147971369121)
      ·
        refine ⟨10309581962006360978526841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13746109282675147971369121 10309581962006360978526841)
        ·
          refine ⟨7732186471504770733895131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10309581962006360978526841 7732186471504770733895131)
          ·
            refine ⟨11598279707257156100842697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732186471504770733895131 11598279707257156100842697)
            ·
              refine ⟨8698709780442867075632023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11598279707257156100842697 8698709780442867075632023)
              ·
                refine ⟨13048064670664300613448035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8698709780442867075632023 13048064670664300613448035)
                ·
                  refine ⟨19572097005996450920172053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13048064670664300613448035 19572097005996450920172053)
                  ·
                    refine ⟨917442047156083636883065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19572097005996450920172053 917442047156083636883065)
                    ·
                      rfl

theorem cell22_2680068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2680068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680068 prefixEnd_2680068 := by exact prefixLift 2680068
  have htrace : WordTrace (prefixWord ++ tailWord_2680068) baseStart_2680068 baseEnd_2680068 := by
    simpa [prefixWord, tailWord_2680068, baseEnd_2680068] using wordTrace_append hprefix tailTrace_2680068
  have hstable : (prefixWord ++ tailWord_2680068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680068).length < 2 ^ (prefixWord ++ tailWord_2680068).sum := by decide
  have hdescent : baseEnd_2680068 < baseStart_2680068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680072 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 4]
def baseStart_2680072 : Nat := 118140960795 + 2680072 * 2 ^ 59
def prefixEnd_2680072 : Nat := 4983230072969 + 3 ^ 40 * 2680072 * 2
def baseEnd_2680072 : Nat := 305814472145942986594351

theorem tailTrace_2680072 : CollatzResearch.WordTrace tailWord_2680072 prefixEnd_2680072 305814472145942986594351 := by
  unfold tailWord_2680072
  simp only [CollatzResearch.WordTrace]
  refine ⟨48875128173282169350885235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65166837564376225801180313 48875128173282169350885235)
  ·
    refine ⟨73312692259923254026327853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48875128173282169350885235 73312692259923254026327853)
    ·
      refine ⟨27492259597471220259872945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73312692259923254026327853 27492259597471220259872945)
      ·
        refine ⟨20619194698103415194904709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27492259597471220259872945 20619194698103415194904709)
        ·
          refine ⟨3866099005894390349044633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20619194698103415194904709 3866099005894390349044633)
          ·
            refine ⟨2899574254420792761783475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866099005894390349044633 2899574254420792761783475)
            ·
              refine ⟨4349361381631189142675213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899574254420792761783475 4349361381631189142675213)
              ·
                refine ⟨1631010518111695928503205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4349361381631189142675213 1631010518111695928503205)
                ·
                  refine ⟨305814472145942986594351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1631010518111695928503205 305814472145942986594351)
                  ·
                    rfl

theorem cell22_2680072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_2680072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680072 prefixEnd_2680072 := by exact prefixLift 2680072
  have htrace : WordTrace (prefixWord ++ tailWord_2680072) baseStart_2680072 baseEnd_2680072 := by
    simpa [prefixWord, tailWord_2680072, baseEnd_2680072] using wordTrace_append hprefix tailTrace_2680072
  have hstable : (prefixWord ++ tailWord_2680072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680072).length < 2 ^ (prefixWord ++ tailWord_2680072).sum := by decide
  have hdescent : baseEnd_2680072 < baseStart_2680072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680104 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2680104 : Nat := 118140960795 + 2680104 * 2 ^ 59
def prefixEnd_2680104 : Nat := 4983230072969 + 3 ^ 40 * 2680104 * 2
def baseEnd_2680104 : Nat := 917454370691791542982955

theorem tailTrace_2680104 : CollatzResearch.WordTrace tailWord_2680104 prefixEnd_2680104 917454370691791542982955 := by
  unfold tailWord_2680104
  simp only [CollatzResearch.WordTrace]
  refine ⟨48875711741224204083467683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65167615654965605444623577 48875711741224204083467683)
  ·
    refine ⟨73313567611836306125201525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48875711741224204083467683 73313567611836306125201525)
    ·
      refine ⟨6873146963609653699237643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73313567611836306125201525 6873146963609653699237643)
      ·
        refine ⟨10309720445414480548856465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6873146963609653699237643 10309720445414480548856465)
        ·
          refine ⟨7732290334060860411642349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10309720445414480548856465 7732290334060860411642349)
          ·
            refine ⟨2899608875272822654365881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7732290334060860411642349 2899608875272822654365881)
            ·
              refine ⟨2174706656454616990774411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899608875272822654365881 2174706656454616990774411)
              ·
                refine ⟨3262059984681925486161617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174706656454616990774411 3262059984681925486161617)
                ·
                  refine ⟨2446544988511444114621213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262059984681925486161617 2446544988511444114621213)
                  ·
                    refine ⟨917454370691791542982955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446544988511444114621213 917454370691791542982955)
                    ·
                      rfl

theorem cell22_2680104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2680104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680104 prefixEnd_2680104 := by exact prefixLift 2680104
  have htrace : WordTrace (prefixWord ++ tailWord_2680104) baseStart_2680104 baseEnd_2680104 := by
    simpa [prefixWord, tailWord_2680104, baseEnd_2680104] using wordTrace_append hprefix tailTrace_2680104
  have hstable : (prefixWord ++ tailWord_2680104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680104).length < 2 ^ (prefixWord ++ tailWord_2680104).sum := by decide
  have hdescent : baseEnd_2680104 < baseStart_2680104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680149 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_2680149 : Nat := 118140960795 + 2680149 * 2 ^ 59
def prefixEnd_2680149 : Nat := 4983230072969 + 3 ^ 40 * 2680149 * 2
def baseEnd_2680149 : Nat := 917469775111426425607817

theorem tailTrace_2680149 : CollatzResearch.WordTrace tailWord_2680149 prefixEnd_2680149 917469775111426425607817 := by
  unfold tailWord_2680149
  simp only [CollatzResearch.WordTrace]
  refine ⟨97753064767285380852323501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65168709844856920568215667 97753064767285380852323501)
  ·
    refine ⟨36657399287732017819621313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97753064767285380852323501 36657399287732017819621313)
    ·
      refine ⟨27493049465799013364715985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36657399287732017819621313 27493049465799013364715985)
      ·
        refine ⟨20619787099349260023536989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27493049465799013364715985 20619787099349260023536989)
        ·
          refine ⟨7732420162255972508826371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20619787099349260023536989 7732420162255972508826371)
          ·
            refine ⟨11598630243383958763239557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732420162255972508826371 11598630243383958763239557)
            ·
              refine ⟨2174743170634492268107417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11598630243383958763239557 2174743170634492268107417)
              ·
                refine ⟨1631057377975869201080563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174743170634492268107417 1631057377975869201080563)
                ·
                  refine ⟨2446586066963803801620845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631057377975869201080563 2446586066963803801620845)
                  ·
                    refine ⟨917469775111426425607817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446586066963803801620845 917469775111426425607817)
                    ·
                      rfl

theorem cell22_2680149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_2680149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680149 prefixEnd_2680149 := by exact prefixLift 2680149
  have htrace : WordTrace (prefixWord ++ tailWord_2680149) baseStart_2680149 baseEnd_2680149 := by
    simpa [prefixWord, tailWord_2680149, baseEnd_2680149] using wordTrace_append hprefix tailTrace_2680149
  have hstable : (prefixWord ++ tailWord_2680149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680149).length < 2 ^ (prefixWord ++ tailWord_2680149).sum := by decide
  have hdescent : baseEnd_2680149 < baseStart_2680149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680173 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2680173 : Nat := 118140960795 + 2680173 * 2 ^ 59
def prefixEnd_2680173 : Nat := 4983230072969 + 3 ^ 40 * 2680173 * 2
def baseEnd_2680173 : Nat := 305825996933966121002581

theorem tailTrace_2680173 : CollatzResearch.WordTrace tailWord_2680173 prefixEnd_2680173 305825996933966121002581 := by
  unfold tailWord_2680173
  simp only [CollatzResearch.WordTrace]
  refine ⟨97753940119198432951197173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65169293412798955300798115 97753940119198432951197173)
  ·
    refine ⟨9164431886174853089174735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97753940119198432951197173 9164431886174853089174735)
    ·
      refine ⟨13746647829262279633762103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9164431886174853089174735 13746647829262279633762103)
      ·
        refine ⟨20619971743893419450643155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13746647829262279633762103 20619971743893419450643155)
        ·
          refine ⟨30929957615840129175964733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20619971743893419450643155 30929957615840129175964733)
          ·
            refine ⟨11598734105940048440986775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30929957615840129175964733 11598734105940048440986775)
            ·
              refine ⟨17398101158910072661480163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11598734105940048440986775 17398101158910072661480163)
              ·
                refine ⟨26097151738365108992220245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17398101158910072661480163 26097151738365108992220245)
                ·
                  refine ⟨305825996933966121002581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26097151738365108992220245 305825996933966121002581)
                  ·
                    rfl

theorem cell22_2680173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2680173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680173 prefixEnd_2680173 := by exact prefixLift 2680173
  have htrace : WordTrace (prefixWord ++ tailWord_2680173) baseStart_2680173 baseEnd_2680173 := by
    simpa [prefixWord, tailWord_2680173, baseEnd_2680173] using wordTrace_append hprefix tailTrace_2680173
  have hstable : (prefixWord ++ tailWord_2680173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680173).length < 2 ^ (prefixWord ++ tailWord_2680173).sum := by decide
  have hdescent : baseEnd_2680173 < baseStart_2680173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680188 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_2680188 : Nat := 118140960795 + 2680188 * 2 ^ 59
def prefixEnd_2680188 : Nat := 4983230072969 + 3 ^ 40 * 2680188 * 2
def baseEnd_2680188 : Nat := 917483125608443323882697

theorem tailTrace_2680188 : CollatzResearch.WordTrace tailWord_2680188 prefixEnd_2680188 917483125608443323882697 := by
  unfold tailWord_2680188
  simp only [CollatzResearch.WordTrace]
  refine ⟨48877243607072045256496609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65169658142762727008662145 48877243607072045256496609)
  ·
    refine ⟨36657932705304033942372457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48877243607072045256496609 36657932705304033942372457)
    ·
      refine ⟨27493449528978025456779343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36657932705304033942372457 27493449528978025456779343)
      ·
        refine ⟨41240174293467038185169015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27493449528978025456779343 41240174293467038185169015)
        ·
          refine ⟨61860261440200557277753523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41240174293467038185169015 61860261440200557277753523)
          ·
            refine ⟨92790392160300835916630285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61860261440200557277753523 92790392160300835916630285)
            ·
              refine ⟨34796397060112813468736357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92790392160300835916630285 34796397060112813468736357)
              ·
                refine ⟨6524324448771152525388067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34796397060112813468736357 6524324448771152525388067)
                ·
                  refine ⟨9786486673156728788082101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524324448771152525388067 9786486673156728788082101)
                  ·
                    refine ⟨917483125608443323882697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9786486673156728788082101 917483125608443323882697)
                    ·
                      rfl

theorem cell22_2680188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_2680188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680188 prefixEnd_2680188 := by exact prefixLift 2680188
  have htrace : WordTrace (prefixWord ++ tailWord_2680188) baseStart_2680188 baseEnd_2680188 := by
    simpa [prefixWord, tailWord_2680188, baseEnd_2680188] using wordTrace_append hprefix tailTrace_2680188
  have hstable : (prefixWord ++ tailWord_2680188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680188).length < 2 ^ (prefixWord ++ tailWord_2680188).sum := by decide
  have hdescent : baseEnd_2680188 < baseStart_2680188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680203 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 4, 4]
def baseStart_2680203 : Nat := 118140960795 + 2680203 * 2 ^ 59
def prefixEnd_2680203 : Nat := 4983230072969 + 3 ^ 40 * 2680203 * 2
def baseEnd_2680203 : Nat := 917488260414988284757651

theorem tailTrace_2680203 : CollatzResearch.WordTrace tailWord_2680203 prefixEnd_2680203 917488260414988284757651 := by
  unfold tailWord_2680203
  simp only [CollatzResearch.WordTrace]
  refine ⟨97755034309089748074789263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65170022872726498716526175 97755034309089748074789263)
  ·
    refine ⟨146632551463634622112183895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97755034309089748074789263 146632551463634622112183895)
    ·
      refine ⟨219948827195451933168275843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146632551463634622112183895 219948827195451933168275843)
      ·
        refine ⟨329923240793177899752413765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219948827195451933168275843 329923240793177899752413765)
        ·
          refine ⟨61860607648720856203577581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329923240793177899752413765 61860607648720856203577581)
          ·
            refine ⟨23197727868270321076341593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61860607648720856203577581 23197727868270321076341593)
            ·
              refine ⟨17398295901202740807256195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23197727868270321076341593 17398295901202740807256195)
              ·
                refine ⟨26097443851804111210884293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17398295901202740807256195 26097443851804111210884293)
                ·
                  refine ⟨4893270722213270852040805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26097443851804111210884293 4893270722213270852040805)
                  ·
                    refine ⟨917488260414988284757651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4893270722213270852040805 917488260414988284757651)
                    ·
                      rfl

theorem cell22_2680203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_2680203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680203 prefixEnd_2680203 := by exact prefixLift 2680203
  have htrace : WordTrace (prefixWord ++ tailWord_2680203) baseStart_2680203 baseEnd_2680203 := by
    simpa [prefixWord, tailWord_2680203, baseEnd_2680203] using wordTrace_append hprefix tailTrace_2680203
  have hstable : (prefixWord ++ tailWord_2680203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680203).length < 2 ^ (prefixWord ++ tailWord_2680203).sum := by decide
  have hdescent : baseEnd_2680203 < baseStart_2680203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680218 : List Nat := [3, 1, 1, 4, 1, 1, 2, 9]
def baseStart_2680218 : Nat := 118140960795 + 2680218 * 2 ^ 59
def prefixEnd_2680218 : Nat := 4983230072969 + 3 ^ 40 * 2680218 * 2
def baseEnd_2680218 : Nat := 101943710580170360625845

theorem tailTrace_2680218 : CollatzResearch.WordTrace tailWord_2680218 prefixEnd_2680218 101943710580170360625845 := by
  unfold tailWord_2680218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24438895351008851409146327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65170387602690270424390205 24438895351008851409146327)
  ·
    refine ⟨36658343026513277113719491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24438895351008851409146327 36658343026513277113719491)
    ·
      refine ⟨54987514539769915670579237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36658343026513277113719491 54987514539769915670579237)
      ·
        refine ⟨10310158976206859188233607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54987514539769915670579237 10310158976206859188233607)
        ·
          refine ⟨15465238464310288782350411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310158976206859188233607 15465238464310288782350411)
          ·
            refine ⟨23197857696465433173525617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15465238464310288782350411 23197857696465433173525617)
            ·
              refine ⟨17398393272349074880144213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23197857696465433173525617 17398393272349074880144213)
              ·
                refine ⟨101943710580170360625845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17398393272349074880144213 101943710580170360625845)
                ·
                  rfl

theorem cell22_2680218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_2680218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680218 prefixEnd_2680218 := by exact prefixLift 2680218
  have htrace : WordTrace (prefixWord ++ tailWord_2680218) baseStart_2680218 baseEnd_2680218 := by
    simpa [prefixWord, tailWord_2680218, baseEnd_2680218] using wordTrace_append hprefix tailTrace_2680218
  have hstable : (prefixWord ++ tailWord_2680218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680218).length < 2 ^ (prefixWord ++ tailWord_2680218).sum := by decide
  have hdescent : baseEnd_2680218 < baseStart_2680218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680252 : List Nat := [2, 2, 2, 4, 3, 1, 8]
def baseStart_2680252 : Nat := 118140960795 + 2680252 * 2 ^ 59
def prefixEnd_2680252 : Nat := 4983230072969 + 3 ^ 40 * 2680252 * 2
def baseEnd_2680252 : Nat := 33981667930235870010463

theorem tailTrace_2680252 : CollatzResearch.WordTrace tailWord_2680252 prefixEnd_2680252 33981667930235870010463 := by
  unfold tailWord_2680252
  simp only [CollatzResearch.WordTrace]
  refine ⟨48878410742956114721661505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65171214323941486295548673 48878410742956114721661505)
  ·
    refine ⟨36658808057217086041246129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48878410742956114721661505 36658808057217086041246129)
    ·
      refine ⟨27494106042912814530934597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36658808057217086041246129 27494106042912814530934597)
      ·
        refine ⟨5155144883046152724550237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27494106042912814530934597 5155144883046152724550237)
        ·
          refine ⟨1933179331142307271706339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5155144883046152724550237 1933179331142307271706339)
          ·
            refine ⟨2899768996713460907559509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933179331142307271706339 2899768996713460907559509)
            ·
              refine ⟨33981667930235870010463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2899768996713460907559509 33981667930235870010463)
              ·
                rfl

theorem cell22_2680252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 8].length) (baseStart_2680252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680252 prefixEnd_2680252 := by exact prefixLift 2680252
  have htrace : WordTrace (prefixWord ++ tailWord_2680252) baseStart_2680252 baseEnd_2680252 := by
    simpa [prefixWord, tailWord_2680252, baseEnd_2680252] using wordTrace_append hprefix tailTrace_2680252
  have hstable : (prefixWord ++ tailWord_2680252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680252).length < 2 ^ (prefixWord ++ tailWord_2680252).sum := by decide
  have hdescent : baseEnd_2680252 < baseStart_2680252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680258 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2680258 : Nat := 118140960795 + 2680258 * 2 ^ 59
def prefixEnd_2680258 : Nat := 4983230072969 + 3 ^ 40 * 2680258 * 2
def baseEnd_2680258 : Nat := 305835696012995491544161

theorem tailTrace_2680258 : CollatzResearch.WordTrace tailWord_2680258 prefixEnd_2680258 305835696012995491544161 := by
  unfold tailWord_2680258
  simp only [CollatzResearch.WordTrace]
  refine ⟨24439260080972623117010357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65171360215926994978694285 24439260080972623117010357)
  ·
    refine ⟨2291180632591183417219721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24439260080972623117010357 2291180632591183417219721)
    ·
      refine ⟨1718385474443387562914791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2291180632591183417219721 1718385474443387562914791)
      ·
        refine ⟨2577578211665081344372187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718385474443387562914791 2577578211665081344372187)
        ·
          refine ⟨3866367317497622016558281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577578211665081344372187 3866367317497622016558281)
          ·
            refine ⟨2899775488123216512418711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866367317497622016558281 2899775488123216512418711)
            ·
              refine ⟨4349663232184824768628067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899775488123216512418711 4349663232184824768628067)
              ·
                refine ⟨6524494848277237152942101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349663232184824768628067 6524494848277237152942101)
                ·
                  refine ⟨305835696012995491544161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6524494848277237152942101 305835696012995491544161)
                  ·
                    rfl

theorem cell22_2680258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2680258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680258 prefixEnd_2680258 := by exact prefixLift 2680258
  have htrace : WordTrace (prefixWord ++ tailWord_2680258) baseStart_2680258 baseEnd_2680258 := by
    simpa [prefixWord, tailWord_2680258, baseEnd_2680258] using wordTrace_append hprefix tailTrace_2680258
  have hstable : (prefixWord ++ tailWord_2680258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680258).length < 2 ^ (prefixWord ++ tailWord_2680258).sum := by decide
  have hdescent : baseEnd_2680258 < baseStart_2680258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680263 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 7]
def baseStart_2680263 : Nat := 118140960795 + 2680263 * 2 ^ 59
def prefixEnd_2680263 : Nat := 4983230072969 + 3 ^ 40 * 2680263 * 2
def baseEnd_2680263 : Nat := 305836266547056042752489

theorem tailTrace_2680263 : CollatzResearch.WordTrace tailWord_2680263 prefixEnd_2680263 305836266547056042752489 := by
  unfold tailWord_2680263
  simp only [CollatzResearch.WordTrace]
  refine ⟨97757222688872378321973443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65171481792581585547982295 97757222688872378321973443)
  ·
    refine ⟨146635834033308567482960165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97757222688872378321973443 146635834033308567482960165)
    ·
      refine ⟨27494218881245356403055031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146635834033308567482960165 27494218881245356403055031)
      ·
        refine ⟨41241328321868034604582547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27494218881245356403055031 41241328321868034604582547)
        ·
          refine ⟨61861992482802051906873821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41241328321868034604582547 61861992482802051906873821)
          ·
            refine ⟨23198247181050769465077683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61861992482802051906873821 23198247181050769465077683)
            ·
              refine ⟨34797370771576154197616525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23198247181050769465077683 34797370771576154197616525)
              ·
                refine ⟨13049014039341057824106197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34797370771576154197616525 13049014039341057824106197)
                ·
                  refine ⟨305836266547056042752489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13049014039341057824106197 305836266547056042752489)
                  ·
                    rfl

theorem cell22_2680263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_2680263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680263 prefixEnd_2680263 := by exact prefixLift 2680263
  have htrace : WordTrace (prefixWord ++ tailWord_2680263) baseStart_2680263 baseEnd_2680263 := by
    simpa [prefixWord, tailWord_2680263, baseEnd_2680263] using wordTrace_append hprefix tailTrace_2680263
  have hstable : (prefixWord ++ tailWord_2680263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680263).length < 2 ^ (prefixWord ++ tailWord_2680263).sum := by decide
  have hdescent : baseEnd_2680263 < baseStart_2680263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680267 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 1, 3]
def baseStart_2680267 : Nat := 118140960795 + 2680267 * 2 ^ 59
def prefixEnd_2680267 : Nat := 4983230072969 + 3 ^ 40 * 2680267 * 2
def baseEnd_2680267 : Nat := 917510168922913451157455

theorem tailTrace_2680267 : CollatzResearch.WordTrace tailWord_2680267 prefixEnd_2680267 917510168922913451157455 := by
  unfold tailWord_2680267
  simp only [CollatzResearch.WordTrace]
  refine ⟨97757368580857887005119055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65171579053905258003412703 97757368580857887005119055)
  ·
    refine ⟨146636052871286830507678583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97757368580857887005119055 146636052871286830507678583)
    ·
      refine ⟨219954079306930245761517875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146636052871286830507678583 219954079306930245761517875)
      ·
        refine ⟨329931118960395368642276813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219954079306930245761517875 329931118960395368642276813)
        ·
          refine ⟨123724169610148263240853805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329931118960395368642276813 123724169610148263240853805)
          ·
            refine ⟨46396563603805598715320177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123724169610148263240853805 46396563603805598715320177)
            ·
              refine ⟨34797422702854199036490133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46396563603805598715320177 34797422702854199036490133)
              ·
                refine ⟨1631129189196290579835475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34797422702854199036490133 1631129189196290579835475)
                ·
                  refine ⟨2446693783794435869753213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631129189196290579835475 2446693783794435869753213)
                  ·
                    refine ⟨917510168922913451157455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446693783794435869753213 917510168922913451157455)
                    ·
                      rfl

theorem cell22_2680267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 3].length) (baseStart_2680267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680267 prefixEnd_2680267 := by exact prefixLift 2680267
  have htrace : WordTrace (prefixWord ++ tailWord_2680267) baseStart_2680267 baseEnd_2680267 := by
    simpa [prefixWord, tailWord_2680267, baseEnd_2680267] using wordTrace_append hprefix tailTrace_2680267
  have hstable : (prefixWord ++ tailWord_2680267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680267).length < 2 ^ (prefixWord ++ tailWord_2680267).sum := by decide
  have hdescent : baseEnd_2680267 < baseStart_2680267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680318 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2680318 : Nat := 118140960795 + 2680318 * 2 ^ 59
def prefixEnd_2680318 : Nat := 4983230072969 + 3 ^ 40 * 2680318 * 2
def baseEnd_2680318 : Nat := 917527627265166318132299

theorem tailTrace_2680318 : CollatzResearch.WordTrace tailWord_2680318 prefixEnd_2680318 917527627265166318132299 := by
  unfold tailWord_2680318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12219903587959140339403201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65172819135782081810150405 12219903587959140339403201)
  ·
    refine ⟨9164927690969355254552401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12219903587959140339403201 9164927690969355254552401)
    ·
      refine ⟨6873695768227016440914301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9164927690969355254552401 6873695768227016440914301)
      ·
        refine ⟨2577635913085131165342863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6873695768227016440914301 2577635913085131165342863)
        ·
          refine ⟨3866453869627696748014295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577635913085131165342863 3866453869627696748014295)
          ·
            refine ⟨5799680804441545122021443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866453869627696748014295 5799680804441545122021443)
            ·
              refine ⟨8699521206662317683032165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5799680804441545122021443 8699521206662317683032165)
              ·
                refine ⟨1631160226249184565568531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8699521206662317683032165 1631160226249184565568531)
                ·
                  refine ⟨2446740339373776848352797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631160226249184565568531 2446740339373776848352797)
                  ·
                    refine ⟨917527627265166318132299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446740339373776848352797 917527627265166318132299)
                    ·
                      rfl

theorem cell22_2680318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2680318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680318 prefixEnd_2680318 := by exact prefixLift 2680318
  have htrace : WordTrace (prefixWord ++ tailWord_2680318) baseStart_2680318 baseEnd_2680318 := by
    simpa [prefixWord, tailWord_2680318, baseEnd_2680318] using wordTrace_append hprefix tailTrace_2680318
  have hstable : (prefixWord ++ tailWord_2680318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680318).length < 2 ^ (prefixWord ++ tailWord_2680318).sum := by decide
  have hdescent : baseEnd_2680318 < baseStart_2680318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680391 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 2, 3]
def baseStart_2680391 : Nat := 118140960795 + 2680391 * 2 ^ 59
def prefixEnd_2680391 : Nat := 4983230072969 + 3 ^ 40 * 2680391 * 2
def baseEnd_2680391 : Nat := 917552616657018461057075

theorem tailTrace_2680391 : CollatzResearch.WordTrace tailWord_2680391 prefixEnd_2680391 917552616657018461057075 := by
  unfold tailWord_2680391
  simp only [CollatzResearch.WordTrace]
  refine ⟨97761891232408656182633027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65174594154939104121755351 97761891232408656182633027)
  ·
    refine ⟨146642836848612984273949541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97761891232408656182633027 146642836848612984273949541)
    ·
      refine ⟨27495531909114934551365539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146642836848612984273949541 27495531909114934551365539)
      ·
        refine ⟨41243297863672401827048309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27495531909114934551365539 41243297863672401827048309)
        ·
          refine ⟨3866559174719287671285779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41243297863672401827048309 3866559174719287671285779)
          ·
            refine ⟨5799838762078931506928669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866559174719287671285779 5799838762078931506928669)
            ·
              refine ⟨2174939535779599315098251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5799838762078931506928669 2174939535779599315098251)
              ·
                refine ⟨3262409303669398972647377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174939535779599315098251 3262409303669398972647377)
                ·
                  refine ⟨2446806977752049229485533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262409303669398972647377 2446806977752049229485533)
                  ·
                    refine ⟨917552616657018461057075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446806977752049229485533 917552616657018461057075)
                    ·
                      rfl

theorem cell22_2680391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_2680391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680391 prefixEnd_2680391 := by exact prefixLift 2680391
  have htrace : WordTrace (prefixWord ++ tailWord_2680391) baseStart_2680391 baseEnd_2680391 := by
    simpa [prefixWord, tailWord_2680391, baseEnd_2680391] using wordTrace_append hprefix tailTrace_2680391
  have hstable : (prefixWord ++ tailWord_2680391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680391).length < 2 ^ (prefixWord ++ tailWord_2680391).sum := by decide
  have hdescent : baseEnd_2680391 < baseStart_2680391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680449 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 5]
def baseStart_2680449 : Nat := 118140960795 + 2680449 * 2 ^ 59
def prefixEnd_2680449 : Nat := 4983230072969 + 3 ^ 40 * 2680449 * 2
def baseEnd_2680449 : Nat := 305857490414108547702299

theorem tailTrace_2680449 : CollatzResearch.WordTrace tailWord_2680449 prefixEnd_2680449 305857490414108547702299 := by
  unfold tailWord_2680449
  simp only [CollatzResearch.WordTrace]
  refine ⟨97764006666198532088244401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65176004444132354725496267 97764006666198532088244401)
  ·
    refine ⟨73323004999648899066183301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97764006666198532088244401 73323004999648899066183301)
    ·
      refine ⟨13748063437434168574909369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73323004999648899066183301 13748063437434168574909369)
      ·
        refine ⟨10311047578075626431182027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13748063437434168574909369 10311047578075626431182027)
        ·
          refine ⟨15466571367113439646773041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10311047578075626431182027 15466571367113439646773041)
          ·
            refine ⟨11599928525335079735079781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15466571367113439646773041 11599928525335079735079781)
            ·
              refine ⟨2174986598500327450327459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11599928525335079735079781 2174986598500327450327459)
              ·
                refine ⟨3262479897750491175491189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174986598500327450327459 3262479897750491175491189)
                ·
                  refine ⟨305857490414108547702299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3262479897750491175491189 305857490414108547702299)
                  ·
                    rfl

theorem cell22_2680449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_2680449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680449 prefixEnd_2680449 := by exact prefixLift 2680449
  have htrace : WordTrace (prefixWord ++ tailWord_2680449) baseStart_2680449 baseEnd_2680449 := by
    simpa [prefixWord, tailWord_2680449, baseEnd_2680449] using wordTrace_append hprefix tailTrace_2680449
  have hstable : (prefixWord ++ tailWord_2680449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680449).length < 2 ^ (prefixWord ++ tailWord_2680449).sum := by decide
  have hdescent : baseEnd_2680449 < baseStart_2680449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680460 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_2680460 : Nat := 118140960795 + 2680460 * 2 ^ 59
def prefixEnd_2680460 : Nat := 4983230072969 + 3 ^ 40 * 2680460 * 2
def baseEnd_2680460 : Nat := 305858745589041760360621

theorem tailTrace_2680460 : CollatzResearch.WordTrace tailWord_2680460 prefixEnd_2680460 305858745589041760360621 := by
  unfold tailWord_2680460
  simp only [CollatzResearch.WordTrace]
  refine ⟨48882203934579340483447417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65176271912772453977929889 48882203934579340483447417)
  ·
    refine ⟨36661652950934505362585563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48882203934579340483447417 36661652950934505362585563)
    ·
      refine ⟨54992479426401758043878345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36661652950934505362585563 54992479426401758043878345)
      ·
        refine ⟨41244359569801318532908759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54992479426401758043878345 41244359569801318532908759)
        ·
          refine ⟨61866539354701977799363139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41244359569801318532908759 61866539354701977799363139)
          ·
            refine ⟨92799809032052966699044709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61866539354701977799363139 92799809032052966699044709)
            ·
              refine ⟨17399964193509931256070883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92799809032052966699044709 17399964193509931256070883)
              ·
                refine ⟨26099946290264896884106325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17399964193509931256070883 26099946290264896884106325)
                ·
                  refine ⟨305858745589041760360621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26099946290264896884106325 305858745589041760360621)
                  ·
                    rfl

theorem cell22_2680460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_2680460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680460 prefixEnd_2680460 := by exact prefixLift 2680460
  have htrace : WordTrace (prefixWord ++ tailWord_2680460) baseStart_2680460 baseEnd_2680460 := by
    simpa [prefixWord, tailWord_2680460, baseEnd_2680460] using wordTrace_append hprefix tailTrace_2680460
  have hstable : (prefixWord ++ tailWord_2680460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680460).length < 2 ^ (prefixWord ++ tailWord_2680460).sum := by decide
  have hdescent : baseEnd_2680460 < baseStart_2680460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680509 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2680509 : Nat := 118140960795 + 2680509 * 2 ^ 59
def prefixEnd_2680509 : Nat := 4983230072969 + 3 ^ 40 * 2680509 * 2
def baseEnd_2680509 : Nat := 917593010468505486606713

theorem tailTrace_2680509 : CollatzResearch.WordTrace tailWord_2680509 prefixEnd_2680509 917593010468505486606713 := by
  unfold tailWord_2680509
  simp only [CollatzResearch.WordTrace]
  refine ⟨97766195045981162335428581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65177463363987441556952387 97766195045981162335428581)
  ·
    refine ⟨18331161571121467937892859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97766195045981162335428581 18331161571121467937892859)
    ·
      refine ⟨27496742356682201906839289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18331161571121467937892859 27496742356682201906839289)
      ·
        refine ⟨20622556767511651430129467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27496742356682201906839289 20622556767511651430129467)
        ·
          refine ⟨30933835151267477145194201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20622556767511651430129467 30933835151267477145194201)
          ·
            refine ⟨23200376363450607858895651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30933835151267477145194201 23200376363450607858895651)
            ·
              refine ⟨34800564545175911788343477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23200376363450607858895651 34800564545175911788343477)
              ·
                refine ⟨3262552926110241730157201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34800564545175911788343477 3262552926110241730157201)
                ·
                  refine ⟨2446914694582681297617901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262552926110241730157201 2446914694582681297617901)
                  ·
                    refine ⟨917593010468505486606713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446914694582681297617901 917593010468505486606713)
                    ·
                      rfl

theorem cell22_2680509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2680509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680509 prefixEnd_2680509 := by exact prefixLift 2680509
  have htrace : WordTrace (prefixWord ++ tailWord_2680509) baseStart_2680509 baseEnd_2680509 := by
    simpa [prefixWord, tailWord_2680509, baseEnd_2680509] using wordTrace_append hprefix tailTrace_2680509
  have hstable : (prefixWord ++ tailWord_2680509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680509).length < 2 ^ (prefixWord ++ tailWord_2680509).sum := by decide
  have hdescent : baseEnd_2680509 < baseStart_2680509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680524 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_2680524 : Nat := 118140960795 + 2680524 * 2 ^ 59
def prefixEnd_2680524 : Nat := 4983230072969 + 3 ^ 40 * 2680524 * 2
def baseEnd_2680524 : Nat := 917598145275050447481667

theorem tailTrace_2680524 : CollatzResearch.WordTrace tailWord_2680524 prefixEnd_2680524 917598145275050447481667 := by
  unfold tailWord_2680524
  simp only [CollatzResearch.WordTrace]
  refine ⟨48883371070463409948612313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65177828093951213264816417 48883371070463409948612313)
  ·
    refine ⟨36662528302847557461459235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48883371070463409948612313 36662528302847557461459235)
    ·
      refine ⟨54993792454271336192188853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36662528302847557461459235 54993792454271336192188853)
      ·
        refine ⟨5155668042587937768017705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54993792454271336192188853 5155668042587937768017705)
        ·
          refine ⟨3866751031940953326013279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5155668042587937768017705 3866751031940953326013279)
          ·
            refine ⟨5800126547911429989019919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866751031940953326013279 5800126547911429989019919)
            ·
              refine ⟨8700189821867144983529879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800126547911429989019919 8700189821867144983529879)
              ·
                refine ⟨13050284732800717475294819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700189821867144983529879 13050284732800717475294819)
                ·
                  refine ⟨19575427099201076212942229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13050284732800717475294819 19575427099201076212942229)
                  ·
                    refine ⟨917598145275050447481667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19575427099201076212942229 917598145275050447481667)
                    ·
                      rfl

theorem cell22_2680524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_2680524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680524 prefixEnd_2680524 := by exact prefixLift 2680524
  have htrace : WordTrace (prefixWord ++ tailWord_2680524) baseStart_2680524 baseEnd_2680524 := by
    simpa [prefixWord, tailWord_2680524, baseEnd_2680524] using wordTrace_append hprefix tailTrace_2680524
  have hstable : (prefixWord ++ tailWord_2680524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680524).length < 2 ^ (prefixWord ++ tailWord_2680524).sum := by decide
  have hdescent : baseEnd_2680524 < baseStart_2680524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680554 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2680554 : Nat := 118140960795 + 2680554 * 2 ^ 59
def prefixEnd_2680554 : Nat := 4983230072969 + 3 ^ 40 * 2680554 * 2
def baseEnd_2680554 : Nat := 917608414888140369231575

theorem tailTrace_2680554 : CollatzResearch.WordTrace tailWord_2680554 prefixEnd_2680554 917608414888140369231575 := by
  unfold tailWord_2680554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441959082704533755204179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65178557553878756680544477 24441959082704533755204179)
  ·
    refine ⟨36662938624056800632806269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24441959082704533755204179 36662938624056800632806269)
    ·
      refine ⟨13748601984021300237302351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36662938624056800632806269 13748601984021300237302351)
      ·
        refine ⟨20622902976031950355953527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13748601984021300237302351 20622902976031950355953527)
        ·
          refine ⟨30934354464047925533930291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20622902976031950355953527 30934354464047925533930291)
          ·
            refine ⟨46401531696071888300895437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30934354464047925533930291 46401531696071888300895437)
            ·
              refine ⟨17400574386026958112835789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46401531696071888300895437 17400574386026958112835789)
              ·
                refine ⟨6525215394760109292313421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17400574386026958112835789 6525215394760109292313421)
                ·
                  refine ⟨2446955773035040984617533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6525215394760109292313421 2446955773035040984617533)
                  ·
                    refine ⟨917608414888140369231575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446955773035040984617533 917608414888140369231575)
                    ·
                      rfl

theorem cell22_2680554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2680554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680554 prefixEnd_2680554 := by exact prefixLift 2680554
  have htrace : WordTrace (prefixWord ++ tailWord_2680554) baseStart_2680554 baseEnd_2680554 := by
    simpa [prefixWord, tailWord_2680554, baseEnd_2680554] using wordTrace_append hprefix tailTrace_2680554
  have hstable : (prefixWord ++ tailWord_2680554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680554).length < 2 ^ (prefixWord ++ tailWord_2680554).sum := by decide
  have hdescent : baseEnd_2680554 < baseStart_2680554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680567 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 5]
def baseStart_2680567 : Nat := 118140960795 + 2680567 * 2 ^ 59
def prefixEnd_2680567 : Nat := 4983230072969 + 3 ^ 40 * 2680567 * 2
def baseEnd_2680567 : Nat := 305870955017937556218845

theorem tailTrace_2680567 : CollatzResearch.WordTrace tailWord_2680567 prefixEnd_2680567 305870955017937556218845 := by
  unfold tailWord_2680567
  simp only [CollatzResearch.WordTrace]
  refine ⟨97768310479771038241039955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65178873653180692160693303 97768310479771038241039955)
  ·
    refine ⟨146652465719656557361559933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97768310479771038241039955 146652465719656557361559933)
    ·
      refine ⟨54994674644871209010584975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146652465719656557361559933 54994674644871209010584975)
      ·
        refine ⟨82492011967306813515877463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54994674644871209010584975 82492011967306813515877463)
        ·
          refine ⟨123738017950960220273816195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82492011967306813515877463 123738017950960220273816195)
          ·
            refine ⟨185607026926440330410724293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123738017950960220273816195 185607026926440330410724293)
            ·
              refine ⟨34801317548707561952010805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185607026926440330410724293 34801317548707561952010805)
              ·
                refine ⟨3262623520191333933001013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34801317548707561952010805 3262623520191333933001013)
                ·
                  refine ⟨305870955017937556218845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3262623520191333933001013 305870955017937556218845)
                  ·
                    rfl

theorem cell22_2680567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 5].length) (baseStart_2680567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680567 prefixEnd_2680567 := by exact prefixLift 2680567
  have htrace : WordTrace (prefixWord ++ tailWord_2680567) baseStart_2680567 baseEnd_2680567 := by
    simpa [prefixWord, tailWord_2680567, baseEnd_2680567] using wordTrace_append hprefix tailTrace_2680567
  have hstable : (prefixWord ++ tailWord_2680567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680567).length < 2 ^ (prefixWord ++ tailWord_2680567).sum := by decide
  have hdescent : baseEnd_2680567 < baseStart_2680567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680657 : List Nat := [1, 2, 2, 1, 5, 11]
def baseStart_2680657 : Nat := 118140960795 + 2680657 * 2 ^ 59
def prefixEnd_2680657 : Nat := 4983230072969 + 3 ^ 40 * 2680657 * 2
def baseEnd_2680657 : Nat := 11328934245593610295139

theorem tailTrace_2680657 : CollatzResearch.WordTrace tailWord_2680657 prefixEnd_2680657 11328934245593610295139 := by
  unfold tailWord_2680657
  simp only [CollatzResearch.WordTrace]
  refine ⟨97771593049444983611816225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65181062032963322407877483 97771593049444983611816225)
  ·
    refine ⟨73328694787083737708862169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97771593049444983611816225 73328694787083737708862169)
    ·
      refine ⟨54996521090312803281646627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73328694787083737708862169 54996521090312803281646627)
      ·
        refine ⟨82494781635469204922469941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54996521090312803281646627 82494781635469204922469941)
        ·
          refine ⟨7733885778325237961481557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82494781635469204922469941 7733885778325237961481557)
          ·
            refine ⟨11328934245593610295139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7733885778325237961481557 11328934245593610295139)
            ·
              rfl

theorem cell22_2680657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 11].length) (baseStart_2680657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680657 prefixEnd_2680657 := by exact prefixLift 2680657
  have htrace : WordTrace (prefixWord ++ tailWord_2680657) baseStart_2680657 baseEnd_2680657 := by
    simpa [prefixWord, tailWord_2680657, baseEnd_2680657] using wordTrace_append hprefix tailTrace_2680657
  have hstable : (prefixWord ++ tailWord_2680657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680657).length < 2 ^ (prefixWord ++ tailWord_2680657).sum := by decide
  have hdescent : baseEnd_2680657 < baseStart_2680657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680661 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2680661 : Nat := 118140960795 + 2680661 * 2 ^ 59
def prefixEnd_2680661 : Nat := 4983230072969 + 3 ^ 40 * 2680661 * 2
def baseEnd_2680661 : Nat := 917645043174827756806247

theorem tailTrace_2680661 : CollatzResearch.WordTrace tailWord_2680661 prefixEnd_2680661 917645043174827756806247 := by
  unfold tailWord_2680661
  simp only [CollatzResearch.WordTrace]
  refine ⟨97771738941430492294961837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65181159294286994863307891 97771738941430492294961837)
  ·
    refine ⟨36664402103036434610610689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97771738941430492294961837 36664402103036434610610689)
    ·
      refine ⟨27498301577277325957958017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36664402103036434610610689 27498301577277325957958017)
      ·
        refine ⟨20623726182957994468468513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27498301577277325957958017 20623726182957994468468513)
        ·
          refine ⟨15467794637218495851351385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20623726182957994468468513 15467794637218495851351385)
          ·
            refine ⟨11600845977913871888513539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15467794637218495851351385 11600845977913871888513539)
            ·
              refine ⟨17401268966870807832770309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11600845977913871888513539 17401268966870807832770309)
              ·
                refine ⟨3262737931288276468644433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17401268966870807832770309 3262737931288276468644433)
                ·
                  refine ⟨2447053448466207351483325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262737931288276468644433 2447053448466207351483325)
                  ·
                    refine ⟨917645043174827756806247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447053448466207351483325 917645043174827756806247)
                    ·
                      rfl

theorem cell22_2680661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2680661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680661 prefixEnd_2680661 := by exact prefixLift 2680661
  have htrace : WordTrace (prefixWord ++ tailWord_2680661) baseStart_2680661 baseEnd_2680661 := by
    simpa [prefixWord, tailWord_2680661, baseEnd_2680661] using wordTrace_append hprefix tailTrace_2680661
  have hstable : (prefixWord ++ tailWord_2680661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680661).length < 2 ^ (prefixWord ++ tailWord_2680661).sum := by decide
  have hdescent : baseEnd_2680661 < baseStart_2680661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680830 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2680830 : Nat := 118140960795 + 2680830 * 2 ^ 59
def prefixEnd_2680830 : Nat := 4983230072969 + 3 ^ 40 * 2680830 * 2
def baseEnd_2680830 : Nat := 917702895328567649330729

theorem tailTrace_2680830 : CollatzResearch.WordTrace tailWord_2680830 prefixEnd_2680830 917702895328567649330729 := by
  unfold tailWord_2680830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222237859727279269732993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65185268585212156105242629 12222237859727279269732993)
  ·
    refine ⟨9166678394795459452299745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12222237859727279269732993 9166678394795459452299745)
    ·
      refine ⟨6875008796096594589224809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9166678394795459452299745 6875008796096594589224809)
      ·
        refine ⟨5156256597072445941918607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6875008796096594589224809 5156256597072445941918607)
        ·
          refine ⟨7734384895608668912877911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156256597072445941918607 7734384895608668912877911)
          ·
            refine ⟨11601577343413003369316867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734384895608668912877911 11601577343413003369316867)
            ·
              refine ⟨17402366015119505053975301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11601577343413003369316867 17402366015119505053975301)
              ·
                refine ⟨3262943627834907197620369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17402366015119505053975301 3262943627834907197620369)
                ·
                  refine ⟨2447207720876180398215277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262943627834907197620369 2447207720876180398215277)
                  ·
                    refine ⟨917702895328567649330729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447207720876180398215277 917702895328567649330729)
                    ·
                      rfl

theorem cell22_2680830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2680830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680830 prefixEnd_2680830 := by exact prefixLift 2680830
  have htrace : WordTrace (prefixWord ++ tailWord_2680830) baseStart_2680830 baseEnd_2680830 := by
    simpa [prefixWord, tailWord_2680830, baseEnd_2680830] using wordTrace_append hprefix tailTrace_2680830
  have hstable : (prefixWord ++ tailWord_2680830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680830).length < 2 ^ (prefixWord ++ tailWord_2680830).sum := by decide
  have hdescent : baseEnd_2680830 < baseStart_2680830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680858 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_2680858 : Nat := 118140960795 + 2680858 * 2 ^ 59
def prefixEnd_2680858 : Nat := 4983230072969 + 3 ^ 40 * 2680858 * 2
def baseEnd_2680858 : Nat := 917712480300784909630643

theorem tailTrace_2680858 : CollatzResearch.WordTrace tailWord_2680858 prefixEnd_2680858 917712480300784909630643 := by
  unfold tailWord_2680858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444731030429198734970807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65185949414477863293255485 24444731030429198734970807)
  ·
    refine ⟨36667096545643798102456211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24444731030429198734970807 36667096545643798102456211)
    ·
      refine ⟨55000644818465697153684317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36667096545643798102456211 55000644818465697153684317)
      ·
        refine ⟨20625241806924636432631619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55000644818465697153684317 20625241806924636432631619)
        ·
          refine ⟨30937862710386954648947429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20625241806924636432631619 30937862710386954648947429)
          ·
            refine ⟨5800849258197553996677643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30937862710386954648947429 5800849258197553996677643)
            ·
              refine ⟨8701273887296330995016465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800849258197553996677643 8701273887296330995016465)
              ·
                refine ⟨6525955415472248246262349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8701273887296330995016465 6525955415472248246262349)
                ·
                  refine ⟨2447233280802093092348381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6525955415472248246262349 2447233280802093092348381)
                  ·
                    refine ⟨917712480300784909630643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447233280802093092348381 917712480300784909630643)
                    ·
                      rfl

theorem cell22_2680858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_2680858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680858 prefixEnd_2680858 := by exact prefixLift 2680858
  have htrace : WordTrace (prefixWord ++ tailWord_2680858) baseStart_2680858 baseEnd_2680858 := by
    simpa [prefixWord, tailWord_2680858, baseEnd_2680858] using wordTrace_append hprefix tailTrace_2680858
  have hstable : (prefixWord ++ tailWord_2680858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680858).length < 2 ^ (prefixWord ++ tailWord_2680858).sum := by decide
  have hdescent : baseEnd_2680858 < baseStart_2680858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680931 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 1, 5]
def baseStart_2680931 : Nat := 118140960795 + 2680931 * 2 ^ 59
def prefixEnd_2680931 : Nat := 4983230072969 + 3 ^ 40 * 2680931 * 2
def baseEnd_2680931 : Nat := 917737469692637052555419

theorem tailTrace_2680931 : CollatzResearch.WordTrace tailWord_2680931 prefixEnd_2680931 917737469692637052555419 := by
  unfold tailWord_2680931
  simp only [CollatzResearch.WordTrace]
  refine ⟨97781586650452328407290647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65187724433634885604860431 97781586650452328407290647)
  ·
    refine ⟨146672379975678492610935971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97781586650452328407290647 146672379975678492610935971)
    ·
      refine ⟨220008569963517738916403957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146672379975678492610935971 220008569963517738916403957)
      ·
        refine ⟨20625803434079788023412871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220008569963517738916403957 20625803434079788023412871)
        ·
          refine ⟨30938705151119682035119307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20625803434079788023412871 30938705151119682035119307)
          ·
            refine ⟨46408057726679523052678961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30938705151119682035119307 46408057726679523052678961)
            ·
              refine ⟨34806043295009642289509221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46408057726679523052678961 34806043295009642289509221)
              ·
                refine ⟨6526133117814307929282979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34806043295009642289509221 6526133117814307929282979)
                ·
                  refine ⟨9789199676721461893924469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526133117814307929282979 9789199676721461893924469)
                  ·
                    refine ⟨917737469692637052555419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9789199676721461893924469 917737469692637052555419)
                    ·
                      rfl

theorem cell22_2680931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_2680931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680931 prefixEnd_2680931 := by exact prefixLift 2680931
  have htrace : WordTrace (prefixWord ++ tailWord_2680931) baseStart_2680931 baseEnd_2680931 := by
    simpa [prefixWord, tailWord_2680931, baseEnd_2680931] using wordTrace_append hprefix tailTrace_2680931
  have hstable : (prefixWord ++ tailWord_2680931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680931).length < 2 ^ (prefixWord ++ tailWord_2680931).sum := by decide
  have hdescent : baseEnd_2680931 < baseStart_2680931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680950 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2680950 : Nat := 118140960795 + 2680950 * 2 ^ 59
def prefixEnd_2680950 : Nat := 4983230072969 + 3 ^ 40 * 2680950 * 2
def baseEnd_2680950 : Nat := 305914657926975778776787

theorem tailTrace_2680950 : CollatzResearch.WordTrace tailWord_2680950 prefixEnd_2680950 305914657926975778776787 := by
  unfold tailWord_2680950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6111392477336468415764519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65188186424922329768154869 6111392477336468415764519)
  ·
    refine ⟨9167088716004702623646779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6111392477336468415764519 9167088716004702623646779)
    ·
      refine ⟨13750633074007053935470169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9167088716004702623646779 13750633074007053935470169)
      ·
        refine ⟨10312974805505290451602627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13750633074007053935470169 10312974805505290451602627)
        ·
          refine ⟨15469462208257935677403941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10312974805505290451602627 15469462208257935677403941)
          ·
            refine ⟨2900524164048362939513239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15469462208257935677403941 2900524164048362939513239)
            ·
              refine ⟨4350786246072544409269859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900524164048362939513239 4350786246072544409269859)
              ·
                refine ⟨6526179369108816613904789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350786246072544409269859 6526179369108816613904789)
                ·
                  refine ⟨305914657926975778776787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6526179369108816613904789 305914657926975778776787)
                  ·
                    rfl

theorem cell22_2680950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2680950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680950 prefixEnd_2680950 := by exact prefixLift 2680950
  have htrace : WordTrace (prefixWord ++ tailWord_2680950) baseStart_2680950 baseEnd_2680950 := by
    simpa [prefixWord, tailWord_2680950, baseEnd_2680950] using wordTrace_append hprefix tailTrace_2680950
  have hstable : (prefixWord ++ tailWord_2680950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680950).length < 2 ^ (prefixWord ++ tailWord_2680950).sum := by decide
  have hdescent : baseEnd_2680950 < baseStart_2680950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680965 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_2680965 : Nat := 118140960795 + 2680965 * 2 ^ 59
def prefixEnd_2680965 : Nat := 4983230072969 + 3 ^ 40 * 2680965 * 2
def baseEnd_2680965 : Nat := 917749108587472297205315

theorem tailTrace_2680965 : CollatzResearch.WordTrace tailWord_2680965 prefixEnd_2680965 917749108587472297205315 := by
  unfold tailWord_2680965
  simp only [CollatzResearch.WordTrace]
  refine ⟨97782826732329152214028349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65188551154886101476018899 97782826732329152214028349)
  ·
    refine ⟨36668560024623432080260631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97782826732329152214028349 36668560024623432080260631)
    ·
      refine ⟨55002840036935148120390947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36668560024623432080260631 55002840036935148120390947)
      ·
        refine ⟨82504260055402722180586421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55002840036935148120390947 82504260055402722180586421)
        ·
          refine ⟨7734774380194005204429977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82504260055402722180586421 7734774380194005204429977)
          ·
            refine ⟨5801080785145503903322483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7734774380194005204429977 5801080785145503903322483)
            ·
              refine ⟨8701621177718255854983725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801080785145503903322483 8701621177718255854983725)
              ·
                refine ⟨3263107941644345945618897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8701621177718255854983725 3263107941644345945618897)
                ·
                  refine ⟨2447330956233259459214173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263107941644345945618897 2447330956233259459214173)
                  ·
                    refine ⟨917749108587472297205315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447330956233259459214173 917749108587472297205315)
                    ·
                      rfl

theorem cell22_2680965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_2680965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2680965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2680965 prefixEnd_2680965 := by exact prefixLift 2680965
  have htrace : WordTrace (prefixWord ++ tailWord_2680965) baseStart_2680965 baseEnd_2680965 := by
    simpa [prefixWord, tailWord_2680965, baseEnd_2680965] using wordTrace_append hprefix tailTrace_2680965
  have hstable : (prefixWord ++ tailWord_2680965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680965).length < 2 ^ (prefixWord ++ tailWord_2680965).sum := by decide
  have hdescent : baseEnd_2680965 < baseStart_2680965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681068 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_2681068 : Nat := 118140960795 + 2681068 * 2 ^ 59
def prefixEnd_2681068 : Nat := 4983230072969 + 3 ^ 40 * 2681068 * 2
def baseEnd_2681068 : Nat := 305928122530804787293333

theorem tailTrace_2681068 : CollatzResearch.WordTrace tailWord_2681068 prefixEnd_2681068 305928122530804787293333 := by
  unfold tailWord_2681068
  simp only [CollatzResearch.WordTrace]
  refine ⟨48893291725478000402513929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65191055633970667203351905 48893291725478000402513929)
  ·
    refine ⟨36669968794108500301885447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48893291725478000402513929 36669968794108500301885447)
    ·
      refine ⟨55004953191162750452828171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36669968794108500301885447 55004953191162750452828171)
      ·
        refine ⟨82507429786744125679242257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55004953191162750452828171 82507429786744125679242257)
        ·
          refine ⟨61880572340058094259431693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82507429786744125679242257 61880572340058094259431693)
          ·
            refine ⟨23205214627521785347286885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61880572340058094259431693 23205214627521785347286885)
            ·
              refine ⟨4350977742660334752616291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23205214627521785347286885 4350977742660334752616291)
              ·
                refine ⟨6526466613990502128924437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350977742660334752616291 6526466613990502128924437)
                ·
                  refine ⟨305928122530804787293333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6526466613990502128924437 305928122530804787293333)
                  ·
                    rfl

theorem cell22_2681068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_2681068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681068 prefixEnd_2681068 := by exact prefixLift 2681068
  have htrace : WordTrace (prefixWord ++ tailWord_2681068) baseStart_2681068 baseEnd_2681068 := by
    simpa [prefixWord, tailWord_2681068, baseEnd_2681068] using wordTrace_append hprefix tailTrace_2681068
  have hstable : (prefixWord ++ tailWord_2681068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681068).length < 2 ^ (prefixWord ++ tailWord_2681068).sum := by decide
  have hdescent : baseEnd_2681068 < baseStart_2681068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681098 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2681098 : Nat := 118140960795 + 2681098 * 2 ^ 59
def prefixEnd_2681098 : Nat := 4983230072969 + 3 ^ 40 * 2681098 * 2
def baseEnd_2681098 : Nat := 917794637205504283629907

theorem tailTrace_2681098 : CollatzResearch.WordTrace tailWord_2681098 prefixEnd_2681098 917794637205504283629907 := by
  unfold tailWord_2681098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24446919410211828982154987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65191785093898210619079965 24446919410211828982154987)
  ·
    refine ⟨36670379115317743473232481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24446919410211828982154987 36670379115317743473232481)
    ·
      refine ⟨27502784336488307604924361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36670379115317743473232481 27502784336488307604924361)
      ·
        refine ⟨20627088252366230703693271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27502784336488307604924361 20627088252366230703693271)
        ·
          refine ⟨30940632378549346055539907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20627088252366230703693271 30940632378549346055539907)
          ·
            refine ⟨46410948567824019083309861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30940632378549346055539907 46410948567824019083309861)
            ·
              refine ⟨8702052856467003578120599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46410948567824019083309861 8702052856467003578120599)
              ·
                refine ⟨13053079284700505367180899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8702052856467003578120599 13053079284700505367180899)
                ·
                  refine ⟨19579618927050758050771349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13053079284700505367180899 19579618927050758050771349)
                  ·
                    refine ⟨917794637205504283629907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19579618927050758050771349 917794637205504283629907)
                    ·
                      rfl

theorem cell22_2681098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2681098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681098 prefixEnd_2681098 := by exact prefixLift 2681098
  have htrace : WordTrace (prefixWord ++ tailWord_2681098) baseStart_2681098 baseEnd_2681098 := by
    simpa [prefixWord, tailWord_2681098, baseEnd_2681098] using wordTrace_append hprefix tailTrace_2681098
  have hstable : (prefixWord ++ tailWord_2681098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681098).length < 2 ^ (prefixWord ++ tailWord_2681098).sum := by decide
  have hdescent : baseEnd_2681098 < baseStart_2681098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681175 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 5]
def baseStart_2681175 : Nat := 118140960795 + 2681175 * 2 ^ 59
def prefixEnd_2681175 : Nat := 4983230072969 + 3 ^ 40 * 2681175 * 2
def baseEnd_2681175 : Nat := 305940331959700583151557

theorem tailTrace_2681175 : CollatzResearch.WordTrace tailWord_2681175 prefixEnd_2681175 305940331959700583151557 := by
  unfold tailWord_2681175
  simp only [CollatzResearch.WordTrace]
  refine ⟨97790486061568358079172979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65193657374378905386115319 97790486061568358079172979)
  ·
    refine ⟨146685729092352537118759469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97790486061568358079172979 146685729092352537118759469)
    ·
      refine ⟨55007148409632201419534801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146685729092352537118759469 55007148409632201419534801)
      ·
        refine ⟨41255361307224151064651101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55007148409632201419534801 41255361307224151064651101)
        ·
          refine ⟨15470760490209056649244163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41255361307224151064651101 15470760490209056649244163)
          ·
            refine ⟨23206140735313584973866245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15470760490209056649244163 23206140735313584973866245)
            ·
              refine ⟨4351151387871297182599921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23206140735313584973866245 4351151387871297182599921)
              ·
                refine ⟨3263363540903472886949941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351151387871297182599921 3263363540903472886949941)
                ·
                  refine ⟨305940331959700583151557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3263363540903472886949941 305940331959700583151557)
                  ·
                    rfl

theorem cell22_2681175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 5].length) (baseStart_2681175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681175 prefixEnd_2681175 := by exact prefixLift 2681175
  have htrace : WordTrace (prefixWord ++ tailWord_2681175) baseStart_2681175 baseEnd_2681175 := by
    simpa [prefixWord, tailWord_2681175, baseEnd_2681175] using wordTrace_append hprefix tailTrace_2681175
  have hstable : (prefixWord ++ tailWord_2681175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681175).length < 2 ^ (prefixWord ++ tailWord_2681175).sum := by decide
  have hdescent : baseEnd_2681175 < baseStart_2681175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681203 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 6]
def baseStart_2681203 : Nat := 118140960795 + 2681203 * 2 ^ 59
def prefixEnd_2681203 : Nat := 4983230072969 + 3 ^ 40 * 2681203 * 2
def baseEnd_2681203 : Nat := 305943526950439669918195

theorem tailTrace_2681203 : CollatzResearch.WordTrace tailWord_2681203 prefixEnd_2681203 305943526950439669918195 := by
  unfold tailWord_2681203
  simp only [CollatzResearch.WordTrace]
  refine ⟨97791507305466918861192263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65194338203644612574128175 97791507305466918861192263)
  ·
    refine ⟨146687260958200378291788395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97791507305466918861192263 146687260958200378291788395)
    ·
      refine ⟨220030891437300567437682593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146687260958200378291788395 220030891437300567437682593)
      ·
        refine ⟨165023168577975425578261945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220030891437300567437682593 165023168577975425578261945)
        ·
          refine ⟨123767376433481569183696459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165023168577975425578261945 123767376433481569183696459)
          ·
            refine ⟨185651064650222353775544689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123767376433481569183696459 185651064650222353775544689)
            ·
              refine ⟨139238298487666765331658517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185651064650222353775544689 139238298487666765331658517)
              ·
                refine ⟨6526795241609379624921493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139238298487666765331658517 6526795241609379624921493)
                ·
                  refine ⟨305943526950439669918195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6526795241609379624921493 305943526950439669918195)
                  ·
                    rfl

theorem cell22_2681203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_2681203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681203 prefixEnd_2681203 := by exact prefixLift 2681203
  have htrace : WordTrace (prefixWord ++ tailWord_2681203) baseStart_2681203 baseEnd_2681203 := by
    simpa [prefixWord, tailWord_2681203, baseEnd_2681203] using wordTrace_append hprefix tailTrace_2681203
  have hstable : (prefixWord ++ tailWord_2681203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681203).length < 2 ^ (prefixWord ++ tailWord_2681203).sum := by decide
  have hdescent : baseEnd_2681203 < baseStart_2681203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681226 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_2681226 : Nat := 118140960795 + 2681226 * 2 ^ 59
def prefixEnd_2681226 : Nat := 4983230072969 + 3 ^ 40 * 2681226 * 2
def baseEnd_2681226 : Nat := 305946151407118205476505

theorem tailTrace_2681226 : CollatzResearch.WordTrace tailWord_2681226 prefixEnd_2681226 305946151407118205476505 := by
  unfold tailWord_2681226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24448086546095898447319883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65194897456255729192853021 24448086546095898447319883)
  ·
    refine ⟨36672129819143847670979825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24448086546095898447319883 36672129819143847670979825)
    ·
      refine ⟨27504097364357885753234869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36672129819143847670979825 27504097364357885753234869)
      ·
        refine ⟨2578509127908551789365769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27504097364357885753234869 2578509127908551789365769)
        ·
          refine ⟨1933881845931413842024327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2578509127908551789365769 1933881845931413842024327)
          ·
            refine ⟨2900822768897120763036491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933881845931413842024327 2900822768897120763036491)
            ·
              refine ⟨4351234153345681144554737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900822768897120763036491 4351234153345681144554737)
              ·
                refine ⟨3263425615009260858416053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351234153345681144554737 3263425615009260858416053)
                ·
                  refine ⟨305946151407118205476505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3263425615009260858416053 305946151407118205476505)
                  ·
                    rfl

theorem cell22_2681226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_2681226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681226 prefixEnd_2681226 := by exact prefixLift 2681226
  have htrace : WordTrace (prefixWord ++ tailWord_2681226) baseStart_2681226 baseEnd_2681226 := by
    simpa [prefixWord, tailWord_2681226, baseEnd_2681226] using wordTrace_append hprefix tailTrace_2681226
  have hstable : (prefixWord ++ tailWord_2681226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681226).length < 2 ^ (prefixWord ++ tailWord_2681226).sum := by decide
  have hdescent : baseEnd_2681226 < baseStart_2681226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681233 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2681233 : Nat := 118140960795 + 2681233 * 2 ^ 59
def prefixEnd_2681233 : Nat := 4983230072969 + 3 ^ 40 * 2681233 * 2
def baseEnd_2681233 : Nat := 917840850464408931504493

theorem tailTrace_2681233 : CollatzResearch.WordTrace tailWord_2681233 prefixEnd_2681233 917840850464408931504493 := by
  unfold tailWord_2681233
  simp only [CollatzResearch.WordTrace]
  refine ⟨97792601495358233984784353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65195067663572155989856235 97792601495358233984784353)
  ·
    refine ⟨73344451121518675488588265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97792601495358233984784353 73344451121518675488588265)
    ·
      refine ⟨55008338341139006616441199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73344451121518675488588265 55008338341139006616441199)
      ·
        refine ⟨82512507511708509924661799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55008338341139006616441199 82512507511708509924661799)
        ·
          refine ⟨123768761267562764886992699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82512507511708509924661799 123768761267562764886992699)
          ·
            refine ⟨185653141901344147330489049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123768761267562764886992699 185653141901344147330489049)
            ·
              refine ⟨139239856426008110497866787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185653141901344147330489049 139239856426008110497866787)
              ·
                refine ⟨208859784639012165746800181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139239856426008110497866787 208859784639012165746800181)
                ·
                  refine ⟨19580604809907390538762517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208859784639012165746800181 19580604809907390538762517)
                  ·
                    refine ⟨917840850464408931504493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19580604809907390538762517 917840850464408931504493)
                    ·
                      rfl

theorem cell22_2681233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2681233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681233 prefixEnd_2681233 := by exact prefixLift 2681233
  have htrace : WordTrace (prefixWord ++ tailWord_2681233) baseStart_2681233 baseEnd_2681233 := by
    simpa [prefixWord, tailWord_2681233, baseEnd_2681233] using wordTrace_append hprefix tailTrace_2681233
  have hstable : (prefixWord ++ tailWord_2681233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681233).length < 2 ^ (prefixWord ++ tailWord_2681233).sum := by decide
  have hdescent : baseEnd_2681233 < baseStart_2681233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681250 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2681250 : Nat := 118140960795 + 2681250 * 2 ^ 59
def prefixEnd_2681250 : Nat := 4983230072969 + 3 ^ 40 * 2681250 * 2
def baseEnd_2681250 : Nat := 917846669911826553829441

theorem tailTrace_2681250 : CollatzResearch.WordTrace tailWord_2681250 prefixEnd_2681250 917846669911826553829441 := by
  unfold tailWord_2681250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24448305384074161472038301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65195481024197763925435469 24448305384074161472038301)
  ·
    refine ⟨9168114519027810552014363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24448305384074161472038301 9168114519027810552014363)
    ·
      refine ⟨13752171778541715828021545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9168114519027810552014363 13752171778541715828021545)
      ·
        refine ⟨10314128833906286871016159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13752171778541715828021545 10314128833906286871016159)
        ·
          refine ⟨15471193250859430306524239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314128833906286871016159 15471193250859430306524239)
          ·
            refine ⟨23206789876289145459786359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15471193250859430306524239 23206789876289145459786359)
            ·
              refine ⟨34810184814433718189679539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23206789876289145459786359 34810184814433718189679539)
              ·
                refine ⟨52215277221650577284519309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34810184814433718189679539 52215277221650577284519309)
                ·
                  refine ⟨19580728958118966481694741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52215277221650577284519309 19580728958118966481694741)
                  ·
                    refine ⟨917846669911826553829441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19580728958118966481694741 917846669911826553829441)
                    ·
                      rfl

theorem cell22_2681250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2681250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681250 prefixEnd_2681250 := by exact prefixLift 2681250
  have htrace : WordTrace (prefixWord ++ tailWord_2681250) baseStart_2681250 baseEnd_2681250 := by
    simpa [prefixWord, tailWord_2681250, baseEnd_2681250] using wordTrace_append hprefix tailTrace_2681250
  have hstable : (prefixWord ++ tailWord_2681250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681250).length < 2 ^ (prefixWord ++ tailWord_2681250).sum := by decide
  have hdescent : baseEnd_2681250 < baseStart_2681250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681252 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_2681252 : Nat := 118140960795 + 2681252 * 2 ^ 59
def prefixEnd_2681252 : Nat := 4983230072969 + 3 ^ 40 * 2681252 * 2
def baseEnd_2681252 : Nat := 917847354552699215279435

theorem tailTrace_2681252 : CollatzResearch.WordTrace tailWord_2681252 prefixEnd_2681252 917847354552699215279435 := by
  unfold tailWord_2681252
  simp only [CollatzResearch.WordTrace]
  refine ⟨48896647241144700114863005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65195529654859600153150673 48896647241144700114863005)
  ·
    refine ⟨18336242715429262543073627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48896647241144700114863005 18336242715429262543073627)
    ·
      refine ⟨27504364073143893814610441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18336242715429262543073627 27504364073143893814610441)
      ·
        refine ⟨20628273054857920360957831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27504364073143893814610441 20628273054857920360957831)
        ·
          refine ⟨30942409582286880541436747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20628273054857920360957831 30942409582286880541436747)
          ·
            refine ⟨46413614373430320812155121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30942409582286880541436747 46413614373430320812155121)
            ·
              refine ⟨34810210780072740609116341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46413614373430320812155121 34810210780072740609116341)
              ·
                refine ⟨3263457260631819432104657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34810210780072740609116341 3263457260631819432104657)
                ·
                  refine ⟨2447592945473864574078493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263457260631819432104657 2447592945473864574078493)
                  ·
                    refine ⟨917847354552699215279435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447592945473864574078493 917847354552699215279435)
                    ·
                      rfl

theorem cell22_2681252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_2681252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681252 prefixEnd_2681252 := by exact prefixLift 2681252
  have htrace : WordTrace (prefixWord ++ tailWord_2681252) baseStart_2681252 baseEnd_2681252 := by
    simpa [prefixWord, tailWord_2681252, baseEnd_2681252] using wordTrace_append hprefix tailTrace_2681252
  have hstable : (prefixWord ++ tailWord_2681252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681252).length < 2 ^ (prefixWord ++ tailWord_2681252).sum := by decide
  have hdescent : baseEnd_2681252 < baseStart_2681252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681265 : List Nat := [1, 2, 2, 4, 1, 3, 1, 8]
def baseStart_2681265 : Nat := 118140960795 + 2681265 * 2 ^ 59
def prefixEnd_2681265 : Nat := 4983230072969 + 3 ^ 40 * 2681265 * 2
def baseEnd_2681265 : Nat := 101983533857596834967155

theorem tailTrace_2681265 : CollatzResearch.WordTrace tailWord_2681265 prefixEnd_2681265 101983533857596834967155 := by
  unfold tailWord_2681265
  simp only [CollatzResearch.WordTrace]
  refine ⟨97793768631242303449949249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65195845754161535633299499 97793768631242303449949249)
  ·
    refine ⟨73345326473431727587461937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97793768631242303449949249 73345326473431727587461937)
    ·
      refine ⟨55008994855073795690596453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73345326473431727587461937 55008994855073795690596453)
      ·
        refine ⟨10314186535326336691986835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55008994855073795690596453 10314186535326336691986835)
        ·
          refine ⟨15471279802989505037980253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314186535326336691986835 15471279802989505037980253)
          ·
            refine ⟨5801729926121064389242595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15471279802989505037980253 5801729926121064389242595)
            ·
              refine ⟨8702594889181596583863893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801729926121064389242595 8702594889181596583863893)
              ·
                refine ⟨101983533857596834967155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8702594889181596583863893 101983533857596834967155)
                ·
                  rfl

theorem cell22_2681265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 8].length) (baseStart_2681265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681265 prefixEnd_2681265 := by exact prefixLift 2681265
  have htrace : WordTrace (prefixWord ++ tailWord_2681265) baseStart_2681265 baseEnd_2681265 := by
    simpa [prefixWord, tailWord_2681265, baseEnd_2681265] using wordTrace_append hprefix tailTrace_2681265
  have hstable : (prefixWord ++ tailWord_2681265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681265).length < 2 ^ (prefixWord ++ tailWord_2681265).sum := by decide
  have hdescent : baseEnd_2681265 < baseStart_2681265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681284 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2681284 : Nat := 118140960795 + 2681284 * 2 ^ 59
def prefixEnd_2681284 : Nat := 4983230072969 + 3 ^ 40 * 2681284 * 2
def baseEnd_2681284 : Nat := 917858308806661798479337

theorem tailTrace_2681284 : CollatzResearch.WordTrace tailWord_2681284 prefixEnd_2681284 917858308806661798479337 := by
  unfold tailWord_2681284
  simp only [CollatzResearch.WordTrace]
  refine ⟨48897230809086734847445453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65196307745448979796593937 48897230809086734847445453)
  ·
    refine ⟨18336461553407525567792045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48897230809086734847445453 18336461553407525567792045)
    ·
      refine ⟨6876173082527822087922017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18336461553407525567792045 6876173082527822087922017)
      ·
        refine ⟨5157129811895866565941513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6876173082527822087922017 5157129811895866565941513)
        ·
          refine ⟨3867847358921899924456135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5157129811895866565941513 3867847358921899924456135)
          ·
            refine ⟨5801771038382849886684203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867847358921899924456135 5801771038382849886684203)
            ·
              refine ⟨8702656557574274830026305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801771038382849886684203 8702656557574274830026305)
              ·
                refine ⟨6526992418180706122519729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702656557574274830026305 6526992418180706122519729)
                ·
                  refine ⟨4895244313635529591889797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6526992418180706122519729 4895244313635529591889797)
                  ·
                    refine ⟨917858308806661798479337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4895244313635529591889797 917858308806661798479337)
                    ·
                      rfl

theorem cell22_2681284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2681284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681284 prefixEnd_2681284 := by exact prefixLift 2681284
  have htrace : WordTrace (prefixWord ++ tailWord_2681284) baseStart_2681284 baseEnd_2681284 := by
    simpa [prefixWord, tailWord_2681284, baseEnd_2681284] using wordTrace_append hprefix tailTrace_2681284
  have hstable : (prefixWord ++ tailWord_2681284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681284).length < 2 ^ (prefixWord ++ tailWord_2681284).sum := by decide
  have hdescent : baseEnd_2681284 < baseStart_2681284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681348 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2681348 : Nat := 118140960795 + 2681348 * 2 ^ 59
def prefixEnd_2681348 : Nat := 4983230072969 + 3 ^ 40 * 2681348 * 2
def baseEnd_2681348 : Nat := 917880217314586964879141

theorem tailTrace_2681348 : CollatzResearch.WordTrace tailWord_2681348 prefixEnd_2681348 917880217314586964879141 := by
  unfold tailWord_2681348
  simp only [CollatzResearch.WordTrace]
  refine ⟨48898397944970804312610349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65197863926627739083480465 48898397944970804312610349)
  ·
    refine ⟨18336899229364051617228881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48898397944970804312610349 18336899229364051617228881)
    ·
      refine ⟨13752674422023038712921661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18336899229364051617228881 13752674422023038712921661)
      ·
        refine ⟨5157252908258639517345623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13752674422023038712921661 5157252908258639517345623)
        ·
          refine ⟨7735879362387959276018435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5157252908258639517345623 7735879362387959276018435)
          ·
            refine ⟨11603819043581938914027653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735879362387959276018435 11603819043581938914027653)
            ·
              refine ⟨2175716070671613546380185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11603819043581938914027653 2175716070671613546380185)
              ·
                refine ⟨1631787053003710159785139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2175716070671613546380185 1631787053003710159785139)
                ·
                  refine ⟨2447680579505565239677709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631787053003710159785139 2447680579505565239677709)
                  ·
                    refine ⟨917880217314586964879141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447680579505565239677709 917880217314586964879141)
                    ·
                      rfl

theorem cell22_2681348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2681348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681348 prefixEnd_2681348 := by exact prefixLift 2681348
  have htrace : WordTrace (prefixWord ++ tailWord_2681348) baseStart_2681348 baseEnd_2681348 := by
    simpa [prefixWord, tailWord_2681348, baseEnd_2681348] using wordTrace_append hprefix tailTrace_2681348
  have hstable : (prefixWord ++ tailWord_2681348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681348).length < 2 ^ (prefixWord ++ tailWord_2681348).sum := by decide
  have hdescent : baseEnd_2681348 < baseStart_2681348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681372 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_2681372 : Nat := 118140960795 + 2681372 * 2 ^ 59
def prefixEnd_2681372 : Nat := 4983230072969 + 3 ^ 40 * 2681372 * 2
def baseEnd_2681372 : Nat := 305962811001686300759689

theorem tailTrace_2681372 : CollatzResearch.WordTrace tailWord_2681372 prefixEnd_2681372 305962811001686300759689 := by
  unfold tailWord_2681372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48898835620927330362047185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65198447494569773816062913 48898835620927330362047185)
  ·
    refine ⟨36674126715695497771535389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48898835620927330362047185 36674126715695497771535389)
    ·
      refine ⟨13752797518385811664325771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36674126715695497771535389 13752797518385811664325771)
      ·
        refine ⟨20629196277578717496488657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13752797518385811664325771 20629196277578717496488657)
        ·
          refine ⟨15471897208184038122366493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20629196277578717496488657 15471897208184038122366493)
          ·
            refine ⟨5801961453069014295887435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15471897208184038122366493 5801961453069014295887435)
            ·
              refine ⟨8702942179603521443831153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801961453069014295887435 8702942179603521443831153)
              ·
                refine ⟨6527206634702641082873365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702942179603521443831153 6527206634702641082873365)
                ·
                  refine ⟨305962811001686300759689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6527206634702641082873365 305962811001686300759689)
                  ·
                    rfl

theorem cell22_2681372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_2681372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681372 prefixEnd_2681372 := by exact prefixLift 2681372
  have htrace : WordTrace (prefixWord ++ tailWord_2681372) baseStart_2681372 baseEnd_2681372 := by
    simpa [prefixWord, tailWord_2681372, baseEnd_2681372] using wordTrace_append hprefix tailTrace_2681372
  have hstable : (prefixWord ++ tailWord_2681372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681372).length < 2 ^ (prefixWord ++ tailWord_2681372).sum := by decide
  have hdescent : baseEnd_2681372 < baseStart_2681372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681400 : List Nat := [2, 1, 2, 1, 4, 1, 11]
def baseStart_2681400 : Nat := 118140960795 + 2681400 * 2 ^ 59
def prefixEnd_2681400 : Nat := 4983230072969 + 3 ^ 40 * 2681400 * 2
def baseEnd_2681400 : Nat := 33996222888047265280703

theorem tailTrace_2681400 : CollatzResearch.WordTrace tailWord_2681400 prefixEnd_2681400 33996222888047265280703 := by
  unfold tailWord_2681400
  simp only [CollatzResearch.WordTrace]
  refine ⟨48899346242876610753056827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65199128323835481004075769 48899346242876610753056827)
  ·
    refine ⟨73349019364314916129585241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48899346242876610753056827 73349019364314916129585241)
    ·
      refine ⟨55011764523236187097188931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73349019364314916129585241 55011764523236187097188931)
      ·
        refine ⟨82517646784854280645783397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55011764523236187097188931 82517646784854280645783397)
        ·
          refine ⟨15472058772160177621084387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82517646784854280645783397 15472058772160177621084387)
          ·
            refine ⟨23208088158240266431626581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15472058772160177621084387 23208088158240266431626581)
            ·
              refine ⟨33996222888047265280703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23208088158240266431626581 33996222888047265280703)
              ·
                rfl

theorem cell22_2681400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 11].length) (baseStart_2681400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681400 prefixEnd_2681400 := by exact prefixLift 2681400
  have htrace : WordTrace (prefixWord ++ tailWord_2681400) baseStart_2681400 baseEnd_2681400 := by
    simpa [prefixWord, tailWord_2681400, baseEnd_2681400] using wordTrace_append hprefix tailTrace_2681400
  have hstable : (prefixWord ++ tailWord_2681400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681400).length < 2 ^ (prefixWord ++ tailWord_2681400).sum := by decide
  have hdescent : baseEnd_2681400 < baseStart_2681400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681404 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_2681404 : Nat := 118140960795 + 2681404 * 2 ^ 59
def prefixEnd_2681404 : Nat := 4983230072969 + 3 ^ 40 * 2681404 * 2
def baseEnd_2681404 : Nat := 917899387259021485478969

theorem tailTrace_2681404 : CollatzResearch.WordTrace tailWord_2681404 prefixEnd_2681404 917899387259021485478969 := by
  unfold tailWord_2681404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48899419188869365094629633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65199225585159153459506177 48899419188869365094629633)
  ·
    refine ⟨36674564391652023820972225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48899419188869365094629633 36674564391652023820972225)
    ·
      refine ⟨27505923293739017865729169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36674564391652023820972225 27505923293739017865729169)
      ·
        refine ⟨20629442470304263399296877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27505923293739017865729169 20629442470304263399296877)
        ·
          refine ⟨7736040926364098774736329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20629442470304263399296877 7736040926364098774736329)
          ·
            refine ⟨5802030694773074081052247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7736040926364098774736329 5802030694773074081052247)
            ·
              refine ⟨8703046042159611121578371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802030694773074081052247 8703046042159611121578371)
              ·
                refine ⟨13054569063239416682367557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8703046042159611121578371 13054569063239416682367557)
                ·
                  refine ⟨2447731699357390627943917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13054569063239416682367557 2447731699357390627943917)
                  ·
                    refine ⟨917899387259021485478969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447731699357390627943917 917899387259021485478969)
                    ·
                      rfl

theorem cell22_2681404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_2681404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681404 prefixEnd_2681404 := by exact prefixLift 2681404
  have htrace : WordTrace (prefixWord ++ tailWord_2681404) baseStart_2681404 baseEnd_2681404 := by
    simpa [prefixWord, tailWord_2681404, baseEnd_2681404] using wordTrace_append hprefix tailTrace_2681404
  have hstable : (prefixWord ++ tailWord_2681404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681404).length < 2 ^ (prefixWord ++ tailWord_2681404).sum := by decide
  have hdescent : baseEnd_2681404 < baseStart_2681404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681406 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2681406 : Nat := 118140960795 + 2681406 * 2 ^ 59
def prefixEnd_2681406 : Nat := 4983230072969 + 3 ^ 40 * 2681406 * 2
def baseEnd_2681406 : Nat := 305966690633298048976321

theorem tailTrace_2681406 : CollatzResearch.WordTrace tailWord_2681406 prefixEnd_2681406 305966690633298048976321 := by
  unfold tailWord_2681406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224863915466435566354009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65199274215820989687221381 12224863915466435566354009)
  ·
    refine ⟨9168647936599826674765507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12224863915466435566354009 9168647936599826674765507)
    ·
      refine ⟨13752971904899740012148261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9168647936599826674765507 13752971904899740012148261)
      ·
        refine ⟨2578682232168701252277799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13752971904899740012148261 2578682232168701252277799)
        ·
          refine ⟨3868023348253051878416699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578682232168701252277799 3868023348253051878416699)
          ·
            refine ⟨5802035022379577817625049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868023348253051878416699 5802035022379577817625049)
            ·
              refine ⟨4351526266784683363218787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5802035022379577817625049 4351526266784683363218787)
              ·
                refine ⟨6527289400177025044828181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351526266784683363218787 6527289400177025044828181)
                ·
                  refine ⟨305966690633298048976321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6527289400177025044828181 305966690633298048976321)
                  ·
                    rfl

theorem cell22_2681406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2681406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681406 prefixEnd_2681406 := by exact prefixLift 2681406
  have htrace : WordTrace (prefixWord ++ tailWord_2681406) baseStart_2681406 baseEnd_2681406 := by
    simpa [prefixWord, tailWord_2681406, baseEnd_2681406] using wordTrace_append hprefix tailTrace_2681406
  have hstable : (prefixWord ++ tailWord_2681406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681406).length < 2 ^ (prefixWord ++ tailWord_2681406).sum := by decide
  have hdescent : baseEnd_2681406 < baseStart_2681406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681421 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2681421 : Nat := 118140960795 + 2681421 * 2 ^ 59
def prefixEnd_2681421 : Nat := 4983230072969 + 3 ^ 40 * 2681421 * 2
def baseEnd_2681421 : Nat := 917905206706439107803917

theorem tailTrace_2681421 : CollatzResearch.WordTrace tailWord_2681421 prefixEnd_2681421 917905206706439107803917 := by
  unfold tailWord_2681421
  simp only [CollatzResearch.WordTrace]
  refine ⟨97799458418677142092628117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65199638945784761395085411 97799458418677142092628117)
  ·
    refine ⟨4584349613375491035591943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97799458418677142092628117 4584349613375491035591943)
    ·
      refine ⟨6876524420063236553387915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584349613375491035591943 6876524420063236553387915)
      ·
        refine ⟨10314786630094854830081873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876524420063236553387915 10314786630094854830081873)
        ·
          refine ⟨7736089972571141122561405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10314786630094854830081873 7736089972571141122561405)
          ·
            refine ⟨2901033739714177920960527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7736089972571141122561405 2901033739714177920960527)
            ·
              refine ⟨4351550609571266881440791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901033739714177920960527 4351550609571266881440791)
              ·
                refine ⟨6527325914356900322161187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351550609571266881440791 6527325914356900322161187)
                ·
                  refine ⟨9790988871535350483241781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6527325914356900322161187 9790988871535350483241781)
                  ·
                    refine ⟨917905206706439107803917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9790988871535350483241781 917905206706439107803917)
                    ·
                      rfl

theorem cell22_2681421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2681421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681421 prefixEnd_2681421 := by exact prefixLift 2681421
  have htrace : WordTrace (prefixWord ++ tailWord_2681421) baseStart_2681421 baseEnd_2681421 := by
    simpa [prefixWord, tailWord_2681421, baseEnd_2681421] using wordTrace_append hprefix tailTrace_2681421
  have hstable : (prefixWord ++ tailWord_2681421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681421).length < 2 ^ (prefixWord ++ tailWord_2681421).sum := by decide
  have hdescent : baseEnd_2681421 < baseStart_2681421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681522 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_2681522 : Nat := 118140960795 + 2681522 * 2 ^ 59
def prefixEnd_2681522 : Nat := 4983230072969 + 3 ^ 40 * 2681522 * 2
def baseEnd_2681522 : Nat := 917939781070508511028607

theorem tailTrace_2681522 : CollatzResearch.WordTrace tailWord_2681522 prefixEnd_2681522 917939781070508511028607 := by
  unfold tailWord_2681522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450785547827809085513705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65202094794207490894703213 24450785547827809085513705)
  ·
    refine ⟨18338089160870856814135279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24450785547827809085513705 18338089160870856814135279)
    ·
      refine ⟨27507133741306285221202919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18338089160870856814135279 27507133741306285221202919)
      ·
        refine ⟨41260700611959427831804379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27507133741306285221202919 41260700611959427831804379)
        ·
          refine ⟨61891050917939141747706569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41260700611959427831804379 61891050917939141747706569)
          ·
            refine ⟨46418288188454356310779927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61891050917939141747706569 46418288188454356310779927)
            ·
              refine ⟨69627432282681534466169891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46418288188454356310779927 69627432282681534466169891)
              ·
                refine ⟨104441148424022301699254837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69627432282681534466169891 104441148424022301699254837)
                ·
                  refine ⟨9791357664752090784305141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104441148424022301699254837 9791357664752090784305141)
                  ·
                    refine ⟨917939781070508511028607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9791357664752090784305141 917939781070508511028607)
                    ·
                      rfl

theorem cell22_2681522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_2681522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681522 prefixEnd_2681522 := by exact prefixLift 2681522
  have htrace : WordTrace (prefixWord ++ tailWord_2681522) baseStart_2681522 baseEnd_2681522 := by
    simpa [prefixWord, tailWord_2681522, baseEnd_2681522] using wordTrace_append hprefix tailTrace_2681522
  have hstable : (prefixWord ++ tailWord_2681522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681522).length < 2 ^ (prefixWord ++ tailWord_2681522).sum := by decide
  have hdescent : baseEnd_2681522 < baseStart_2681522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681573 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_2681573 : Nat := 118140960795 + 2681573 * 2 ^ 59
def prefixEnd_2681573 : Nat := 4983230072969 + 3 ^ 40 * 2681573 * 2
def baseEnd_2681573 : Nat := 917957239412761378003451

theorem tailTrace_2681573 : CollatzResearch.WordTrace tailWord_2681573 prefixEnd_2681573 917957239412761378003451 := by
  unfold tailWord_2681573
  simp only [CollatzResearch.WordTrace]
  refine ⟨97805002314126472052161373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65203334876084314701440915 97805002314126472052161373)
  ·
    refine ⟨36676875867797427019560515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97805002314126472052161373 36676875867797427019560515)
    ·
      refine ⟨55015313801696140529340773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36676875867797427019560515 55015313801696140529340773)
      ·
        refine ⟨10315371337818026349251395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55015313801696140529340773 10315371337818026349251395)
        ·
          refine ⟨15473057006727039523877093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10315371337818026349251395 15473057006727039523877093)
          ·
            refine ⟨2901198188761319910726955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15473057006727039523877093 2901198188761319910726955)
            ·
              refine ⟨4351797283141979866090433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901198188761319910726955 4351797283141979866090433)
              ·
                refine ⟨3263847962356484899567825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351797283141979866090433 3263847962356484899567825)
                ·
                  refine ⟨2447885971767363674675869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263847962356484899567825 2447885971767363674675869)
                  ·
                    refine ⟨917957239412761378003451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447885971767363674675869 917957239412761378003451)
                    ·
                      rfl

theorem cell22_2681573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_2681573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681573 prefixEnd_2681573 := by exact prefixLift 2681573
  have htrace : WordTrace (prefixWord ++ tailWord_2681573) baseStart_2681573 baseEnd_2681573 := by
    simpa [prefixWord, tailWord_2681573, baseEnd_2681573] using wordTrace_append hprefix tailTrace_2681573
  have hstable : (prefixWord ++ tailWord_2681573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681573).length < 2 ^ (prefixWord ++ tailWord_2681573).sum := by decide
  have hdescent : baseEnd_2681573 < baseStart_2681573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681644 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_2681644 : Nat := 118140960795 + 2681644 * 2 ^ 59
def prefixEnd_2681644 : Nat := 4983230072969 + 3 ^ 40 * 2681644 * 2
def baseEnd_2681644 : Nat := 917981544163740859478233

theorem tailTrace_2681644 : CollatzResearch.WordTrace tailWord_2681644 prefixEnd_2681644 917981544163740859478233 := by
  unfold tailWord_2681644
  simp only [CollatzResearch.WordTrace]
  refine ⟨48903795948434625588997993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65205061264579500785330657 48903795948434625588997993)
  ·
    refine ⟨36677846961325969191748495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48903795948434625588997993 36677846961325969191748495)
    ·
      refine ⟨55016770441988953787622743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36677846961325969191748495 55016770441988953787622743)
      ·
        refine ⟨82525155662983430681434115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55016770441988953787622743 82525155662983430681434115)
        ·
          refine ⟨123787733494475146022151173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82525155662983430681434115 123787733494475146022151173)
          ·
            refine ⟨23210200030214089879153345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123787733494475146022151173 23210200030214089879153345)
            ·
              refine ⟨17407650022660567409365009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23210200030214089879153345 17407650022660567409365009)
              ·
                refine ⟨13055737516995425557023757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17407650022660567409365009 13055737516995425557023757)
                ·
                  refine ⟨4895901568873284583883909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13055737516995425557023757 4895901568873284583883909)
                  ·
                    refine ⟨917981544163740859478233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4895901568873284583883909 917981544163740859478233)
                    ·
                      rfl

theorem cell22_2681644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_2681644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681644 prefixEnd_2681644 := by exact prefixLift 2681644
  have htrace : WordTrace (prefixWord ++ tailWord_2681644) baseStart_2681644 baseEnd_2681644 := by
    simpa [prefixWord, tailWord_2681644, baseEnd_2681644] using wordTrace_append hprefix tailTrace_2681644
  have hstable : (prefixWord ++ tailWord_2681644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681644).length < 2 ^ (prefixWord ++ tailWord_2681644).sum := by decide
  have hdescent : baseEnd_2681644 < baseStart_2681644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681721 : List Nat := [1, 2, 1, 3, 2, 4, 3, 6]
def baseStart_2681721 : Nat := 118140960795 + 2681721 * 2 ^ 59
def prefixEnd_2681721 : Nat := 4983230072969 + 3 ^ 40 * 2681721 * 2
def baseEnd_2681721 : Nat := 102000878093037591700333

theorem tailTrace_2681721 : CollatzResearch.WordTrace tailWord_2681721 prefixEnd_2681721 102000878093037591700333 := by
  unfold tailWord_2681721
  simp only [CollatzResearch.WordTrace]
  refine ⟨97810400317590293328549017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65206933545060195552366011 97810400317590293328549017)
  ·
    refine ⟨73357800238192719996411763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97810400317590293328549017 73357800238192719996411763)
    ·
      refine ⟨110036700357289079994617645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73357800238192719996411763 110036700357289079994617645)
      ·
        refine ⟨41263762633983404997981617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110036700357289079994617645 41263762633983404997981617)
        ·
          refine ⟨30947821975487553748486213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41263762633983404997981617 30947821975487553748486213)
          ·
            refine ⟨5802716620403916327841165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30947821975487553748486213 5802716620403916327841165)
            ·
              refine ⟨2176018732651468622940437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5802716620403916327841165 2176018732651468622940437)
              ·
                refine ⟨102000878093037591700333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2176018732651468622940437 102000878093037591700333)
                ·
                  rfl

theorem cell22_2681721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 6].length) (baseStart_2681721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681721 prefixEnd_2681721 := by exact prefixLift 2681721
  have htrace : WordTrace (prefixWord ++ tailWord_2681721) baseStart_2681721 baseEnd_2681721 := by
    simpa [prefixWord, tailWord_2681721, baseEnd_2681721] using wordTrace_append hprefix tailTrace_2681721
  have hstable : (prefixWord ++ tailWord_2681721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681721).length < 2 ^ (prefixWord ++ tailWord_2681721).sum := by decide
  have hdescent : baseEnd_2681721 < baseStart_2681721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681946 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_2681946 : Nat := 118140960795 + 2681946 * 2 ^ 59
def prefixEnd_2681946 : Nat := 4983230072969 + 3 ^ 40 * 2681946 * 2
def baseEnd_2681946 : Nat := 306028308311837579475769

theorem tailTrace_2681946 : CollatzResearch.WordTrace tailWord_2681946 prefixEnd_2681946 306028308311837579475769 := by
  unfold tailWord_2681946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24454651685443789188872423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65212404494516771170326461 24454651685443789188872423)
  ·
    refine ⟨36681977528165683783308635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24454651685443789188872423 36681977528165683783308635)
    ·
      refine ⟨55022966292248525674962953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36681977528165683783308635 55022966292248525674962953)
      ·
        refine ⟨41267224719186394256222215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55022966292248525674962953 41267224719186394256222215)
        ·
          refine ⟨61900837078779591384333323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41267224719186394256222215 61900837078779591384333323)
          ·
            refine ⟨92851255618169387076499985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61900837078779591384333323 92851255618169387076499985)
            ·
              refine ⟨69638441713627040307374989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92851255618169387076499985 69638441713627040307374989)
              ·
                refine ⟨26114415642610140115265621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69638441713627040307374989 26114415642610140115265621)
                ·
                  refine ⟨306028308311837579475769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26114415642610140115265621 306028308311837579475769)
                  ·
                    rfl

theorem cell22_2681946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_2681946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681946 prefixEnd_2681946 := by exact prefixLift 2681946
  have htrace : WordTrace (prefixWord ++ tailWord_2681946) baseStart_2681946 baseEnd_2681946 := by
    simpa [prefixWord, tailWord_2681946, baseEnd_2681946] using wordTrace_append hprefix tailTrace_2681946
  have hstable : (prefixWord ++ tailWord_2681946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681946).length < 2 ^ (prefixWord ++ tailWord_2681946).sum := by decide
  have hdescent : baseEnd_2681946 < baseStart_2681946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681965 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2681965 : Nat := 118140960795 + 2681965 * 2 ^ 59
def prefixEnd_2681965 : Nat := 4983230072969 + 3 ^ 40 * 2681965 * 2
def baseEnd_2681965 : Nat := 918091429023803022202249

theorem tailTrace_2681965 : CollatzResearch.WordTrace tailWord_2681965 prefixEnd_2681965 918091429023803022202249 := by
  unfold tailWord_2681965
  simp only [CollatzResearch.WordTrace]
  refine ⟨97819299728706323000431349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65212866485804215333620899 97819299728706323000431349)
  ·
    refine ⟨9170559349566217781290439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97819299728706323000431349 9170559349566217781290439)
    ·
      refine ⟨13755839024349326671935659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9170559349566217781290439 13755839024349326671935659)
      ·
        refine ⟨20633758536523990007903489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13755839024349326671935659 20633758536523990007903489)
        ·
          refine ⟨15475318902392992505927617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20633758536523990007903489 15475318902392992505927617)
          ·
            refine ⟨11606489176794744379445713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15475318902392992505927617 11606489176794744379445713)
            ·
              refine ⟨8704866882596058284584285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11606489176794744379445713 8704866882596058284584285)
              ·
                refine ⟨3264325080973521856719107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8704866882596058284584285 3264325080973521856719107)
                ·
                  refine ⟨4896487621460282785078661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264325080973521856719107 4896487621460282785078661)
                  ·
                    refine ⟨918091429023803022202249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4896487621460282785078661 918091429023803022202249)
                    ·
                      rfl

theorem cell22_2681965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2681965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2681965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2681965 prefixEnd_2681965 := by exact prefixLift 2681965
  have htrace : WordTrace (prefixWord ++ tailWord_2681965) baseStart_2681965 baseEnd_2681965 := by
    simpa [prefixWord, tailWord_2681965, baseEnd_2681965] using wordTrace_append hprefix tailTrace_2681965
  have hstable : (prefixWord ++ tailWord_2681965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681965).length < 2 ^ (prefixWord ++ tailWord_2681965).sum := by decide
  have hdescent : baseEnd_2681965 < baseStart_2681965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682008 : List Nat := [2, 1, 2, 4, 2, 1, 2, 8]
def baseStart_2682008 : Nat := 118140960795 + 2682008 * 2 ^ 59
def prefixEnd_2682008 : Nat := 4983230072969 + 3 ^ 40 * 2682008 * 2
def baseEnd_2682008 : Nat := 102011794311396138153013

theorem tailTrace_2682008 : CollatzResearch.WordTrace tailWord_2682008 prefixEnd_2682008 102011794311396138153013 := by
  unfold tailWord_2682008
  simp only [CollatzResearch.WordTrace]
  refine ⟨48910434033775270672123339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65213912045033694229497785 48910434033775270672123339)
  ·
    refine ⟨73365651050662906008185009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48910434033775270672123339 73365651050662906008185009)
    ·
      refine ⟨55024238287997179506138757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73365651050662906008185009 55024238287997179506138757)
      ·
        refine ⟨10317044678999471157401017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55024238287997179506138757 10317044678999471157401017)
        ·
          refine ⟨7737783509249603368050763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10317044678999471157401017 7737783509249603368050763)
          ·
            refine ⟨11606675263874405052076145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7737783509249603368050763 11606675263874405052076145)
            ·
              refine ⟨8705006447905803789057109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11606675263874405052076145 8705006447905803789057109)
              ·
                refine ⟨102011794311396138153013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8705006447905803789057109 102011794311396138153013)
                ·
                  rfl

theorem cell22_2682008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_2682008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682008 prefixEnd_2682008 := by exact prefixLift 2682008
  have htrace : WordTrace (prefixWord ++ tailWord_2682008) baseStart_2682008 baseEnd_2682008 := by
    simpa [prefixWord, tailWord_2682008, baseEnd_2682008] using wordTrace_append hprefix tailTrace_2682008
  have hstable : (prefixWord ++ tailWord_2682008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682008).length < 2 ^ (prefixWord ++ tailWord_2682008).sum := by decide
  have hdescent : baseEnd_2682008 < baseStart_2682008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682010 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_2682010 : Nat := 118140960795 + 2682010 * 2 ^ 59
def prefixEnd_2682010 : Nat := 4983230072969 + 3 ^ 40 * 2682010 * 2
def baseEnd_2682010 : Nat := 918106833443437904827111

theorem tailTrace_2682010 : CollatzResearch.WordTrace tailWord_2682010 prefixEnd_2682010 918106833443437904827111 := by
  unfold tailWord_2682010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24455235253385823921454871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65213960675695530457212989 24455235253385823921454871)
  ·
    refine ⟨36682852880078735882182307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24455235253385823921454871 36682852880078735882182307)
    ·
      refine ⟨55024279320118103823273461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36682852880078735882182307 55024279320118103823273461)
      ·
        refine ⟨5158526186261072233431887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55024279320118103823273461 5158526186261072233431887)
        ·
          refine ⟨7737789279391608350147831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158526186261072233431887 7737789279391608350147831)
          ·
            refine ⟨11606683919087412525221747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7737789279391608350147831 11606683919087412525221747)
            ·
              refine ⟨17410025878631118787832621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11606683919087412525221747 17410025878631118787832621)
              ·
                refine ⟨6528759704486669545437233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17410025878631118787832621 6528759704486669545437233)
                ·
                  refine ⟨4896569778365002159077925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528759704486669545437233 4896569778365002159077925)
                  ·
                    refine ⟨918106833443437904827111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4896569778365002159077925 918106833443437904827111)
                    ·
                      rfl

theorem cell22_2682010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_2682010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682010 prefixEnd_2682010 := by exact prefixLift 2682010
  have htrace : WordTrace (prefixWord ++ tailWord_2682010) baseStart_2682010 baseEnd_2682010 := by
    simpa [prefixWord, tailWord_2682010, baseEnd_2682010] using wordTrace_append hprefix tailTrace_2682010
  have hstable : (prefixWord ++ tailWord_2682010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682010).length < 2 ^ (prefixWord ++ tailWord_2682010).sum := by decide
  have hdescent : baseEnd_2682010 < baseStart_2682010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682029 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_2682029 : Nat := 118140960795 + 2682029 * 2 ^ 59
def prefixEnd_2682029 : Nat := 4983230072969 + 3 ^ 40 * 2682029 * 2
def baseEnd_2682029 : Nat := 918113337531728188602053

theorem tailTrace_2682029 : CollatzResearch.WordTrace tailWord_2682029 prefixEnd_2682029 918113337531728188602053 := by
  unfold tailWord_2682029
  simp only [CollatzResearch.WordTrace]
  refine ⟨97821634000474461930761141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65214422666982974620507427 97821634000474461930761141)
  ·
    refine ⟨9170778187544480806008857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97821634000474461930761141 9170778187544480806008857)
    ·
      refine ⟨6878083640658360604506643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9170778187544480806008857 6878083640658360604506643)
      ·
        refine ⟨10317125460987540906759965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6878083640658360604506643 10317125460987540906759965)
        ·
          refine ⟨3868922047870327840034987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10317125460987540906759965 3868922047870327840034987)
          ·
            refine ⟨5803383071805491760052481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868922047870327840034987 5803383071805491760052481)
            ·
              refine ⟨4352537303854118820039361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5803383071805491760052481 4352537303854118820039361)
              ·
                refine ⟨3264402977890589115029521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4352537303854118820039361 3264402977890589115029521)
                ·
                  refine ⟨2448302233417941836272141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3264402977890589115029521 2448302233417941836272141)
                  ·
                    refine ⟨918113337531728188602053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448302233417941836272141 918113337531728188602053)
                    ·
                      rfl

theorem cell22_2682029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_2682029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682029 prefixEnd_2682029 := by exact prefixLift 2682029
  have htrace : WordTrace (prefixWord ++ tailWord_2682029) baseStart_2682029 baseEnd_2682029 := by
    simpa [prefixWord, tailWord_2682029, baseEnd_2682029] using wordTrace_append hprefix tailTrace_2682029
  have hstable : (prefixWord ++ tailWord_2682029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682029).length < 2 ^ (prefixWord ++ tailWord_2682029).sum := by decide
  have hdescent : baseEnd_2682029 < baseStart_2682029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682061 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2682061 : Nat := 118140960795 + 2682061 * 2 ^ 59
def prefixEnd_2682061 : Nat := 4983230072969 + 3 ^ 40 * 2682061 * 2
def baseEnd_2682061 : Nat := 918124291785690771801955

theorem tailTrace_2682061 : CollatzResearch.WordTrace tailWord_2682061 prefixEnd_2682061 918124291785690771801955 := by
  unfold tailWord_2682061
  simp only [CollatzResearch.WordTrace]
  refine ⟨97822801136358531395926037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65215200757572354263950691 97822801136358531395926037)
  ·
    refine ⟨4585443803266806159184033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97822801136358531395926037 4585443803266806159184033)
    ·
      refine ⟨3439082852450104619388025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4585443803266806159184033 3439082852450104619388025)
      ·
        refine ⟨2579312139337578464541019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3439082852450104619388025 2579312139337578464541019)
        ·
          refine ⟨3868968209006367696811529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2579312139337578464541019 3868968209006367696811529)
          ·
            refine ⟨2901726156754775772608647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3868968209006367696811529 2901726156754775772608647)
            ·
              refine ⟨4352589235132163658912971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901726156754775772608647 4352589235132163658912971)
              ·
                refine ⟨6528883852698245488369457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352589235132163658912971 6528883852698245488369457)
                ·
                  refine ⟨4896662889523684116277093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528883852698245488369457 4896662889523684116277093)
                  ·
                    refine ⟨918124291785690771801955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4896662889523684116277093 918124291785690771801955)
                    ·
                      rfl

theorem cell22_2682061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2682061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682061 prefixEnd_2682061 := by exact prefixLift 2682061
  have htrace : WordTrace (prefixWord ++ tailWord_2682061) baseStart_2682061 baseEnd_2682061 := by
    simpa [prefixWord, tailWord_2682061, baseEnd_2682061] using wordTrace_append hprefix tailTrace_2682061
  have hstable : (prefixWord ++ tailWord_2682061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682061).length < 2 ^ (prefixWord ++ tailWord_2682061).sum := by decide
  have hdescent : baseEnd_2682061 < baseStart_2682061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682149 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 4]
def baseStart_2682149 : Nat := 118140960795 + 2682149 * 2 ^ 59
def prefixEnd_2682149 : Nat := 4983230072969 + 3 ^ 40 * 2682149 * 2
def baseEnd_2682149 : Nat := 306051471994695958533895

theorem tailTrace_2682149 : CollatzResearch.WordTrace tailWord_2682149 prefixEnd_2682149 306051471994695958533895 := by
  unfold tailWord_2682149
  simp only [CollatzResearch.WordTrace]
  refine ⟨97826010760039722425129501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65217340506693148283419667 97826010760039722425129501)
  ·
    refine ⟨36684754035014895909423563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97826010760039722425129501 36684754035014895909423563)
    ·
      refine ⟨55027131052522343864135345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36684754035014895909423563 55027131052522343864135345)
      ·
        refine ⟨41270348289391757898101509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55027131052522343864135345 41270348289391757898101509)
        ·
          refine ⟨7738190304260954605894033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41270348289391757898101509 7738190304260954605894033)
          ·
            refine ⟨5803642728195715954420525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7738190304260954605894033 5803642728195715954420525)
            ·
              refine ⟨2176366023073393482907697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5803642728195715954420525 2176366023073393482907697)
              ·
                refine ⟨1632274517305045112180773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176366023073393482907697 1632274517305045112180773)
                ·
                  refine ⟨306051471994695958533895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632274517305045112180773 306051471994695958533895)
                  ·
                    rfl

theorem cell22_2682149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_2682149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682149 prefixEnd_2682149 := by exact prefixLift 2682149
  have htrace : WordTrace (prefixWord ++ tailWord_2682149) baseStart_2682149 baseEnd_2682149 := by
    simpa [prefixWord, tailWord_2682149, baseEnd_2682149] using wordTrace_append hprefix tailTrace_2682149
  have hstable : (prefixWord ++ tailWord_2682149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682149).length < 2 ^ (prefixWord ++ tailWord_2682149).sum := by decide
  have hdescent : baseEnd_2682149 < baseStart_2682149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682164 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_2682164 : Nat := 118140960795 + 2682164 * 2 ^ 59
def prefixEnd_2682164 : Nat := 4983230072969 + 3 ^ 40 * 2682164 * 2
def baseEnd_2682164 : Nat := 918159550790632836476639

theorem tailTrace_2682164 : CollatzResearch.WordTrace tailWord_2682164 prefixEnd_2682164 918159550790632836476639 := by
  unfold tailWord_2682164
  simp only [CollatzResearch.WordTrace]
  refine ⟨48913278927492689993462773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65217705236656919991283697 48913278927492689993462773)
  ·
    refine ⟨4585619899452439686887135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48913278927492689993462773 4585619899452439686887135)
    ·
      refine ⟨6878429849178659530330703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585619899452439686887135 6878429849178659530330703)
      ·
        refine ⟨10317644773767989295496055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6878429849178659530330703 10317644773767989295496055)
        ·
          refine ⟨15476467160651983943244083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10317644773767989295496055 15476467160651983943244083)
          ·
            refine ⟨23214700740977975914866125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15476467160651983943244083 23214700740977975914866125)
            ·
              refine ⟨8705512777866740968074797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23214700740977975914866125 8705512777866740968074797)
              ·
                refine ⟨3264567291700027863028049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8705512777866740968074797 3264567291700027863028049)
                ·
                  refine ⟨2448425468775020897271037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3264567291700027863028049 2448425468775020897271037)
                  ·
                    refine ⟨918159550790632836476639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448425468775020897271037 918159550790632836476639)
                    ·
                      rfl

theorem cell22_2682164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_2682164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682164 prefixEnd_2682164 := by exact prefixLift 2682164
  have htrace : WordTrace (prefixWord ++ tailWord_2682164) baseStart_2682164 baseEnd_2682164 := by
    simpa [prefixWord, tailWord_2682164, baseEnd_2682164] using wordTrace_append hprefix tailTrace_2682164
  have hstable : (prefixWord ++ tailWord_2682164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682164).length < 2 ^ (prefixWord ++ tailWord_2682164).sum := by decide
  have hdescent : baseEnd_2682164 < baseStart_2682164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682220 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_2682220 : Nat := 118140960795 + 2682220 * 2 ^ 59
def prefixEnd_2682220 : Nat := 4983230072969 + 3 ^ 40 * 2682220 * 2
def baseEnd_2682220 : Nat := 918178720735067357076467

theorem tailTrace_2682220 : CollatzResearch.WordTrace tailWord_2682220 prefixEnd_2682220 918178720735067357076467 := by
  unfold tailWord_2682220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48914300171391250775482057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65219066895188334367309409 48914300171391250775482057)
  ·
    refine ⟨36685725128543438081611543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48914300171391250775482057 36685725128543438081611543)
    ·
      refine ⟨55028587692815157122417315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36685725128543438081611543 55028587692815157122417315)
      ·
        refine ⟨82542881539222735683625973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55028587692815157122417315 82542881539222735683625973)
        ·
          refine ⟨7738395144302131470339935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82542881539222735683625973 7738395144302131470339935)
          ·
            refine ⟨11607592716453197205509903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7738395144302131470339935 11607592716453197205509903)
            ·
              refine ⟨17411389074679795808264855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11607592716453197205509903 17411389074679795808264855)
              ·
                refine ⟨26117083612019693712397283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17411389074679795808264855 26117083612019693712397283)
                ·
                  refine ⟨39175625418029540568595925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26117083612019693712397283 39175625418029540568595925)
                  ·
                    refine ⟨918178720735067357076467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39175625418029540568595925 918178720735067357076467)
                    ·
                      rfl

theorem cell22_2682220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_2682220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682220 prefixEnd_2682220 := by exact prefixLift 2682220
  have htrace : WordTrace (prefixWord ++ tailWord_2682220) baseStart_2682220 baseEnd_2682220 := by
    simpa [prefixWord, tailWord_2682220, baseEnd_2682220] using wordTrace_append hprefix tailTrace_2682220
  have hstable : (prefixWord ++ tailWord_2682220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682220).length < 2 ^ (prefixWord ++ tailWord_2682220).sum := by decide
  have hdescent : baseEnd_2682220 < baseStart_2682220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682235 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 3, 4]
def baseStart_2682235 : Nat := 118140960795 + 2682235 * 2 ^ 59
def prefixEnd_2682235 : Nat := 4983230072969 + 3 ^ 40 * 2682235 * 2
def baseEnd_2682235 : Nat := 918183855541612317951421

theorem tailTrace_2682235 : CollatzResearch.WordTrace tailWord_2682235 prefixEnd_2682235 918183855541612317951421 := by
  unfold tailWord_2682235
  simp only [CollatzResearch.WordTrace]
  refine ⟨97829147437728159112760159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65219431625152106075173439 97829147437728159112760159)
  ·
    refine ⟨146743721156592238669140239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97829147437728159112760159 146743721156592238669140239)
    ·
      refine ⟨220115581734888358003710359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146743721156592238669140239 220115581734888358003710359)
      ·
        refine ⟨330173372602332537005565539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220115581734888358003710359 330173372602332537005565539)
        ·
          refine ⟨495260058903498805508348309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330173372602332537005565539 495260058903498805508348309)
          ·
            refine ⟨23215315261101506508203827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 495260058903498805508348309 23215315261101506508203827)
            ·
              refine ⟨34822972891652259762305741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23215315261101506508203827 34822972891652259762305741)
              ·
                refine ⟨13058614834369597410864653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34822972891652259762305741 13058614834369597410864653)
                ·
                  refine ⟨4896980562888599029074245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13058614834369597410864653 4896980562888599029074245)
                  ·
                    refine ⟨918183855541612317951421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4896980562888599029074245 918183855541612317951421)
                    ·
                      rfl

theorem cell22_2682235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_2682235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682235 prefixEnd_2682235 := by exact prefixLift 2682235
  have htrace : WordTrace (prefixWord ++ tailWord_2682235) baseStart_2682235 baseEnd_2682235 := by
    simpa [prefixWord, tailWord_2682235, baseEnd_2682235] using wordTrace_append hprefix tailTrace_2682235
  have hstable : (prefixWord ++ tailWord_2682235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682235).length < 2 ^ (prefixWord ++ tailWord_2682235).sum := by decide
  have hdescent : baseEnd_2682235 < baseStart_2682235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682252 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_2682252 : Nat := 118140960795 + 2682252 * 2 ^ 59
def prefixEnd_2682252 : Nat := 4983230072969 + 3 ^ 40 * 2682252 * 2
def baseEnd_2682252 : Nat := 918189674989029940276369

theorem tailTrace_2682252 : CollatzResearch.WordTrace tailWord_2682252 prefixEnd_2682252 918189674989029940276369 := by
  unfold tailWord_2682252
  simp only [CollatzResearch.WordTrace]
  refine ⟨48914883739333285508064505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65219844985777714010752673 48914883739333285508064505)
  ·
    refine ⟨36686162804499964131048379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48914883739333285508064505 36686162804499964131048379)
    ·
      refine ⟨55029244206749946196572569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36686162804499964131048379 55029244206749946196572569)
      ·
        refine ⟨41271933155062459647429427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55029244206749946196572569 41271933155062459647429427)
        ·
          refine ⟨61907899732593689471144141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41271933155062459647429427 61907899732593689471144141)
          ·
            refine ⟨23215462399722633551679053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61907899732593689471144141 23215462399722633551679053)
            ·
              refine ⟨8705798399895987581879645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23215462399722633551679053 8705798399895987581879645)
              ·
                refine ⟨3264674399960995343204867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8705798399895987581879645 3264674399960995343204867)
                ·
                  refine ⟨4897011599941493014807301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264674399960995343204867 4897011599941493014807301)
                  ·
                    refine ⟨918189674989029940276369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897011599941493014807301 918189674989029940276369)
                    ·
                      rfl

theorem cell22_2682252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_2682252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682252 prefixEnd_2682252 := by exact prefixLift 2682252
  have htrace : WordTrace (prefixWord ++ tailWord_2682252) baseStart_2682252 baseEnd_2682252 := by
    simpa [prefixWord, tailWord_2682252, baseEnd_2682252] using wordTrace_append hprefix tailTrace_2682252
  have hstable : (prefixWord ++ tailWord_2682252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682252).length < 2 ^ (prefixWord ++ tailWord_2682252).sum := by decide
  have hdescent : baseEnd_2682252 < baseStart_2682252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682295 : List Nat := [1, 1, 3, 1, 3, 2, 3, 8]
def baseStart_2682295 : Nat := 118140960795 + 2682295 * 2 ^ 59
def prefixEnd_2682295 : Nat := 4983230072969 + 3 ^ 40 * 2682295 * 2
def baseEnd_2682295 : Nat := 102022710529754684605693

theorem tailTrace_2682295 : CollatzResearch.WordTrace tailWord_2682295 prefixEnd_2682295 102022710529754684605693 := by
  unfold tailWord_2682295
  simp only [CollatzResearch.WordTrace]
  refine ⟨97831335817510789359944339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65220890545007192906629559 97831335817510789359944339)
  ·
    refine ⟨146747003726266184039916509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97831335817510789359944339 146747003726266184039916509)
    ·
      refine ⟨55030126397349819014968691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146747003726266184039916509 55030126397349819014968691)
      ·
        refine ⟨82545189596024728522453037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55030126397349819014968691 82545189596024728522453037)
        ·
          refine ⟨30954446098509273195919889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82545189596024728522453037 30954446098509273195919889)
          ·
            refine ⟨23215834573881954896939917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30954446098509273195919889 23215834573881954896939917)
            ·
              refine ⟨8705937965205733086352469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23215834573881954896939917 8705937965205733086352469)
              ·
                refine ⟨102022710529754684605693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8705937965205733086352469 102022710529754684605693)
                ·
                  rfl

theorem cell22_2682295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 8].length) (baseStart_2682295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682295 prefixEnd_2682295 := by exact prefixLift 2682295
  have htrace : WordTrace (prefixWord ++ tailWord_2682295) baseStart_2682295 baseEnd_2682295 := by
    simpa [prefixWord, tailWord_2682295, baseEnd_2682295] using wordTrace_append hprefix tailTrace_2682295
  have hstable : (prefixWord ++ tailWord_2682295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682295).length < 2 ^ (prefixWord ++ tailWord_2682295).sum := by decide
  have hdescent : baseEnd_2682295 < baseStart_2682295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682333 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2682333 : Nat := 118140960795 + 2682333 * 2 ^ 59
def prefixEnd_2682333 : Nat := 4983230072969 + 3 ^ 40 * 2682333 * 2
def baseEnd_2682333 : Nat := 918217402944372729001121

theorem tailTrace_2682333 : CollatzResearch.WordTrace tailWord_2682333 prefixEnd_2682333 918217402944372729001121 := by
  unfold tailWord_2682333
  simp only [CollatzResearch.WordTrace]
  refine ⟨97832721791373121849827653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65221814527582081233218435 97832721791373121849827653)
  ·
    refine ⟨18343635335882460346842685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97832721791373121849827653 18343635335882460346842685)
    ·
      refine ⟨6878863250955922630066007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18343635335882460346842685 6878863250955922630066007)
      ·
        refine ⟨10318294876433883945099011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6878863250955922630066007 10318294876433883945099011)
        ·
          refine ⟨15477442314650825917648517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10318294876433883945099011 15477442314650825917648517)
          ·
            refine ⟨2902020433997029859559097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15477442314650825917648517 2902020433997029859559097)
            ·
              refine ⟨2176515325497772394669323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902020433997029859559097 2176515325497772394669323)
              ·
                refine ⟨3264772988246658592003985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176515325497772394669323 3264772988246658592003985)
                ·
                  refine ⟨2448579741184993944002989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3264772988246658592003985 2448579741184993944002989)
                  ·
                    refine ⟨918217402944372729001121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448579741184993944002989 918217402944372729001121)
                    ·
                      rfl

theorem cell22_2682333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2682333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682333 prefixEnd_2682333 := by exact prefixLift 2682333
  have htrace : WordTrace (prefixWord ++ tailWord_2682333) baseStart_2682333 baseEnd_2682333 := by
    simpa [prefixWord, tailWord_2682333, baseEnd_2682333] using wordTrace_append hprefix tailTrace_2682333
  have hstable : (prefixWord ++ tailWord_2682333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682333).length < 2 ^ (prefixWord ++ tailWord_2682333).sum := by decide
  have hdescent : baseEnd_2682333 < baseStart_2682333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682355 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_2682355 : Nat := 118140960795 + 2682355 * 2 ^ 59
def prefixEnd_2682355 : Nat := 4983230072969 + 3 ^ 40 * 2682355 * 2
def baseEnd_2682355 : Nat := 918224933993972004951053

theorem tailTrace_2682355 : CollatzResearch.WordTrace tailWord_2682355 prefixEnd_2682355 918224933993972004951053 := by
  unfold tailWord_2682355
  simp only [CollatzResearch.WordTrace]
  refine ⟨97833524197293419607128519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65222349464862279738085679 97833524197293419607128519)
  ·
    refine ⟨146750286295940129410692779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97833524197293419607128519 146750286295940129410692779)
    ·
      refine ⟨220125429443910194116039169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146750286295940129410692779 220125429443910194116039169)
      ·
        refine ⟨165094072082932645587029377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220125429443910194116039169 165094072082932645587029377)
        ·
          refine ⟨123820554062199484190272033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165094072082932645587029377 123820554062199484190272033)
          ·
            refine ⟨92865415546649613142704025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123820554062199484190272033 92865415546649613142704025)
            ·
              refine ⟨69649061659987209857028019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92865415546649613142704025 69649061659987209857028019)
              ·
                refine ⟨104473592489980814785542029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69649061659987209857028019 104473592489980814785542029)
                ·
                  refine ⟨39177597183742805544578261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104473592489980814785542029 39177597183742805544578261)
                  ·
                    refine ⟨918224933993972004951053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39177597183742805544578261 918224933993972004951053)
                    ·
                      rfl

theorem cell22_2682355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_2682355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682355 prefixEnd_2682355 := by exact prefixLift 2682355
  have htrace : WordTrace (prefixWord ++ tailWord_2682355) baseStart_2682355 baseEnd_2682355 := by
    simpa [prefixWord, tailWord_2682355, baseEnd_2682355] using wordTrace_append hprefix tailTrace_2682355
  have hstable : (prefixWord ++ tailWord_2682355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682355).length < 2 ^ (prefixWord ++ tailWord_2682355).sum := by decide
  have hdescent : baseEnd_2682355 < baseStart_2682355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682378 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_2682378 : Nat := 118140960795 + 2682378 * 2 ^ 59
def prefixEnd_2682378 : Nat := 4983230072969 + 3 ^ 40 * 2682378 * 2
def baseEnd_2682378 : Nat := 918232807364007611625983

theorem tailTrace_2682378 : CollatzResearch.WordTrace tailWord_2682378 prefixEnd_2682378 918232807364007611625983 := by
  unfold tailWord_2682378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24458590769052523633803947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65222908717473396356810525 24458590769052523633803947)
  ·
    refine ⟨36687886153578785450705921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24458590769052523633803947 36687886153578785450705921)
    ·
      refine ⟨27515914615184089088029441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36687886153578785450705921 27515914615184089088029441)
      ·
        refine ⟨20636935961388066816022081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27515914615184089088029441 20636935961388066816022081)
        ·
          refine ⟨15477701971041050112016561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20636935961388066816022081 15477701971041050112016561)
          ·
            refine ⟨11608276478280787584012421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15477701971041050112016561 11608276478280787584012421)
            ·
              refine ⟨2176551839677647672002329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11608276478280787584012421 2176551839677647672002329)
              ·
                refine ⟨1632413879758235754001747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176551839677647672002329 1632413879758235754001747)
                ·
                  refine ⟨2448620819637353631002621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632413879758235754001747 2448620819637353631002621)
                  ·
                    refine ⟨918232807364007611625983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448620819637353631002621 918232807364007611625983)
                    ·
                      rfl

theorem cell22_2682378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_2682378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682378 prefixEnd_2682378 := by exact prefixLift 2682378
  have htrace : WordTrace (prefixWord ++ tailWord_2682378) baseStart_2682378 baseEnd_2682378 := by
    simpa [prefixWord, tailWord_2682378, baseEnd_2682378] using wordTrace_append hprefix tailTrace_2682378
  have hstable : (prefixWord ++ tailWord_2682378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682378).length < 2 ^ (prefixWord ++ tailWord_2682378).sum := by decide
  have hdescent : baseEnd_2682378 < baseStart_2682378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682387 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 3, 4]
def baseStart_2682387 : Nat := 118140960795 + 2682387 * 2 ^ 59
def prefixEnd_2682387 : Nat := 4983230072969 + 3 ^ 40 * 2682387 * 2
def baseEnd_2682387 : Nat := 918235888247934588150955

theorem tailTrace_2682387 : CollatzResearch.WordTrace tailWord_2682387 prefixEnd_2682387 918235888247934588150955 := by
  unfold tailWord_2682387
  simp only [CollatzResearch.WordTrace]
  refine ⟨97834691333177489072293415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65223127555451659381528943 97834691333177489072293415)
  ·
    refine ⟨146752036999766233608440123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97834691333177489072293415 146752036999766233608440123)
    ·
      refine ⟨220128055499649350412660185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146752036999766233608440123 220128055499649350412660185)
      ·
        refine ⟨165096041624737012809495139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220128055499649350412660185 165096041624737012809495139)
        ·
          refine ⟨247644062437105519214242709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165096041624737012809495139 247644062437105519214242709)
          ·
            refine ⟨11608315426739321213167627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 247644062437105519214242709 11608315426739321213167627)
            ·
              refine ⟨17412473140108981819751441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11608315426739321213167627 17412473140108981819751441)
              ·
                refine ⟨13059354855081736364813581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17412473140108981819751441 13059354855081736364813581)
                ·
                  refine ⟨4897258070655651136805093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13059354855081736364813581 4897258070655651136805093)
                  ·
                    refine ⟨918235888247934588150955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897258070655651136805093 918235888247934588150955)
                    ·
                      rfl

theorem cell22_2682387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_2682387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682387 prefixEnd_2682387 := by exact prefixLift 2682387
  have htrace : WordTrace (prefixWord ++ tailWord_2682387) baseStart_2682387 baseEnd_2682387 := by
    simpa [prefixWord, tailWord_2682387, baseEnd_2682387] using wordTrace_append hprefix tailTrace_2682387
  have hstable : (prefixWord ++ tailWord_2682387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682387).length < 2 ^ (prefixWord ++ tailWord_2682387).sum := by decide
  have hdescent : baseEnd_2682387 < baseStart_2682387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682402 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2682402 : Nat := 118140960795 + 2682402 * 2 ^ 59
def prefixEnd_2682402 : Nat := 4983230072969 + 3 ^ 40 * 2682402 * 2
def baseEnd_2682402 : Nat := 306080341018159849675303

theorem tailTrace_2682402 : CollatzResearch.WordTrace tailWord_2682402 prefixEnd_2682402 306080341018159849675303 := by
  unfold tailWord_2682402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24458809607030786658522365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65223492285415431089392973 24458809607030786658522365)
  ·
    refine ⟨9172053602636544996945887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24458809607030786658522365 9172053602636544996945887)
    ·
      refine ⟨13758080403954817495418831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9172053602636544996945887 13758080403954817495418831)
      ·
        refine ⟨20637120605932226243128247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13758080403954817495418831 20637120605932226243128247)
        ·
          refine ⟨30955680908898339364692371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20637120605932226243128247 30955680908898339364692371)
          ·
            refine ⟨46433521363347509047038557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30955680908898339364692371 46433521363347509047038557)
            ·
              refine ⟨17412570511255315892639459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46433521363347509047038557 17412570511255315892639459)
              ·
                refine ⟨26118855766882973838959189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17412570511255315892639459 26118855766882973838959189)
                ·
                  refine ⟨306080341018159849675303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26118855766882973838959189 306080341018159849675303)
                  ·
                    rfl

theorem cell22_2682402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2682402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682402 prefixEnd_2682402 := by exact prefixLift 2682402
  have htrace : WordTrace (prefixWord ++ tailWord_2682402) baseStart_2682402 baseEnd_2682402 := by
    simpa [prefixWord, tailWord_2682402, baseEnd_2682402] using wordTrace_append hprefix tailTrace_2682402
  have hstable : (prefixWord ++ tailWord_2682402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682402).length < 2 ^ (prefixWord ++ tailWord_2682402).sum := by decide
  have hdescent : baseEnd_2682402 < baseStart_2682402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682419 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 4]
def baseStart_2682419 : Nat := 118140960795 + 2682419 * 2 ^ 59
def prefixEnd_2682419 : Nat := 4983230072969 + 3 ^ 40 * 2682419 * 2
def baseEnd_2682419 : Nat := 306082280833965723783619

theorem tailTrace_2682419 : CollatzResearch.WordTrace tailWord_2682419 prefixEnd_2682419 306082280833965723783619 := by
  unfold tailWord_2682419
  simp only [CollatzResearch.WordTrace]
  refine ⟨97835858469061558537458311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65223905646041039024972207 97835858469061558537458311)
  ·
    refine ⟨146753787703592337806187467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97835858469061558537458311 146753787703592337806187467)
    ·
      refine ⟨220130681555388506709281201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146753787703592337806187467 220130681555388506709281201)
      ·
        refine ⟨165098011166541380031960901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220130681555388506709281201 165098011166541380031960901)
        ·
          refine ⟨30955877093726508755992669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165098011166541380031960901 30955877093726508755992669)
          ·
            refine ⟨11608453910147440783497251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30955877093726508755992669 11608453910147440783497251)
            ·
              refine ⟨17412680865221161175245877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11608453910147440783497251 17412680865221161175245877)
              ·
                refine ⟨1632438831114483860179301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17412680865221161175245877 1632438831114483860179301)
                ·
                  refine ⟨306082280833965723783619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632438831114483860179301 306082280833965723783619)
                  ·
                    rfl

theorem cell22_2682419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 4].length) (baseStart_2682419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682419 prefixEnd_2682419 := by exact prefixLift 2682419
  have htrace : WordTrace (prefixWord ++ tailWord_2682419) baseStart_2682419 baseEnd_2682419 := by
    simpa [prefixWord, tailWord_2682419, baseEnd_2682419] using wordTrace_append hprefix tailTrace_2682419
  have hstable : (prefixWord ++ tailWord_2682419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682419).length < 2 ^ (prefixWord ++ tailWord_2682419).sum := by decide
  have hdescent : baseEnd_2682419 < baseStart_2682419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682421 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2682421 : Nat := 118140960795 + 2682421 * 2 ^ 59
def prefixEnd_2682421 : Nat := 4983230072969 + 3 ^ 40 * 2682421 * 2
def baseEnd_2682421 : Nat := 918247527142769832800851

theorem tailTrace_2682421 : CollatzResearch.WordTrace tailWord_2682421 prefixEnd_2682421 918247527142769832800851 := by
  unfold tailWord_2682421
  simp only [CollatzResearch.WordTrace]
  refine ⟨97835931415054312879031117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65223954276702875252687411 97835931415054312879031117)
  ·
    refine ⟨36688474280645367329636669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97835931415054312879031117 36688474280645367329636669)
    ·
      refine ⟨13758177855242012748613751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36688474280645367329636669 13758177855242012748613751)
      ·
        refine ⟨20637266782863019122920627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13758177855242012748613751 20637266782863019122920627)
        ·
          refine ⟨30955900174294528684380941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20637266782863019122920627 30955900174294528684380941)
          ·
            refine ⟨11608462565360448256642853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30955900174294528684380941 11608462565360448256642853)
            ·
              refine ⟨2176586731005084048120535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11608462565360448256642853 2176586731005084048120535)
              ·
                refine ⟨3264880096507626072180803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176586731005084048120535 3264880096507626072180803)
                ·
                  refine ⟨4897320144761439108271205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264880096507626072180803 4897320144761439108271205)
                  ·
                    refine ⟨918247527142769832800851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897320144761439108271205 918247527142769832800851)
                    ·
                      rfl

theorem cell22_2682421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2682421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682421 prefixEnd_2682421 := by exact prefixLift 2682421
  have htrace : WordTrace (prefixWord ++ tailWord_2682421) baseStart_2682421 baseEnd_2682421 := by
    simpa [prefixWord, tailWord_2682421, baseEnd_2682421] using wordTrace_append hprefix tailTrace_2682421
  have hstable : (prefixWord ++ tailWord_2682421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682421).length < 2 ^ (prefixWord ++ tailWord_2682421).sum := by decide
  have hdescent : baseEnd_2682421 < baseStart_2682421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682432 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_2682432 : Nat := 118140960795 + 2682432 * 2 ^ 59
def prefixEnd_2682432 : Nat := 4983230072969 + 3 ^ 40 * 2682432 * 2
def baseEnd_2682432 : Nat := 918251292667569470775817

theorem tailTrace_2682432 : CollatzResearch.WordTrace tailWord_2682432 prefixEnd_2682432 918251292667569470775817 := by
  unfold tailWord_2682432
  simp only [CollatzResearch.WordTrace]
  refine ⟨48918166309007230878840775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65224221745342974505121033 48918166309007230878840775)
  ·
    refine ⟨73377249463510846318261163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48918166309007230878840775 73377249463510846318261163)
    ·
      refine ⟨110065874195266269477391745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73377249463510846318261163 110065874195266269477391745)
      ·
        refine ⟨82549405646449702108043809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110065874195266269477391745 82549405646449702108043809)
        ·
          refine ⟨61912054234837276581032857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82549405646449702108043809 61912054234837276581032857)
          ·
            refine ⟨46434040676127957435774643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61912054234837276581032857 46434040676127957435774643)
            ·
              refine ⟨69651061014191936153661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46434040676127957435774643 69651061014191936153661965)
              ·
                refine ⟨26119147880321976057623237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69651061014191936153661965 26119147880321976057623237)
                ·
                  refine ⟨4897340227560370510804357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26119147880321976057623237 4897340227560370510804357)
                  ·
                    refine ⟨918251292667569470775817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897340227560370510804357 918251292667569470775817)
                    ·
                      rfl

theorem cell22_2682432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_2682432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682432 prefixEnd_2682432 := by exact prefixLift 2682432
  have htrace : WordTrace (prefixWord ++ tailWord_2682432) baseStart_2682432 baseEnd_2682432 := by
    simpa [prefixWord, tailWord_2682432, baseEnd_2682432] using wordTrace_append hprefix tailTrace_2682432
  have hstable : (prefixWord ++ tailWord_2682432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682432).length < 2 ^ (prefixWord ++ tailWord_2682432).sum := by decide
  have hdescent : baseEnd_2682432 < baseStart_2682432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682507 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_2682507 : Nat := 118140960795 + 2682507 * 2 ^ 59
def prefixEnd_2682507 : Nat := 4983230072969 + 3 ^ 40 * 2682507 * 2
def baseEnd_2682507 : Nat := 918276966700294275150587

theorem tailTrace_2682507 : CollatzResearch.WordTrace tailWord_2682507 prefixEnd_2682507 918276966700294275150587 := by
  unfold tailWord_2682507
  simp only [CollatzResearch.WordTrace]
  refine ⟨97839068092742749566661775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65226045395161833044441183 97839068092742749566661775)
  ·
    refine ⟨146758602139114124349992663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97839068092742749566661775 146758602139114124349992663)
    ·
      refine ⟨220137903208671186524988995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146758602139114124349992663 220137903208671186524988995)
      ·
        refine ⟨330206854813006779787483493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220137903208671186524988995 330206854813006779787483493)
        ·
          refine ⟨61913785277438771210153155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330206854813006779787483493 61913785277438771210153155)
          ·
            refine ⟨92870677916158156815229733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61913785277438771210153155 92870677916158156815229733)
            ·
              refine ⟨17413252109279654402855575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92870677916158156815229733 17413252109279654402855575)
              ·
                refine ⟨26119878163919481604283363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17413252109279654402855575 26119878163919481604283363)
                ·
                  refine ⟨39179817245879222406425045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26119878163919481604283363 39179817245879222406425045)
                  ·
                    refine ⟨918276966700294275150587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39179817245879222406425045 918276966700294275150587)
                    ·
                      rfl

theorem cell22_2682507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_2682507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682507 prefixEnd_2682507 := by exact prefixLift 2682507
  have htrace : WordTrace (prefixWord ++ tailWord_2682507) baseStart_2682507 baseEnd_2682507 := by
    simpa [prefixWord, tailWord_2682507, baseEnd_2682507] using wordTrace_append hprefix tailTrace_2682507
  have hstable : (prefixWord ++ tailWord_2682507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682507).length < 2 ^ (prefixWord ++ tailWord_2682507).sum := by decide
  have hdescent : baseEnd_2682507 < baseStart_2682507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682573 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2682573 : Nat := 118140960795 + 2682573 * 2 ^ 59
def prefixEnd_2682573 : Nat := 4983230072969 + 3 ^ 40 * 2682573 * 2
def baseEnd_2682573 : Nat := 918299559849092103000385

theorem tailTrace_2682573 : CollatzResearch.WordTrace tailWord_2682573 prefixEnd_2682573 918299559849092103000385 := by
  unfold tailWord_2682573
  simp only [CollatzResearch.WordTrace]
  refine ⟨97841475310503642838564373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65227650207002428559042915 97841475310503642838564373)
  ·
    refine ⟨4586319155179858258057705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97841475310503642838564373 4586319155179858258057705)
    ·
      refine ⟨3439739366384893693543279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4586319155179858258057705 3439739366384893693543279)
      ·
        refine ⟨5159609049577340540314919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3439739366384893693543279 5159609049577340540314919)
        ·
          refine ⟨7739413574366010810472379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5159609049577340540314919 7739413574366010810472379)
          ·
            refine ⟨11609120361549016215708569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7739413574366010810472379 11609120361549016215708569)
            ·
              refine ⟨8706840271161762161781427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11609120361549016215708569 8706840271161762161781427)
              ·
                refine ⟨13060260406742643242672141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706840271161762161781427 13060260406742643242672141)
                ·
                  refine ⟨4897597652528491216002053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13060260406742643242672141 4897597652528491216002053)
                  ·
                    refine ⟨918299559849092103000385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897597652528491216002053 918299559849092103000385)
                    ·
                      rfl

theorem cell22_2682573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2682573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682573 prefixEnd_2682573 := by exact prefixLift 2682573
  have htrace : WordTrace (prefixWord ++ tailWord_2682573) baseStart_2682573 baseEnd_2682573 := by
    simpa [prefixWord, tailWord_2682573, baseEnd_2682573] using wordTrace_append hprefix tailTrace_2682573
  have hstable : (prefixWord ++ tailWord_2682573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682573).length < 2 ^ (prefixWord ++ tailWord_2682573).sum := by decide
  have hdescent : baseEnd_2682573 < baseStart_2682573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682584 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2682584 : Nat := 118140960795 + 2682584 * 2 ^ 59
def prefixEnd_2682584 : Nat := 4983230072969 + 3 ^ 40 * 2682584 * 2
def baseEnd_2682584 : Nat := 918303325373891740975351

theorem tailTrace_2682584 : CollatzResearch.WordTrace tailWord_2682584 prefixEnd_2682584 918303325373891740975351 := by
  unfold tailWord_2682584
  simp only [CollatzResearch.WordTrace]
  refine ⟨48920938256731895858607403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65227917675642527811476537 48920938256731895858607403)
  ·
    refine ⟨73381407385097843787911105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48920938256731895858607403 73381407385097843787911105)
    ·
      refine ⟨55036055538823382840933329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73381407385097843787911105 55036055538823382840933329)
      ·
        refine ⟨41277041654117537130699997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55036055538823382840933329 41277041654117537130699997)
        ·
          refine ⟨15478890620294076424012499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41277041654117537130699997 15478890620294076424012499)
          ·
            refine ⟨23218335930441114636018749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15478890620294076424012499 23218335930441114636018749)
            ·
              refine ⟨8706875973915417988507031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23218335930441114636018749 8706875973915417988507031)
              ·
                refine ⟨13060313960873126982760547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706875973915417988507031 13060313960873126982760547)
                ·
                  refine ⟨19590470941309690474140821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13060313960873126982760547 19590470941309690474140821)
                  ·
                    refine ⟨918303325373891740975351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19590470941309690474140821 918303325373891740975351)
                    ·
                      rfl

theorem cell22_2682584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2682584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682584 prefixEnd_2682584 := by exact prefixLift 2682584
  have htrace : WordTrace (prefixWord ++ tailWord_2682584) baseStart_2682584 baseEnd_2682584 := by
    simpa [prefixWord, tailWord_2682584, baseEnd_2682584] using wordTrace_append hprefix tailTrace_2682584
  have hstable : (prefixWord ++ tailWord_2682584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682584).length < 2 ^ (prefixWord ++ tailWord_2682584).sum := by decide
  have hdescent : baseEnd_2682584 < baseStart_2682584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682659 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_2682659 : Nat := 118140960795 + 2682659 * 2 ^ 59
def prefixEnd_2682659 : Nat := 4983230072969 + 3 ^ 40 * 2682659 * 2
def baseEnd_2682659 : Nat := 918328999406616545350121

theorem tailTrace_2682659 : CollatzResearch.WordTrace tailWord_2682659 prefixEnd_2682659 918328999406616545350121 := by
  unfold tailWord_2682659
  simp only [CollatzResearch.WordTrace]
  refine ⟨97844611988192079526195031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65229741325461386350796687 97844611988192079526195031)
  ·
    refine ⟨146766917982288119289292547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97844611988192079526195031 146766917982288119289292547)
    ·
      refine ⟨220150376973432178933938821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146766917982288119289292547 220150376973432178933938821)
      ·
        refine ⟨41278195682518533550113529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220150376973432178933938821 41278195682518533550113529)
        ·
          refine ⟨30958646761888900162585147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41278195682518533550113529 30958646761888900162585147)
          ·
            refine ⟨46437970142833350243877721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30958646761888900162585147 46437970142833350243877721)
            ·
              refine ⟨34828477607125012682908291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46437970142833350243877721 34828477607125012682908291)
              ·
                refine ⟨52242716410687519024362437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34828477607125012682908291 52242716410687519024362437)
                ·
                  refine ⟨9795509327003909817067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52242716410687519024362437 9795509327003909817067957)
                  ·
                    refine ⟨918328999406616545350121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9795509327003909817067957 918328999406616545350121)
                    ·
                      rfl

theorem cell22_2682659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_2682659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682659 prefixEnd_2682659 := by exact prefixLift 2682659
  have htrace : WordTrace (prefixWord ++ tailWord_2682659) baseStart_2682659 baseEnd_2682659 := by
    simpa [prefixWord, tailWord_2682659, baseEnd_2682659] using wordTrace_append hprefix tailTrace_2682659
  have hstable : (prefixWord ++ tailWord_2682659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682659).length < 2 ^ (prefixWord ++ tailWord_2682659).sum := by decide
  have hdescent : baseEnd_2682659 < baseStart_2682659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682691 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 3, 4]
def baseStart_2682691 : Nat := 118140960795 + 2682691 * 2 ^ 59
def prefixEnd_2682691 : Nat := 4983230072969 + 3 ^ 40 * 2682691 * 2
def baseEnd_2682691 : Nat := 918339953660579128550023

theorem tailTrace_2682691 : CollatzResearch.WordTrace tailWord_2682691 prefixEnd_2682691 918339953660579128550023 := by
  unfold tailWord_2682691
  simp only [CollatzResearch.WordTrace]
  refine ⟨97845779124076148991359927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65230519416050765994239951 97845779124076148991359927)
  ·
    refine ⟨146768668686114223487039891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97845779124076148991359927 146768668686114223487039891)
    ·
      refine ⟨220153003029171335230559837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146768668686114223487039891 220153003029171335230559837)
      ·
        refine ⟨82557376135939250711459939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220153003029171335230559837 82557376135939250711459939)
        ·
          refine ⟨123836064203908876067189909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82557376135939250711459939 123836064203908876067189909)
          ·
            refine ⟨5804815509558228565649527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123836064203908876067189909 5804815509558228565649527)
            ·
              refine ⟨8707223264337342848474291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5804815509558228565649527 8707223264337342848474291)
              ·
                refine ⟨13060834896506014272711437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8707223264337342848474291 13060834896506014272711437)
                ·
                  refine ⟨4897813086189755352266789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13060834896506014272711437 4897813086189755352266789)
                  ·
                    refine ⟨918339953660579128550023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897813086189755352266789 918339953660579128550023)
                    ·
                      rfl

theorem cell22_2682691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_2682691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682691 prefixEnd_2682691 := by exact prefixLift 2682691
  have htrace : WordTrace (prefixWord ++ tailWord_2682691) baseStart_2682691 baseEnd_2682691 := by
    simpa [prefixWord, tailWord_2682691, baseEnd_2682691] using wordTrace_append hprefix tailTrace_2682691
  have hstable : (prefixWord ++ tailWord_2682691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682691).length < 2 ^ (prefixWord ++ tailWord_2682691).sum := by decide
  have hdescent : baseEnd_2682691 < baseStart_2682691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682716 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2682716 : Nat := 118140960795 + 2682716 * 2 ^ 59
def prefixEnd_2682716 : Nat := 4983230072969 + 3 ^ 40 * 2682716 * 2
def baseEnd_2682716 : Nat := 918348511671487396674947

theorem tailTrace_2682716 : CollatzResearch.WordTrace tailWord_2682716 prefixEnd_2682716 918348511671487396674947 := by
  unfold tailWord_2682716
  simp only [CollatzResearch.WordTrace]
  refine ⟨48923345474492789130510001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65231127299323718840680001 48923345474492789130510001)
  ·
    refine ⟨36692509105869591847882501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48923345474492789130510001 36692509105869591847882501)
    ·
      refine ⟨6879845457350548471477969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36692509105869591847882501 6879845457350548471477969)
      ·
        refine ⟨5159884093012911353608477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6879845457350548471477969 5159884093012911353608477)
        ·
          refine ⟨1934956534879841757603179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5159884093012911353608477 1934956534879841757603179)
          ·
            refine ⟨2902434802319762636404769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934956534879841757603179 2902434802319762636404769)
            ·
              refine ⟨2176826101739821977303577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902434802319762636404769 2176826101739821977303577)
              ·
                refine ⟨1632619576304866482977683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176826101739821977303577 1632619576304866482977683)
                ·
                  refine ⟨2448929364457299724466525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632619576304866482977683 2448929364457299724466525)
                  ·
                    refine ⟨918348511671487396674947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448929364457299724466525 918348511671487396674947)
                    ·
                      rfl

theorem cell22_2682716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2682716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682716 prefixEnd_2682716 := by exact prefixLift 2682716
  have htrace : WordTrace (prefixWord ++ tailWord_2682716) baseStart_2682716 baseEnd_2682716 := by
    simpa [prefixWord, tailWord_2682716, baseEnd_2682716] using wordTrace_append hprefix tailTrace_2682716
  have hstable : (prefixWord ++ tailWord_2682716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682716).length < 2 ^ (prefixWord ++ tailWord_2682716).sum := by decide
  have hdescent : baseEnd_2682716 < baseStart_2682716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682772 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2682772 : Nat := 118140960795 + 2682772 * 2 ^ 59
def prefixEnd_2682772 : Nat := 4983230072969 + 3 ^ 40 * 2682772 * 2
def baseEnd_2682772 : Nat := 918367681615921917274775

theorem tailTrace_2682772 : CollatzResearch.WordTrace tailWord_2682772 prefixEnd_2682772 918367681615921917274775 := by
  unfold tailWord_2682772
  simp only [CollatzResearch.WordTrace]
  refine ⟨48924366718391349912529285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65232488957855133216705713 48924366718391349912529285)
  ·
    refine ⟨9173318759698378108599241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48924366718391349912529285 9173318759698378108599241)
    ·
      refine ⟨6879989069773783581449431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9173318759698378108599241 6879989069773783581449431)
      ·
        refine ⟨10319983604660675372174147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6879989069773783581449431 10319983604660675372174147)
        ·
          refine ⟨15479975406991013058261221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10319983604660675372174147 15479975406991013058261221)
          ·
            refine ⟨2902495388810814948423979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15479975406991013058261221 2902495388810814948423979)
            ·
              refine ⟨4353743083216222422635969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902495388810814948423979 4353743083216222422635969)
              ·
                refine ⟨3265307312412166816976977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4353743083216222422635969 3265307312412166816976977)
                ·
                  refine ⟨2448980484309125112732733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265307312412166816976977 2448980484309125112732733)
                  ·
                    refine ⟨918367681615921917274775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448980484309125112732733 918367681615921917274775)
                    ·
                      rfl

theorem cell22_2682772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2682772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682772 prefixEnd_2682772 := by exact prefixLift 2682772
  have htrace : WordTrace (prefixWord ++ tailWord_2682772) baseStart_2682772 baseEnd_2682772 := by
    simpa [prefixWord, tailWord_2682772, baseEnd_2682772] using wordTrace_append hprefix tailTrace_2682772
  have hstable : (prefixWord ++ tailWord_2682772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682772).length < 2 ^ (prefixWord ++ tailWord_2682772).sum := by decide
  have hdescent : baseEnd_2682772 < baseStart_2682772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682834 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_2682834 : Nat := 118140960795 + 2682834 * 2 ^ 59
def prefixEnd_2682834 : Nat := 4983230072969 + 3 ^ 40 * 2682834 * 2
def baseEnd_2682834 : Nat := 918388905482974422224585

theorem tailTrace_2682834 : CollatzResearch.WordTrace tailWord_2682834 prefixEnd_2682834 918388905482974422224585 := by
  unfold tailWord_2682834
  simp only [CollatzResearch.WordTrace]
  refine ⟨24462748690639521103453889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65233996508372056275877037 24462748690639521103453889)
  ·
    refine ⟨18347061517979640827590417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24462748690639521103453889 18347061517979640827590417)
    ·
      refine ⟨13760296138484730620692813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18347061517979640827590417 13760296138484730620692813)
      ·
        refine ⟨5160111051931773982759805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13760296138484730620692813 5160111051931773982759805)
        ·
          refine ⟨1935041644474415243534927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5160111051931773982759805 1935041644474415243534927)
          ·
            refine ⟨2902562466711622865302391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935041644474415243534927 2902562466711622865302391)
            ·
              refine ⟨4353843700067434297953587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902562466711622865302391 4353843700067434297953587)
              ·
                refine ⟨6530765550101151446930381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353843700067434297953587 6530765550101151446930381)
                ·
                  refine ⟨2449037081287931792598893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6530765550101151446930381 2449037081287931792598893)
                  ·
                    refine ⟨918388905482974422224585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449037081287931792598893 918388905482974422224585)
                    ·
                      rfl

theorem cell22_2682834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_2682834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682834 prefixEnd_2682834 := by exact prefixLift 2682834
  have htrace : WordTrace (prefixWord ++ tailWord_2682834) baseStart_2682834 baseEnd_2682834 := by
    simpa [prefixWord, tailWord_2682834, baseEnd_2682834] using wordTrace_append hprefix tailTrace_2682834
  have hstable : (prefixWord ++ tailWord_2682834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682834).length < 2 ^ (prefixWord ++ tailWord_2682834).sum := by decide
  have hdescent : baseEnd_2682834 < baseStart_2682834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682873 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_2682873 : Nat := 118140960795 + 2682873 * 2 ^ 59
def prefixEnd_2682873 : Nat := 4983230072969 + 3 ^ 40 * 2682873 * 2
def baseEnd_2682873 : Nat := 918402255979991320499465

theorem tailTrace_2682873 : CollatzResearch.WordTrace tailWord_2682873 prefixEnd_2682873 918402255979991320499465 := by
  unfold tailWord_2682873
  simp only [CollatzResearch.WordTrace]
  refine ⟨97852417209416794074485273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65234944806277862716323515 97852417209416794074485273)
  ·
    refine ⟨73389312907062595555863955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97852417209416794074485273 73389312907062595555863955)
    ·
      refine ⟨110083969360593893333795933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73389312907062595555863955 110083969360593893333795933)
      ·
        refine ⟨41281488510222710000173475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110083969360593893333795933 41281488510222710000173475)
        ·
          refine ⟨61922232765334065000260213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41281488510222710000173475 61922232765334065000260213)
          ·
            refine ⟨5805209321750068593774395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61922232765334065000260213 5805209321750068593774395)
            ·
              refine ⟨8707813982625102890661593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805209321750068593774395 8707813982625102890661593)
              ·
                refine ⟨6530860486968827167996195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8707813982625102890661593 6530860486968827167996195)
                ·
                  refine ⟨9796290730453240751994293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6530860486968827167996195 9796290730453240751994293)
                  ·
                    refine ⟨918402255979991320499465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9796290730453240751994293 918402255979991320499465)
                    ·
                      rfl

theorem cell22_2682873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_2682873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682873 prefixEnd_2682873 := by exact prefixLift 2682873
  have htrace : WordTrace (prefixWord ++ tailWord_2682873) baseStart_2682873 baseEnd_2682873 := by
    simpa [prefixWord, tailWord_2682873, baseEnd_2682873] using wordTrace_append hprefix tailTrace_2682873
  have hstable : (prefixWord ++ tailWord_2682873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682873).length < 2 ^ (prefixWord ++ tailWord_2682873).sum := by decide
  have hdescent : baseEnd_2682873 < baseStart_2682873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682888 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_2682888 : Nat := 118140960795 + 2682888 * 2 ^ 59
def prefixEnd_2682888 : Nat := 4983230072969 + 3 ^ 40 * 2682888 * 2
def baseEnd_2682888 : Nat := 918407390786536281374419

theorem tailTrace_2682888 : CollatzResearch.WordTrace tailWord_2682888 prefixEnd_2682888 918407390786536281374419 := by
  unfold tailWord_2682888
  simp only [CollatzResearch.WordTrace]
  refine ⟨48926482152181225818140659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65235309536241634424187545 48926482152181225818140659)
  ·
    refine ⟨73389723228271838727210989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48926482152181225818140659 73389723228271838727210989)
    ·
      refine ⟨27521146210601939522704121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73389723228271838727210989 27521146210601939522704121)
      ·
        refine ⟨20640859657951454642028091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27521146210601939522704121 20640859657951454642028091)
        ·
          refine ⟨30961289486927181963042137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20640859657951454642028091 30961289486927181963042137)
          ·
            refine ⟨23220967115195386472281603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30961289486927181963042137 23220967115195386472281603)
            ·
              refine ⟨34831450672793079708422405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23220967115195386472281603 34831450672793079708422405)
              ·
                refine ⟨6530897001148702445329201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34831450672793079708422405 6530897001148702445329201)
                ·
                  refine ⟨4898172750861526833996901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530897001148702445329201 4898172750861526833996901)
                  ·
                    refine ⟨918407390786536281374419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898172750861526833996901 918407390786536281374419)
                    ·
                      rfl

theorem cell22_2682888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_2682888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682888 prefixEnd_2682888 := by exact prefixLift 2682888
  have htrace : WordTrace (prefixWord ++ tailWord_2682888) baseStart_2682888 baseEnd_2682888 := by
    simpa [prefixWord, tailWord_2682888, baseEnd_2682888] using wordTrace_append hprefix tailTrace_2682888
  have hstable : (prefixWord ++ tailWord_2682888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682888).length < 2 ^ (prefixWord ++ tailWord_2682888).sum := by decide
  have hdescent : baseEnd_2682888 < baseStart_2682888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682922 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2682922 : Nat := 118140960795 + 2682922 * 2 ^ 59
def prefixEnd_2682922 : Nat := 4983230072969 + 3 ^ 40 * 2682922 * 2
def baseEnd_2682922 : Nat := 918419029681371526024315

theorem tailTrace_2682922 : CollatzResearch.WordTrace tailWord_2682922 prefixEnd_2682922 918419029681371526024315 := by
  unfold tailWord_2682922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24463551096559818860754755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65236136257492850295346013 24463551096559818860754755)
  ·
    refine ⟨36695326644839728291132133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24463551096559818860754755 36695326644839728291132133)
    ·
      refine ⟨6880373745907449054587275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36695326644839728291132133 6880373745907449054587275)
      ·
        refine ⟨10320560618861173581880913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880373745907449054587275 10320560618861173581880913)
        ·
          refine ⟨7740420464145880186410685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10320560618861173581880913 7740420464145880186410685)
          ·
            refine ⟨2902657674054705069904007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7740420464145880186410685 2902657674054705069904007)
            ·
              refine ⟨4353986511082057604856011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902657674054705069904007 4353986511082057604856011)
              ·
                refine ⟨6530979766623086407284017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353986511082057604856011 6530979766623086407284017)
                ·
                  refine ⟨4898234824967314805463013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530979766623086407284017 4898234824967314805463013)
                  ·
                    refine ⟨918419029681371526024315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898234824967314805463013 918419029681371526024315)
                    ·
                      rfl

theorem cell22_2682922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2682922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682922 prefixEnd_2682922 := by exact prefixLift 2682922
  have htrace : WordTrace (prefixWord ++ tailWord_2682922) baseStart_2682922 baseEnd_2682922 := by
    simpa [prefixWord, tailWord_2682922, baseEnd_2682922] using wordTrace_append hprefix tailTrace_2682922
  have hstable : (prefixWord ++ tailWord_2682922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682922).length < 2 ^ (prefixWord ++ tailWord_2682922).sum := by decide
  have hdescent : baseEnd_2682922 < baseStart_2682922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682986 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2682986 : Nat := 118140960795 + 2682986 * 2 ^ 59
def prefixEnd_2682986 : Nat := 4983230072969 + 3 ^ 40 * 2682986 * 2
def baseEnd_2682986 : Nat := 918440938189296692424119

theorem tailTrace_2682986 : CollatzResearch.WordTrace tailWord_2682986 prefixEnd_2682986 918440938189296692424119 := by
  unfold tailWord_2682986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464134664501853593337203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65237692438671609582232541 24464134664501853593337203)
  ·
    refine ⟨36696201996752780390005805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24464134664501853593337203 36696201996752780390005805)
    ·
      refine ⟨13761075748782292646252177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36696201996752780390005805 13761075748782292646252177)
      ·
        refine ⟨10320806811586719484689133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13761075748782292646252177 10320806811586719484689133)
        ·
          refine ⟨3870302554345019806758425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10320806811586719484689133 3870302554345019806758425)
          ·
            refine ⟨2902726915758764855068819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3870302554345019806758425 2902726915758764855068819)
            ·
              refine ⟨4354090373638147282603229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902726915758764855068819 4354090373638147282603229)
              ·
                refine ⟨1632783890114305230976211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4354090373638147282603229 1632783890114305230976211)
                ·
                  refine ⟨2449175835171457846464317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632783890114305230976211 2449175835171457846464317)
                  ·
                    refine ⟨918440938189296692424119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449175835171457846464317 918440938189296692424119)
                    ·
                      rfl

theorem cell22_2682986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2682986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2682986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2682986 prefixEnd_2682986 := by exact prefixLift 2682986
  have htrace : WordTrace (prefixWord ++ tailWord_2682986) baseStart_2682986 baseEnd_2682986 := by
    simpa [prefixWord, tailWord_2682986, baseEnd_2682986] using wordTrace_append hprefix tailTrace_2682986
  have hstable : (prefixWord ++ tailWord_2682986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682986).length < 2 ^ (prefixWord ++ tailWord_2682986).sum := by decide
  have hdescent : baseEnd_2682986 < baseStart_2682986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683040 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_2683040 : Nat := 118140960795 + 2683040 * 2 ^ 59
def prefixEnd_2683040 : Nat := 4983230072969 + 3 ^ 40 * 2683040 * 2
def baseEnd_2683040 : Nat := 918459423492858551573953

theorem tailTrace_2683040 : CollatzResearch.WordTrace tailWord_2683040 prefixEnd_2683040 918459423492858551573953 := by
  unfold tailWord_2683040
  simp only [CollatzResearch.WordTrace]
  refine ⟨48929254099905890797907287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65239005466541187730543049 48929254099905890797907287)
  ·
    refine ⟨73393881149858836196860931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48929254099905890797907287 73393881149858836196860931)
    ·
      refine ⟨110090821724788254295291397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73393881149858836196860931 110090821724788254295291397)
      ·
        refine ⟨20642029073397797680367137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110090821724788254295291397 20642029073397797680367137)
        ·
          refine ⟨15481521805048348260275353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20642029073397797680367137 15481521805048348260275353)
          ·
            refine ⟨11611141353786261195206515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15481521805048348260275353 11611141353786261195206515)
            ·
              refine ⟨17416712030679391792809773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11611141353786261195206515 17416712030679391792809773)
              ·
                refine ⟨6531267011504771922303665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17416712030679391792809773 6531267011504771922303665)
                ·
                  refine ⟨4898450258628578941727749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6531267011504771922303665 4898450258628578941727749)
                  ·
                    refine ⟨918459423492858551573953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898450258628578941727749 918459423492858551573953)
                    ·
                      rfl

theorem cell22_2683040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_2683040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683040 prefixEnd_2683040 := by exact prefixLift 2683040
  have htrace : WordTrace (prefixWord ++ tailWord_2683040) baseStart_2683040 baseEnd_2683040 := by
    simpa [prefixWord, tailWord_2683040, baseEnd_2683040] using wordTrace_append hprefix tailTrace_2683040
  have hstable : (prefixWord ++ tailWord_2683040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683040).length < 2 ^ (prefixWord ++ tailWord_2683040).sum := by decide
  have hdescent : baseEnd_2683040 < baseStart_2683040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683042 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2683042 : Nat := 118140960795 + 2683042 * 2 ^ 59
def prefixEnd_2683042 : Nat := 4983230072969 + 3 ^ 40 * 2683042 * 2
def baseEnd_2683042 : Nat := 918460108133731213023947

theorem tailTrace_2683042 : CollatzResearch.WordTrace tailWord_2683042 prefixEnd_2683042 918460108133731213023947 := by
  unfold tailWord_2683042
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464645286451133984346845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65239054097203023958258253 24464645286451133984346845)
  ·
    refine ⟨9174241982419175244130067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24464645286451133984346845 9174241982419175244130067)
    ·
      refine ⟨13761362973628762866195101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9174241982419175244130067 13761362973628762866195101)
      ·
        refine ⟨5160511115110786074823163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13761362973628762866195101 5160511115110786074823163)
        ·
          refine ⟨7740766672666179112234745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5160511115110786074823163 7740766672666179112234745)
          ·
            refine ⟨5805575004499634334176059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7740766672666179112234745 5805575004499634334176059)
            ·
              refine ⟨8708362506749451501264089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805575004499634334176059 8708362506749451501264089)
              ·
                refine ⟨6531271880062088625948067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8708362506749451501264089 6531271880062088625948067)
                ·
                  refine ⟨9796907820093132938922101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6531271880062088625948067 9796907820093132938922101)
                  ·
                    refine ⟨918460108133731213023947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9796907820093132938922101 918460108133731213023947)
                    ·
                      rfl

theorem cell22_2683042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2683042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683042 prefixEnd_2683042 := by exact prefixLift 2683042
  have htrace : WordTrace (prefixWord ++ tailWord_2683042) baseStart_2683042 baseEnd_2683042 := by
    simpa [prefixWord, tailWord_2683042, baseEnd_2683042] using wordTrace_append hprefix tailTrace_2683042
  have hstable : (prefixWord ++ tailWord_2683042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683042).length < 2 ^ (prefixWord ++ tailWord_2683042).sum := by decide
  have hdescent : baseEnd_2683042 < baseStart_2683042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683104 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 1, 3]
def baseStart_2683104 : Nat := 118140960795 + 2683104 * 2 ^ 59
def prefixEnd_2683104 : Nat := 4983230072969 + 3 ^ 40 * 2683104 * 2
def baseEnd_2683104 : Nat := 918481332000783717973757

theorem tailTrace_2683104 : CollatzResearch.WordTrace tailWord_2683104 prefixEnd_2683104 918481332000783717973757 := by
  unfold tailWord_2683104
  simp only [CollatzResearch.WordTrace]
  refine ⟨48930421235789960263072183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65240561647719947017429577 48930421235789960263072183)
  ·
    refine ⟨73395631853684940394608275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48930421235789960263072183 73395631853684940394608275)
    ·
      refine ⟨110093447780527410591912413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73395631853684940394608275 110093447780527410591912413)
      ·
        refine ⟨41285042917697778971967155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110093447780527410591912413 41285042917697778971967155)
        ·
          refine ⟨61927564376546668457950733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41285042917697778971967155 61927564376546668457950733)
          ·
            refine ⟨23222836641205000671731525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61927564376546668457950733 23222836641205000671731525)
            ·
              refine ⟨4354281870225937625949661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23222836641205000671731525 4354281870225937625949661)
              ·
                refine ⟨1632855701334726609731123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4354281870225937625949661 1632855701334726609731123)
                ·
                  refine ⟨2449283552002089914596685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632855701334726609731123 2449283552002089914596685)
                  ·
                    refine ⟨918481332000783717973757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449283552002089914596685 918481332000783717973757)
                    ·
                      rfl

theorem cell22_2683104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_2683104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683104 prefixEnd_2683104 := by exact prefixLift 2683104
  have htrace : WordTrace (prefixWord ++ tailWord_2683104) baseStart_2683104 baseEnd_2683104 := by
    simpa [prefixWord, tailWord_2683104, baseEnd_2683104] using wordTrace_append hprefix tailTrace_2683104
  have hstable : (prefixWord ++ tailWord_2683104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683104).length < 2 ^ (prefixWord ++ tailWord_2683104).sum := by decide
  have hdescent : baseEnd_2683104 < baseStart_2683104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683117 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2683117 : Nat := 118140960795 + 2683117 * 2 ^ 59
def prefixEnd_2683117 : Nat := 4983230072969 + 3 ^ 40 * 2683117 * 2
def baseEnd_2683117 : Nat := 306161927388818672466239

theorem tailTrace_2683117 : CollatzResearch.WordTrace tailWord_2683117 prefixEnd_2683117 306161927388818672466239 := by
  unfold tailWord_2683117
  simp only [CollatzResearch.WordTrace]
  refine ⟨97861316620532823746367605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65240877747021882497578403 97861316620532823746367605)
  ·
    refine ⟨9174498433174952226221963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97861316620532823746367605 9174498433174952226221963)
    ·
      refine ⟨13761747649762428339332945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9174498433174952226221963 13761747649762428339332945)
      ·
        refine ⟨10321310737321821254499709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13761747649762428339332945 10321310737321821254499709)
        ·
          refine ⟨3870491526495682970437391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10321310737321821254499709 3870491526495682970437391)
          ·
            refine ⟨5805737289743524455656087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870491526495682970437391 5805737289743524455656087)
            ·
              refine ⟨8708605934615286683484131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805737289743524455656087 8708605934615286683484131)
              ·
                refine ⟨13062908901922930025226197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8708605934615286683484131 13062908901922930025226197)
                ·
                  refine ⟨306161927388818672466239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13062908901922930025226197 306161927388818672466239)
                  ·
                    rfl

theorem cell22_2683117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2683117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683117 prefixEnd_2683117 := by exact prefixLift 2683117
  have htrace : WordTrace (prefixWord ++ tailWord_2683117) baseStart_2683117 baseEnd_2683117 := by
    simpa [prefixWord, tailWord_2683117, baseEnd_2683117] using wordTrace_append hprefix tailTrace_2683117
  have hstable : (prefixWord ++ tailWord_2683117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683117).length < 2 ^ (prefixWord ++ tailWord_2683117).sum := by decide
  have hdescent : baseEnd_2683117 < baseStart_2683117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683134 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2683134 : Nat := 118140960795 + 2683134 * 2 ^ 59
def prefixEnd_2683134 : Nat := 4983230072969 + 3 ^ 40 * 2683134 * 2
def baseEnd_2683134 : Nat := 306163867204624546574555

theorem tailTrace_2683134 : CollatzResearch.WordTrace tailWord_2683134 prefixEnd_2683134 306163867204624546574555 := by
  unfold tailWord_2683134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12232742082683904456217057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65241291107647490433157637 12232742082683904456217057)
  ·
    refine ⟨9174556562012928342162793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12232742082683904456217057 9174556562012928342162793)
    ·
      refine ⟨6880917421509696256622095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9174556562012928342162793 6880917421509696256622095)
      ·
        refine ⟨10321376132264544384933143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880917421509696256622095 10321376132264544384933143)
        ·
          refine ⟨15482064198396816577399715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10321376132264544384933143 15482064198396816577399715)
          ·
            refine ⟨23223096297595224866099573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15482064198396816577399715 23223096297595224866099573)
            ·
              refine ⟨2177165277899552331196835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23223096297595224866099573 2177165277899552331196835)
              ·
                refine ⟨3265747916849328496795253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177165277899552331196835 3265747916849328496795253)
                ·
                  refine ⟨306163867204624546574555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3265747916849328496795253 306163867204624546574555)
                  ·
                    rfl

theorem cell22_2683134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2683134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683134 prefixEnd_2683134 := by exact prefixLift 2683134
  have htrace : WordTrace (prefixWord ++ tailWord_2683134) baseStart_2683134 baseEnd_2683134 := by
    simpa [prefixWord, tailWord_2683134, baseEnd_2683134] using wordTrace_append hprefix tailTrace_2683134
  have hstable : (prefixWord ++ tailWord_2683134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683134).length < 2 ^ (prefixWord ++ tailWord_2683134).sum := by decide
  have hdescent : baseEnd_2683134 < baseStart_2683134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683145 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 6]
def baseStart_2683145 : Nat := 118140960795 + 2683145 * 2 ^ 59
def prefixEnd_2683145 : Nat := 4983230072969 + 3 ^ 40 * 2683145 * 2
def baseEnd_2683145 : Nat := 306165122379557759232877

theorem tailTrace_2683145 : CollatzResearch.WordTrace tailWord_2683145 prefixEnd_2683145 306165122379557759232877 := by
  unfold tailWord_2683145
  simp only [CollatzResearch.WordTrace]
  refine ⟨97862337864431384528386889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65241558576287589685591259 97862337864431384528386889)
  ·
    refine ⟨73396753398323538396290167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97862337864431384528386889 73396753398323538396290167)
    ·
      refine ⟨110095130097485307594435251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73396753398323538396290167 110095130097485307594435251)
      ·
        refine ⟨165142695146227961391652877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110095130097485307594435251 165142695146227961391652877)
        ·
          refine ⟨61928510679835485521869829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165142695146227961391652877 61928510679835485521869829)
          ·
            refine ⟨11611595752469153535350593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61928510679835485521869829 11611595752469153535350593)
            ·
              refine ⟨8708696814351865151512945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11611595752469153535350593 8708696814351865151512945)
              ·
                refine ⟨6531522610763898863634709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8708696814351865151512945 6531522610763898863634709)
                ·
                  refine ⟨306165122379557759232877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6531522610763898863634709 306165122379557759232877)
                  ·
                    rfl

theorem cell22_2683145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_2683145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683145 prefixEnd_2683145 := by exact prefixLift 2683145
  have htrace : WordTrace (prefixWord ++ tailWord_2683145) baseStart_2683145 baseEnd_2683145 := by
    simpa [prefixWord, tailWord_2683145, baseEnd_2683145] using wordTrace_append hprefix tailTrace_2683145
  have hstable : (prefixWord ++ tailWord_2683145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683145).length < 2 ^ (prefixWord ++ tailWord_2683145).sum := by decide
  have hdescent : baseEnd_2683145 < baseStart_2683145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683147 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 1, 4]
def baseStart_2683147 : Nat := 118140960795 + 2683147 * 2 ^ 59
def prefixEnd_2683147 : Nat := 4983230072969 + 3 ^ 40 * 2683147 * 2
def baseEnd_2683147 : Nat := 918496051779545939148625

theorem tailTrace_2683147 : CollatzResearch.WordTrace tailWord_2683147 prefixEnd_2683147 918496051779545939148625 := by
  unfold tailWord_2683147
  simp only [CollatzResearch.WordTrace]
  refine ⟨97862410810424138869959695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65241607206949425913306463 97862410810424138869959695)
  ·
    refine ⟨146793616215636208304939543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97862410810424138869959695 146793616215636208304939543)
    ·
      refine ⟨220190424323454312457409315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146793616215636208304939543 220190424323454312457409315)
      ·
        refine ⟨330285636485181468686113973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220190424323454312457409315 330285636485181468686113973)
        ·
          refine ⟨30964278420485762689323185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330285636485181468686113973 30964278420485762689323185)
          ·
            refine ⟨23223208815364322016992389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30964278420485762689323185 23223208815364322016992389)
            ·
              refine ⟨4354351652880810378186073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23223208815364322016992389 4354351652880810378186073)
              ·
                refine ⟨3265763739660607783639555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354351652880810378186073 3265763739660607783639555)
                ·
                  refine ⟨4898645609490911675459333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265763739660607783639555 4898645609490911675459333)
                  ·
                    refine ⟨918496051779545939148625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898645609490911675459333 918496051779545939148625)
                    ·
                      rfl

theorem cell22_2683147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 4].length) (baseStart_2683147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683147 prefixEnd_2683147 := by exact prefixLift 2683147
  have htrace : WordTrace (prefixWord ++ tailWord_2683147) baseStart_2683147 baseEnd_2683147 := by
    simpa [prefixWord, tailWord_2683147, baseEnd_2683147] using wordTrace_append hprefix tailTrace_2683147
  have hstable : (prefixWord ++ tailWord_2683147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683147).length < 2 ^ (prefixWord ++ tailWord_2683147).sum := by decide
  have hdescent : baseEnd_2683147 < baseStart_2683147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683160 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2683160 : Nat := 118140960795 + 2683160 * 2 ^ 59
def prefixEnd_2683160 : Nat := 4983230072969 + 3 ^ 40 * 2683160 * 2
def baseEnd_2683160 : Nat := 918500501945218238573585

theorem tailTrace_2683160 : CollatzResearch.WordTrace tailWord_2683160 prefixEnd_2683160 918500501945218238573585 := by
  unfold tailWord_2683160
  simp only [CollatzResearch.WordTrace]
  refine ⟨48931442479688521045091467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65241923306251361393455289 48931442479688521045091467)
  ·
    refine ⟨73397163719532781567637201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48931442479688521045091467 73397163719532781567637201)
    ·
      refine ⟨55047872789649586175727901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73397163719532781567637201 55047872789649586175727901)
      ·
        refine ⟨20642952296118594815897963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55047872789649586175727901 20642952296118594815897963)
        ·
          refine ⟨30964428444177892223846945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20642952296118594815897963 30964428444177892223846945)
          ·
            refine ⟨23223321333133419167885209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30964428444177892223846945 23223321333133419167885209)
            ·
              refine ⟨17417490999850064375913907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23223321333133419167885209 17417490999850064375913907)
              ·
                refine ⟨26126236499775096563870861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17417490999850064375913907 26126236499775096563870861)
                ·
                  refine ⟨9797338687415661211451573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26126236499775096563870861 9797338687415661211451573)
                  ·
                    refine ⟨918500501945218238573585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9797338687415661211451573 918500501945218238573585)
                    ·
                      rfl

theorem cell22_2683160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2683160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683160 prefixEnd_2683160 := by exact prefixLift 2683160
  have htrace : WordTrace (prefixWord ++ tailWord_2683160) baseStart_2683160 baseEnd_2683160 := by
    simpa [prefixWord, tailWord_2683160, baseEnd_2683160] using wordTrace_append hprefix tailTrace_2683160
  have hstable : (prefixWord ++ tailWord_2683160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683160).length < 2 ^ (prefixWord ++ tailWord_2683160).sum := by decide
  have hdescent : baseEnd_2683160 < baseStart_2683160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683194 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_2683194 : Nat := 118140960795 + 2683194 * 2 ^ 59
def prefixEnd_2683194 : Nat := 4983230072969 + 3 ^ 40 * 2683194 * 2
def baseEnd_2683194 : Nat := 918512140840053483223481

theorem tailTrace_2683194 : CollatzResearch.WordTrace tailWord_2683194 prefixEnd_2683194 918512140840053483223481 := by
  unfold tailWord_2683194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24466031260313466474230159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65242750027502577264613757 24466031260313466474230159)
  ·
    refine ⟨36699046890470199711345239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24466031260313466474230159 36699046890470199711345239)
    ·
      refine ⟨55048570335705299567017859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36699046890470199711345239 55048570335705299567017859)
      ·
        refine ⟨82572855503557949350526789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55048570335705299567017859 82572855503557949350526789)
        ·
          refine ⟨15482410406917115503223773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82572855503557949350526789 15482410406917115503223773)
          ·
            refine ⟨5805903902593918313708915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15482410406917115503223773 5805903902593918313708915)
            ·
              refine ⟨8708855853890877470563373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805903902593918313708915 8708855853890877470563373)
              ·
                refine ⟨3265820945209079051461265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8708855853890877470563373 3265820945209079051461265)
                ·
                  refine ⟨2449365708906809288595949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265820945209079051461265 2449365708906809288595949)
                  ·
                    refine ⟨918512140840053483223481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449365708906809288595949 918512140840053483223481)
                    ·
                      rfl

theorem cell22_2683194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_2683194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683194 prefixEnd_2683194 := by exact prefixLift 2683194
  have htrace : WordTrace (prefixWord ++ tailWord_2683194) baseStart_2683194 baseEnd_2683194 := by
    simpa [prefixWord, tailWord_2683194, baseEnd_2683194] using wordTrace_append hprefix tailTrace_2683194
  have hstable : (prefixWord ++ tailWord_2683194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683194).length < 2 ^ (prefixWord ++ tailWord_2683194).sum := by decide
  have hdescent : baseEnd_2683194 < baseStart_2683194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683228 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2683228 : Nat := 118140960795 + 2683228 * 2 ^ 59
def prefixEnd_2683228 : Nat := 4983230072969 + 3 ^ 40 * 2683228 * 2
def baseEnd_2683228 : Nat := 918523779734888727873377

theorem tailTrace_2683228 : CollatzResearch.WordTrace tailWord_2683228 prefixEnd_2683228 918523779734888727873377 := by
  unfold tailWord_2683228
  simp only [CollatzResearch.WordTrace]
  refine ⟨48932682561565344851829169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65243576748753793135772225 48932682561565344851829169)
  ·
    refine ⟨36699511921174008638871877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48932682561565344851829169 36699511921174008638871877)
    ·
      refine ⟨6881158485220126619788477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36699511921174008638871877 6881158485220126619788477)
      ·
        refine ⟨2580434431957547482420679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6881158485220126619788477 2580434431957547482420679)
        ·
          refine ⟨3870651647936321223631019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580434431957547482420679 3870651647936321223631019)
          ·
            refine ⟨5805977471904481835446529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870651647936321223631019 5805977471904481835446529)
            ·
              refine ⟨4354483103928361376584897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805977471904481835446529 4354483103928361376584897)
              ·
                refine ⟨3265862327946271032438673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354483103928361376584897 3265862327946271032438673)
                ·
                  refine ⟨2449396745959703274329005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265862327946271032438673 2449396745959703274329005)
                  ·
                    refine ⟨918523779734888727873377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449396745959703274329005 918523779734888727873377)
                    ·
                      rfl

theorem cell22_2683228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2683228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683228 prefixEnd_2683228 := by exact prefixLift 2683228
  have htrace : WordTrace (prefixWord ++ tailWord_2683228) baseStart_2683228 baseEnd_2683228 := by
    simpa [prefixWord, tailWord_2683228, baseEnd_2683228] using wordTrace_append hprefix tailTrace_2683228
  have hstable : (prefixWord ++ tailWord_2683228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683228).length < 2 ^ (prefixWord ++ tailWord_2683228).sum := by decide
  have hdescent : baseEnd_2683228 < baseStart_2683228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683348 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2683348 : Nat := 118140960795 + 2683348 * 2 ^ 59
def prefixEnd_2683348 : Nat := 4983230072969 + 3 ^ 40 * 2683348 * 2
def baseEnd_2683348 : Nat := 306188286062416138291003

theorem tailTrace_2683348 : CollatzResearch.WordTrace tailWord_2683348 prefixEnd_2683348 306188286062416138291003 := by
  unfold tailWord_2683348
  simp only [CollatzResearch.WordTrace]
  refine ⟨48934870941347975099013349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65246494588463966798684465 48934870941347975099013349)
  ·
    refine ⟨9175288301502745331065003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48934870941347975099013349 9175288301502745331065003)
    ·
      refine ⟨13762932452254117996597505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9175288301502745331065003 13762932452254117996597505)
      ·
        refine ⟨10322199339190588497448129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13762932452254117996597505 10322199339190588497448129)
        ·
          refine ⟨7741649504392941373086097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10322199339190588497448129 7741649504392941373086097)
          ·
            refine ⟨5806237128294706029814573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7741649504392941373086097 5806237128294706029814573)
            ·
              refine ⟨2177338923110514761180465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5806237128294706029814573 2177338923110514761180465)
              ·
                refine ⟨1633004192332886070885349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177338923110514761180465 1633004192332886070885349)
                ·
                  refine ⟨306188286062416138291003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633004192332886070885349 306188286062416138291003)
                  ·
                    rfl

theorem cell22_2683348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2683348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683348 prefixEnd_2683348 := by exact prefixLift 2683348
  have htrace : WordTrace (prefixWord ++ tailWord_2683348) baseStart_2683348 baseEnd_2683348 := by
    simpa [prefixWord, tailWord_2683348, baseEnd_2683348] using wordTrace_append hprefix tailTrace_2683348
  have hstable : (prefixWord ++ tailWord_2683348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683348).length < 2 ^ (prefixWord ++ tailWord_2683348).sum := by decide
  have hdescent : baseEnd_2683348 < baseStart_2683348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683391 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 1, 3]
def baseStart_2683391 : Nat := 118140960795 + 2683391 * 2 ^ 59
def prefixEnd_2683391 : Nat := 4983230072969 + 3 ^ 40 * 2683391 * 2
def baseEnd_2683391 : Nat := 918579577966010636047877

theorem tailTrace_2683391 : CollatzResearch.WordTrace tailWord_2683391 prefixEnd_2683391 918579577966010636047877 := by
  unfold tailWord_2683391
  simp only [CollatzResearch.WordTrace]
  refine ⟨97871310221540168541842027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65247540147693445694561351 97871310221540168541842027)
  ·
    refine ⟨146806965332310252812763041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97871310221540168541842027 146806965332310252812763041)
    ·
      refine ⟨110105223999232689609572281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146806965332310252812763041 110105223999232689609572281)
      ·
        refine ⟨82578917999424517207179211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110105223999232689609572281 82578917999424517207179211)
        ·
          refine ⟨123868376999136775810768817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82578917999424517207179211 123868376999136775810768817)
          ·
            refine ⟨92901282749352581858076613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123868376999136775810768817 92901282749352581858076613)
            ·
              refine ⟨17418990515503609098389365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92901282749352581858076613 17418990515503609098389365)
              ·
                refine ⟨1633030360828463352974003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17418990515503609098389365 1633030360828463352974003)
                ·
                  refine ⟨2449545541242695029461005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633030360828463352974003 2449545541242695029461005)
                  ·
                    refine ⟨918579577966010636047877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449545541242695029461005 918579577966010636047877)
                    ·
                      rfl

theorem cell22_2683391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_2683391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683391 prefixEnd_2683391 := by exact prefixLift 2683391
  have htrace : WordTrace (prefixWord ++ tailWord_2683391) baseStart_2683391 baseEnd_2683391 := by
    simpa [prefixWord, tailWord_2683391, baseEnd_2683391] using wordTrace_append hprefix tailTrace_2683391
  have hstable : (prefixWord ++ tailWord_2683391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683391).length < 2 ^ (prefixWord ++ tailWord_2683391).sum := by decide
  have hdescent : baseEnd_2683391 < baseStart_2683391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683404 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_2683404 : Nat := 118140960795 + 2683404 * 2 ^ 59
def prefixEnd_2683404 : Nat := 4983230072969 + 3 ^ 40 * 2683404 * 2
def baseEnd_2683404 : Nat := 306194676043894311824279

theorem tailTrace_2683404 : CollatzResearch.WordTrace tailWord_2683404 prefixEnd_2683404 306194676043894311824279 := by
  unfold tailWord_2683404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48935892185246535881032633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65247856246995381174710177 48935892185246535881032633)
  ·
    refine ⟨36701919138934901910774475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48935892185246535881032633 36701919138934901910774475)
    ·
      refine ⟨55052878708402352866161713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36701919138934901910774475 55052878708402352866161713)
      ·
        refine ⟨41289659031301764649621285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55052878708402352866161713 41289659031301764649621285)
        ·
          refine ⟨7741811068369080871803991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41289659031301764649621285 7741811068369080871803991)
          ·
            refine ⟨11612716602553621307705987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7741811068369080871803991 11612716602553621307705987)
            ·
              refine ⟨17419074903830431961558981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612716602553621307705987 17419074903830431961558981)
              ·
                refine ⟨3266076544468205992792309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17419074903830431961558981 3266076544468205992792309)
                ·
                  refine ⟨306194676043894311824279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266076544468205992792309 306194676043894311824279)
                  ·
                    rfl

theorem cell22_2683404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_2683404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683404 prefixEnd_2683404 := by exact prefixLift 2683404
  have htrace : WordTrace (prefixWord ++ tailWord_2683404) baseStart_2683404 baseEnd_2683404 := by
    simpa [prefixWord, tailWord_2683404, baseEnd_2683404] using wordTrace_append hprefix tailTrace_2683404
  have hstable : (prefixWord ++ tailWord_2683404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683404).length < 2 ^ (prefixWord ++ tailWord_2683404).sum := by decide
  have hdescent : baseEnd_2683404 < baseStart_2683404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683466 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_2683466 : Nat := 118140960795 + 2683466 * 2 ^ 59
def prefixEnd_2683466 : Nat := 4983230072969 + 3 ^ 40 * 2683466 * 2
def baseEnd_2683466 : Nat := 306201750666245146807549

theorem tailTrace_2683466 : CollatzResearch.WordTrace tailWord_2683466 prefixEnd_2683466 306201750666245146807549 := by
  unfold tailWord_2683466
  simp only [CollatzResearch.WordTrace]
  refine ⟨24468511424067114087705563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65249363797512304233881501 24468511424067114087705563)
  ·
    refine ⟨36702767136100671131558345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24468511424067114087705563 36702767136100671131558345)
    ·
      refine ⟨27527075352075503348668759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36702767136100671131558345 27527075352075503348668759)
      ·
        refine ⟨41290613028113255023003139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27527075352075503348668759 41290613028113255023003139)
        ·
          refine ⟨61935919542169882534504709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41290613028113255023003139 61935919542169882534504709)
          ·
            refine ⟨11612984914156852975219633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61935919542169882534504709 11612984914156852975219633)
            ·
              refine ⟨8709738685617639731414725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11612984914156852975219633 8709738685617639731414725)
              ·
                refine ⟨1633076003553307449640261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8709738685617639731414725 1633076003553307449640261)
                ·
                  refine ⟨306201750666245146807549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633076003553307449640261 306201750666245146807549)
                  ·
                    rfl

theorem cell22_2683466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_2683466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683466 prefixEnd_2683466 := by exact prefixLift 2683466
  have htrace : WordTrace (prefixWord ++ tailWord_2683466) baseStart_2683466 baseEnd_2683466 := by
    simpa [prefixWord, tailWord_2683466, baseEnd_2683466] using wordTrace_append hprefix tailTrace_2683466
  have hstable : (prefixWord ++ tailWord_2683466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683466).length < 2 ^ (prefixWord ++ tailWord_2683466).sum := by decide
  have hdescent : baseEnd_2683466 < baseStart_2683466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683539 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 5]
def baseStart_2683539 : Nat := 118140960795 + 2683539 * 2 ^ 59
def prefixEnd_2683539 : Nat := 4983230072969 + 3 ^ 40 * 2683539 * 2
def baseEnd_2683539 : Nat := 306210080463529194449141

theorem tailTrace_2683539 : CollatzResearch.WordTrace tailWord_2683539 prefixEnd_2683539 306210080463529194449141 := by
  unfold tailWord_2683539
  simp only [CollatzResearch.WordTrace]
  refine ⟨97876708225003989818229671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65251138816669326545486447 97876708225003989818229671)
  ·
    refine ⟨146815062337505984727344507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97876708225003989818229671 146815062337505984727344507)
    ·
      refine ⟨220222593506258977091016761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146815062337505984727344507 220222593506258977091016761)
      ·
        refine ⟨165166945129694232818262571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220222593506258977091016761 165166945129694232818262571)
        ·
          refine ⟨247750417694541349227393857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165166945129694232818262571 247750417694541349227393857)
          ·
            refine ⟨185812813270906011920545393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247750417694541349227393857 185812813270906011920545393)
            ·
              refine ⟨139359609953179508940409045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185812813270906011920545393 139359609953179508940409045)
              ·
                refine ⟨3266240858277644740790837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 139359609953179508940409045 3266240858277644740790837)
                ·
                  refine ⟨306210080463529194449141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266240858277644740790837 306210080463529194449141)
                  ·
                    rfl

theorem cell22_2683539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 5].length) (baseStart_2683539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683539 prefixEnd_2683539 := by exact prefixLift 2683539
  have htrace : WordTrace (prefixWord ++ tailWord_2683539) baseStart_2683539 baseEnd_2683539 := by
    simpa [prefixWord, tailWord_2683539, baseEnd_2683539] using wordTrace_append hprefix tailTrace_2683539
  have hstable : (prefixWord ++ tailWord_2683539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683539).length < 2 ^ (prefixWord ++ tailWord_2683539).sum := by decide
  have hdescent : baseEnd_2683539 < baseStart_2683539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683573 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 5]
def baseStart_2683573 : Nat := 118140960795 + 2683573 * 2 ^ 59
def prefixEnd_2683573 : Nat := 4983230072969 + 3 ^ 40 * 2683573 * 2
def baseEnd_2683573 : Nat := 306213960095140942665773

theorem tailTrace_2683573 : CollatzResearch.WordTrace tailWord_2683573 prefixEnd_2683573 306213960095140942665773 := by
  unfold tailWord_2683573
  simp only [CollatzResearch.WordTrace]
  refine ⟨97877948306880813624967373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65251965537920542416644915 97877948306880813624967373)
  ·
    refine ⟨36704230615080305109362765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97877948306880813624967373 36704230615080305109362765)
    ·
      refine ⟨13764086480655114416011037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36704230615080305109362765 13764086480655114416011037)
      ·
        refine ⟨5161532430245667906004139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13764086480655114416011037 5161532430245667906004139)
        ·
          refine ⟨7742298645368501859006209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161532430245667906004139 7742298645368501859006209)
          ·
            refine ⟨5806723984026376394254657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7742298645368501859006209 5806723984026376394254657)
            ·
              refine ⟨4355042988019782295690993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5806723984026376394254657 4355042988019782295690993)
              ·
                refine ⟨3266282241014836721768245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355042988019782295690993 3266282241014836721768245)
                ·
                  refine ⟨306213960095140942665773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266282241014836721768245 306213960095140942665773)
                  ·
                    rfl

theorem cell22_2683573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_2683573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683573 prefixEnd_2683573 := by exact prefixLift 2683573
  have htrace : WordTrace (prefixWord ++ tailWord_2683573) baseStart_2683573 baseEnd_2683573 := by
    simpa [prefixWord, tailWord_2683573, baseEnd_2683573] using wordTrace_append hprefix tailTrace_2683573
  have hstable : (prefixWord ++ tailWord_2683573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683573).length < 2 ^ (prefixWord ++ tailWord_2683573).sum := by decide
  have hdescent : baseEnd_2683573 < baseStart_2683573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683616 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_2683616 : Nat := 118140960795 + 2683616 * 2 ^ 59
def prefixEnd_2683616 : Nat := 4983230072969 + 3 ^ 40 * 2683616 * 2
def baseEnd_2683616 : Nat := 918656600064185049172187

theorem tailTrace_2683616 : CollatzResearch.WordTrace tailWord_2683616 prefixEnd_2683616 918656600064185049172187 := by
  unfold tailWord_2683616
  simp only [CollatzResearch.WordTrace]
  refine ⟨48939758322862515984391351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65253011097150021312521801 48939758322862515984391351)
  ·
    refine ⟨73409637484293773976587027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48939758322862515984391351 73409637484293773976587027)
    ·
      refine ⟨110114456226440660964880541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73409637484293773976587027 110114456226440660964880541)
      ·
        refine ⟨41292921084915247861830203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110114456226440660964880541 41292921084915247861830203)
        ·
          refine ⟨61939381627372871792745305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41292921084915247861830203 61939381627372871792745305)
          ·
            refine ⟨46454536220529653844558979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61939381627372871792745305 46454536220529653844558979)
            ·
              refine ⟨69681804330794480766838469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46454536220529653844558979 69681804330794480766838469)
              ·
                refine ⟨13065338312023965143782213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69681804330794480766838469 13065338312023965143782213)
                ·
                  refine ⟨2449750933504493464459165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13065338312023965143782213 2449750933504493464459165)
                  ·
                    refine ⟨918656600064185049172187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449750933504493464459165 918656600064185049172187)
                    ·
                      rfl

theorem cell22_2683616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_2683616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683616 prefixEnd_2683616 := by exact prefixLift 2683616
  have htrace : WordTrace (prefixWord ++ tailWord_2683616) baseStart_2683616 baseEnd_2683616 := by
    simpa [prefixWord, tailWord_2683616, baseEnd_2683616] using wordTrace_append hprefix tailTrace_2683616
  have hstable : (prefixWord ++ tailWord_2683616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683616).length < 2 ^ (prefixWord ++ tailWord_2683616).sum := by decide
  have hdescent : baseEnd_2683616 < baseStart_2683616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683620 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_2683620 : Nat := 118140960795 + 2683620 * 2 ^ 59
def prefixEnd_2683620 : Nat := 4983230072969 + 3 ^ 40 * 2683620 * 2
def baseEnd_2683620 : Nat := 918657969345930372072175

theorem tailTrace_2683620 : CollatzResearch.WordTrace tailWord_2683620 prefixEnd_2683620 918657969345930372072175 := by
  unfold tailWord_2683620
  simp only [CollatzResearch.WordTrace]
  refine ⟨48939831268855270325964157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65253108358473693767952209 48939831268855270325964157)
  ·
    refine ⟨18352436725820726372236559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48939831268855270325964157 18352436725820726372236559)
    ·
      refine ⟨27528655088731089558354839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18352436725820726372236559 27528655088731089558354839)
      ·
        refine ⟨41292982633096634337532259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27528655088731089558354839 41292982633096634337532259)
        ·
          refine ⟨61939473949644951506298389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41292982633096634337532259 61939473949644951506298389)
          ·
            refine ⟨2903412841389607101857737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61939473949644951506298389 2903412841389607101857737)
            ·
              refine ⟨2177559631042205326393303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2903412841389607101857737 2177559631042205326393303)
              ·
                refine ⟨3266339446563307989589955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177559631042205326393303 3266339446563307989589955)
                ·
                  refine ⟨4899509169844961984384933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266339446563307989589955 4899509169844961984384933)
                  ·
                    refine ⟨918657969345930372072175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4899509169844961984384933 918657969345930372072175)
                    ·
                      rfl

theorem cell22_2683620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_2683620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683620 prefixEnd_2683620 := by exact prefixLift 2683620
  have htrace : WordTrace (prefixWord ++ tailWord_2683620) baseStart_2683620 baseEnd_2683620 := by
    simpa [prefixWord, tailWord_2683620, baseEnd_2683620] using wordTrace_append hprefix tailTrace_2683620
  have hstable : (prefixWord ++ tailWord_2683620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683620).length < 2 ^ (prefixWord ++ tailWord_2683620).sum := by decide
  have hdescent : baseEnd_2683620 < baseStart_2683620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683650 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2683650 : Nat := 118140960795 + 2683650 * 2 ^ 59
def prefixEnd_2683650 : Nat := 4983230072969 + 3 ^ 40 * 2683650 * 2
def baseEnd_2683650 : Nat := 918668238959020293822083

theorem tailTrace_2683650 : CollatzResearch.WordTrace tailWord_2683650 prefixEnd_2683650 918668238959020293822083 := by
  unfold tailWord_2683650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24470189181900463943880101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65253837818401237183680269 24470189181900463943880101)
  ·
    refine ⟨4588160471606336989477519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24470189181900463943880101 4588160471606336989477519)
    ·
      refine ⟨6882240707409505484216279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4588160471606336989477519 6882240707409505484216279)
      ·
        refine ⟨10323361061114258226324419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882240707409505484216279 10323361061114258226324419)
        ·
          refine ⟨15485041591671387339486629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10323361061114258226324419 15485041591671387339486629)
          ·
            refine ⟨2903445298438385126153743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15485041591671387339486629 2903445298438385126153743)
            ·
              refine ⟨4355167947657577689230615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903445298438385126153743 4355167947657577689230615)
              ·
                refine ⟨6532751921486366533845923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4355167947657577689230615 6532751921486366533845923)
                ·
                  refine ⟨9799127882229549800768885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6532751921486366533845923 9799127882229549800768885)
                  ·
                    refine ⟨918668238959020293822083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9799127882229549800768885 918668238959020293822083)
                    ·
                      rfl

theorem cell22_2683650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2683650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683650 prefixEnd_2683650 := by exact prefixLift 2683650
  have htrace : WordTrace (prefixWord ++ tailWord_2683650) baseStart_2683650 baseEnd_2683650 := by
    simpa [prefixWord, tailWord_2683650, baseEnd_2683650] using wordTrace_append hprefix tailTrace_2683650
  have hstable : (prefixWord ++ tailWord_2683650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683650).length < 2 ^ (prefixWord ++ tailWord_2683650).sum := by decide
  have hdescent : baseEnd_2683650 < baseStart_2683650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683746 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2683746 : Nat := 118140960795 + 2683746 * 2 ^ 59
def prefixEnd_2683746 : Nat := 4983230072969 + 3 ^ 40 * 2683746 * 2
def baseEnd_2683746 : Nat := 918701101720908043421789

theorem tailTrace_2683746 : CollatzResearch.WordTrace tailWord_2683746 prefixEnd_2683746 918701101720908043421789 := by
  unfold tailWord_2683746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24471064533813516042753773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65256172090169376114010061 24471064533813516042753773)
  ·
    refine ⟨9176649200180068516032665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24471064533813516042753773 9176649200180068516032665)
    ·
      refine ⟨6882486900135051387024499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9176649200180068516032665 6882486900135051387024499)
      ·
        refine ⟨10323730350202577080536749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882486900135051387024499 10323730350202577080536749)
        ·
          refine ⟨3871398881325966405201281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10323730350202577080536749 3871398881325966405201281)
          ·
            refine ⟨2903549160994474803900961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3871398881325966405201281 2903549160994474803900961)
            ·
              refine ⟨2177661870745856102925721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2903549160994474803900961 2177661870745856102925721)
              ·
                refine ⟨1633246403059392077194291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177661870745856102925721 1633246403059392077194291)
                ·
                  refine ⟨2449869604589088115791437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633246403059392077194291 2449869604589088115791437)
                  ·
                    refine ⟨918701101720908043421789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449869604589088115791437 918701101720908043421789)
                    ·
                      rfl

theorem cell22_2683746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2683746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683746 prefixEnd_2683746 := by exact prefixLift 2683746
  have htrace : WordTrace (prefixWord ++ tailWord_2683746) baseStart_2683746 baseEnd_2683746 := by
    simpa [prefixWord, tailWord_2683746, baseEnd_2683746] using wordTrace_append hprefix tailTrace_2683746
  have hstable : (prefixWord ++ tailWord_2683746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683746).length < 2 ^ (prefixWord ++ tailWord_2683746).sum := by decide
  have hdescent : baseEnd_2683746 < baseStart_2683746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683783 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2683783 : Nat := 118140960795 + 2683783 * 2 ^ 59
def prefixEnd_2683783 : Nat := 4983230072969 + 3 ^ 40 * 2683783 * 2
def baseEnd_2683783 : Nat := 918713767577052280246675

theorem tailTrace_2683783 : CollatzResearch.WordTrace tailWord_2683783 prefixEnd_2683783 918713767577052280246675 := by
  unfold tailWord_2683783
  simp only [CollatzResearch.WordTrace]
  refine ⟨97885607636120019490112003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65257071757413346326741335 97885607636120019490112003)
  ·
    refine ⟨146828411454180029235168005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97885607636120019490112003 146828411454180029235168005)
    ·
      refine ⟨27530327147658755481594001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146828411454180029235168005 27530327147658755481594001)
      ·
        refine ⟨20647745360744066611195501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27530327147658755481594001 20647745360744066611195501)
        ·
          refine ⟨7742904510279024979198313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20647745360744066611195501 7742904510279024979198313)
          ·
            refine ⟨5807178382709268734398735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7742904510279024979198313 5807178382709268734398735)
            ·
              refine ⟨8710767574063903101598103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807178382709268734398735 8710767574063903101598103)
              ·
                refine ⟨13066151361095854652397155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8710767574063903101598103 13066151361095854652397155)
                ·
                  refine ⟨19599227041643781978595733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13066151361095854652397155 19599227041643781978595733)
                  ·
                    refine ⟨918713767577052280246675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19599227041643781978595733 918713767577052280246675)
                    ·
                      rfl

theorem cell22_2683783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2683783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683783 prefixEnd_2683783 := by exact prefixLift 2683783
  have htrace : WordTrace (prefixWord ++ tailWord_2683783) baseStart_2683783 baseEnd_2683783 := by
    simpa [prefixWord, tailWord_2683783, baseEnd_2683783] using wordTrace_append hprefix tailTrace_2683783
  have hstable : (prefixWord ++ tailWord_2683783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683783).length < 2 ^ (prefixWord ++ tailWord_2683783).sum := by decide
  have hdescent : baseEnd_2683783 < baseStart_2683783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683811 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_2683811 : Nat := 118140960795 + 2683811 * 2 ^ 59
def prefixEnd_2683811 : Nat := 4983230072969 + 3 ^ 40 * 2683811 * 2
def baseEnd_2683811 : Nat := 918723352549269540546589

theorem tailTrace_2683811 : CollatzResearch.WordTrace tailWord_2683811 prefixEnd_2683811 918723352549269540546589 := by
  unfold tailWord_2683811
  simp only [CollatzResearch.WordTrace]
  refine ⟨97886628880018580272131287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65257752586679053514754191 97886628880018580272131287)
  ·
    refine ⟨146829943320027870408196931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97886628880018580272131287 146829943320027870408196931)
    ·
      refine ⟨220244914980041805612295397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146829943320027870408196931 220244914980041805612295397)
      ·
        refine ⟨41295921558757838552305387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220244914980041805612295397 41295921558757838552305387)
        ·
          refine ⟨61943882338136757828458081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41295921558757838552305387 61943882338136757828458081)
          ·
            refine ⟨46457911753602568371343561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61943882338136757828458081 46457911753602568371343561)
            ·
              refine ⟨34843433815201926278507671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46457911753602568371343561 34843433815201926278507671)
              ·
                refine ⟨52265150722802889417761507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34843433815201926278507671 52265150722802889417761507)
                ·
                  refine ⟨78397726084204334126642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52265150722802889417761507 78397726084204334126642261)
                  ·
                    refine ⟨918723352549269540546589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78397726084204334126642261 918723352549269540546589)
                    ·
                      rfl

theorem cell22_2683811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_2683811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683811 prefixEnd_2683811 := by exact prefixLift 2683811
  have htrace : WordTrace (prefixWord ++ tailWord_2683811) baseStart_2683811 baseEnd_2683811 := by
    simpa [prefixWord, tailWord_2683811, baseEnd_2683811] using wordTrace_append hprefix tailTrace_2683811
  have hstable : (prefixWord ++ tailWord_2683811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683811).length < 2 ^ (prefixWord ++ tailWord_2683811).sum := by decide
  have hdescent : baseEnd_2683811 < baseStart_2683811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683847 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 1, 3]
def baseStart_2683847 : Nat := 118140960795 + 2683847 * 2 ^ 59
def prefixEnd_2683847 : Nat := 4983230072969 + 3 ^ 40 * 2683847 * 2
def baseEnd_2683847 : Nat := 918735676084977446646479

theorem tailTrace_2683847 : CollatzResearch.WordTrace tailWord_2683847 prefixEnd_2683847 918735676084977446646479 := by
  unfold tailWord_2683847
  simp only [CollatzResearch.WordTrace]
  refine ⟨97887941907888158420441795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65258627938592105613627863 97887941907888158420441795)
  ·
    refine ⟨146831912861832237630662693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97887941907888158420441795 146831912861832237630662693)
    ·
      refine ⟨27530983661593544555749255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146831912861832237630662693 27530983661593544555749255)
      ·
        refine ⟨41296475492390316833623883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27530983661593544555749255 41296475492390316833623883)
        ·
          refine ⟨61944713238585475250435825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41296475492390316833623883 61944713238585475250435825)
          ·
            refine ⟨46458534928939106437826869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61944713238585475250435825 46458534928939106437826869)
            ·
              refine ⟨4355487649588041228546269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46458534928939106437826869 4355487649588041228546269)
              ·
                refine ⟨1633307868595515460704851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4355487649588041228546269 1633307868595515460704851)
                ·
                  refine ⟨2449961802893273191057277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633307868595515460704851 2449961802893273191057277)
                  ·
                    refine ⟨918735676084977446646479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449961802893273191057277 918735676084977446646479)
                    ·
                      rfl

theorem cell22_2683847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_2683847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683847 prefixEnd_2683847 := by exact prefixLift 2683847
  have htrace : WordTrace (prefixWord ++ tailWord_2683847) baseStart_2683847 baseEnd_2683847 := by
    simpa [prefixWord, tailWord_2683847, baseEnd_2683847] using wordTrace_append hprefix tailTrace_2683847
  have hstable : (prefixWord ++ tailWord_2683847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683847).length < 2 ^ (prefixWord ++ tailWord_2683847).sum := by decide
  have hdescent : baseEnd_2683847 < baseStart_2683847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683864 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 1, 3]
def baseStart_2683864 : Nat := 118140960795 + 2683864 * 2 ^ 59
def prefixEnd_2683864 : Nat := 4983230072969 + 3 ^ 40 * 2683864 * 2
def baseEnd_2683864 : Nat := 918741495532395068971427

theorem tailTrace_2683864 : CollatzResearch.WordTrace tailWord_2683864 prefixEnd_2683864 918741495532395068971427 := by
  unfold tailWord_2683864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48944280974413285161905323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65259041299217713549207097 48944280974413285161905323)
  ·
    refine ⟨73416421461619927742857985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48944280974413285161905323 73416421461619927742857985)
    ·
      refine ⟨55062316096214945807143489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73416421461619927742857985 55062316096214945807143489)
      ·
        refine ⟨41296737072161209355357617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55062316096214945807143489 41296737072161209355357617)
        ·
          refine ⟨30972552804120907016518213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41296737072161209355357617 30972552804120907016518213)
          ·
            refine ⟨5807353650772670065597165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30972552804120907016518213 5807353650772670065597165)
            ·
              refine ⟨2177757619039751274598937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5807353650772670065597165 2177757619039751274598937)
              ·
                refine ⟨1633318214279813455949203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177757619039751274598937 1633318214279813455949203)
                ·
                  refine ⟨2449977321419720183923805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633318214279813455949203 2449977321419720183923805)
                  ·
                    refine ⟨918741495532395068971427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449977321419720183923805 918741495532395068971427)
                    ·
                      rfl

theorem cell22_2683864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_2683864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683864 prefixEnd_2683864 := by exact prefixLift 2683864
  have htrace : WordTrace (prefixWord ++ tailWord_2683864) baseStart_2683864 baseEnd_2683864 := by
    simpa [prefixWord, tailWord_2683864, baseEnd_2683864] using wordTrace_append hprefix tailTrace_2683864
  have hstable : (prefixWord ++ tailWord_2683864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683864).length < 2 ^ (prefixWord ++ tailWord_2683864).sum := by decide
  have hdescent : baseEnd_2683864 < baseStart_2683864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683873 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2683873 : Nat := 118140960795 + 2683873 * 2 ^ 59
def prefixEnd_2683873 : Nat := 4983230072969 + 3 ^ 40 * 2683873 * 2
def baseEnd_2683873 : Nat := 918744576416322045496399

theorem tailTrace_2683873 : CollatzResearch.WordTrace tailWord_2683873 prefixEnd_2683873 918744576416322045496399 := by
  unfold tailWord_2683873
  simp only [CollatzResearch.WordTrace]
  refine ⟨97888890205793964860888273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65259260137195976573925515 97888890205793964860888273)
  ·
    refine ⟨73416667654345473645666205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97888890205793964860888273 73416667654345473645666205)
    ·
      refine ⟨27531250370379552617124827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73416667654345473645666205 27531250370379552617124827)
      ·
        refine ⟨41296875555569328925687241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27531250370379552617124827 41296875555569328925687241)
        ·
          refine ⟨30972656666676996694265431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41296875555569328925687241 30972656666676996694265431)
          ·
            refine ⟨46458985000015495041398147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30972656666676996694265431 46458985000015495041398147)
            ·
              refine ⟨69688477500023242562097221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46458985000015495041398147 69688477500023242562097221)
              ·
                refine ⟨13066589531254357980393229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69688477500023242562097221 13066589531254357980393229)
                ·
                  refine ⟨4899971074220384242647461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13066589531254357980393229 4899971074220384242647461)
                  ·
                    refine ⟨918744576416322045496399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4899971074220384242647461 918744576416322045496399)
                    ·
                      rfl

theorem cell22_2683873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2683873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683873 prefixEnd_2683873 := by exact prefixLift 2683873
  have htrace : WordTrace (prefixWord ++ tailWord_2683873) baseStart_2683873 baseEnd_2683873 := by
    simpa [prefixWord, tailWord_2683873, baseEnd_2683873] using wordTrace_append hprefix tailTrace_2683873
  have hstable : (prefixWord ++ tailWord_2683873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683873).length < 2 ^ (prefixWord ++ tailWord_2683873).sum := by decide
  have hdescent : baseEnd_2683873 < baseStart_2683873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683877 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 5]
def baseStart_2683877 : Nat := 118140960795 + 2683877 * 2 ^ 59
def prefixEnd_2683877 : Nat := 4983230072969 + 3 ^ 40 * 2683877 * 2
def baseEnd_2683877 : Nat := 306248648566022456132129

theorem tailTrace_2683877 : CollatzResearch.WordTrace tailWord_2683877 prefixEnd_2683877 306248648566022456132129 := by
  unfold tailWord_2683877
  simp only [CollatzResearch.WordTrace]
  refine ⟨97889036097779473544033885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65259357398519649029355923 97889036097779473544033885)
  ·
    refine ⟨36708388536667302579012707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97889036097779473544033885 36708388536667302579012707)
    ·
      refine ⟨55062582805000953868519061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36708388536667302579012707 55062582805000953868519061)
      ·
        refine ⟨2581058568984419712586831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55062582805000953868519061 2581058568984419712586831)
        ·
          refine ⟨3871587853476629568880247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581058568984419712586831 3871587853476629568880247)
          ·
            refine ⟨5807381780214944353320371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871587853476629568880247 5807381780214944353320371)
            ·
              refine ⟨8711072670322416529980557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807381780214944353320371 8711072670322416529980557)
              ·
                refine ⟨3266652251370906198742709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8711072670322416529980557 3266652251370906198742709)
                ·
                  refine ⟨306248648566022456132129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266652251370906198742709 306248648566022456132129)
                  ·
                    rfl

theorem cell22_2683877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_2683877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683877 prefixEnd_2683877 := by exact prefixLift 2683877
  have htrace : WordTrace (prefixWord ++ tailWord_2683877) baseStart_2683877 baseEnd_2683877 := by
    simpa [prefixWord, tailWord_2683877, baseEnd_2683877] using wordTrace_append hprefix tailTrace_2683877
  have hstable : (prefixWord ++ tailWord_2683877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683877).length < 2 ^ (prefixWord ++ tailWord_2683877).sum := by decide
  have hdescent : baseEnd_2683877 < baseStart_2683877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683937 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_2683937 : Nat := 118140960795 + 2683937 * 2 ^ 59
def prefixEnd_2683937 : Nat := 4983230072969 + 3 ^ 40 * 2683937 * 2
def baseEnd_2683937 : Nat := 918766484924247211896203

theorem tailTrace_2683937 : CollatzResearch.WordTrace tailWord_2683937 prefixEnd_2683937 918766484924247211896203 := by
  unfold tailWord_2683937
  simp only [CollatzResearch.WordTrace]
  refine ⟨97891224477562103791218065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65260816318374735860812043 97891224477562103791218065)
  ·
    refine ⟨73418418358171577843413549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97891224477562103791218065 73418418358171577843413549)
    ·
      refine ⟨27531906884314341691280081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73418418358171577843413549 27531906884314341691280081)
      ·
        refine ⟨20648930163235756268460061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27531906884314341691280081 20648930163235756268460061)
        ·
          refine ⟨7743348811213408600672523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20648930163235756268460061 7743348811213408600672523)
          ·
            refine ⟨11615023216820112901008785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743348811213408600672523 11615023216820112901008785)
            ·
              refine ⟨8711267412615084675756589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11615023216820112901008785 8711267412615084675756589)
              ·
                refine ⟨3266725279730656753408721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8711267412615084675756589 3266725279730656753408721)
                ·
                  refine ⟨2450043959797992565056541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3266725279730656753408721 2450043959797992565056541)
                  ·
                    refine ⟨918766484924247211896203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2450043959797992565056541 918766484924247211896203)
                    ·
                      rfl

theorem cell22_2683937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_2683937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683937 prefixEnd_2683937 := by exact prefixLift 2683937
  have htrace : WordTrace (prefixWord ++ tailWord_2683937) baseStart_2683937 baseEnd_2683937 := by
    simpa [prefixWord, tailWord_2683937, baseEnd_2683937] using wordTrace_append hprefix tailTrace_2683937
  have hstable : (prefixWord ++ tailWord_2683937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683937).length < 2 ^ (prefixWord ++ tailWord_2683937).sum := by decide
  have hdescent : baseEnd_2683937 < baseStart_2683937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683982 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_2683982 : Nat := 118140960795 + 2683982 * 2 ^ 59
def prefixEnd_2683982 : Nat := 4983230072969 + 3 ^ 40 * 2683982 * 2
def baseEnd_2683982 : Nat := 918781889343882094521065

theorem tailTrace_2683982 : CollatzResearch.WordTrace tailWord_2683982 prefixEnd_2683982 918781889343882094521065 := by
  unfold tailWord_2683982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12236608220299884559575775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65261910508266050984404133 12236608220299884559575775)
  ·
    refine ⟨18354912330449826839363663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12236608220299884559575775 18354912330449826839363663)
    ·
      refine ⟨27532368495674740259045495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18354912330449826839363663 27532368495674740259045495)
      ·
        refine ⟨41298552743512110388568243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27532368495674740259045495 41298552743512110388568243)
        ·
          refine ⟨61947829115268165582852365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41298552743512110388568243 61947829115268165582852365)
          ·
            refine ⟨23230435918225562093569637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61947829115268165582852365 23230435918225562093569637)
            ·
              refine ⟨4355706734667292892544307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23230435918225562093569637 4355706734667292892544307)
              ·
                refine ⟨6533560102000939338816461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4355706734667292892544307 6533560102000939338816461)
                ·
                  refine ⟨2450085038250352252056173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6533560102000939338816461 2450085038250352252056173)
                  ·
                    refine ⟨918781889343882094521065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2450085038250352252056173 918781889343882094521065)
                    ·
                      rfl

theorem cell22_2683982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_2683982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683982 prefixEnd_2683982 := by exact prefixLift 2683982
  have htrace : WordTrace (prefixWord ++ tailWord_2683982) baseStart_2683982 baseEnd_2683982 := by
    simpa [prefixWord, tailWord_2683982, baseEnd_2683982] using wordTrace_append hprefix tailTrace_2683982
  have hstable : (prefixWord ++ tailWord_2683982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683982).length < 2 ^ (prefixWord ++ tailWord_2683982).sum := by decide
  have hdescent : baseEnd_2683982 < baseStart_2683982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683993 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_2683993 : Nat := 118140960795 + 2683993 * 2 ^ 59
def prefixEnd_2683993 : Nat := 4983230072969 + 3 ^ 40 * 2683993 * 2
def baseEnd_2683993 : Nat := 918785654868681732496031

theorem tailTrace_2683993 : CollatzResearch.WordTrace tailWord_2683993 prefixEnd_2683993 918785654868681732496031 := by
  unfold tailWord_2683993
  simp only [CollatzResearch.WordTrace]
  refine ⟨97893266965359225355256633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65262177976906150236837755 97893266965359225355256633)
  ·
    refine ⟨73419950224019419016442475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97893266965359225355256633 73419950224019419016442475)
    ·
      refine ⟨110129925336029128524663713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73419950224019419016442475 110129925336029128524663713)
      ·
        refine ⟨82597444002021846393497785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110129925336029128524663713 82597444002021846393497785)
        ·
          refine ⟨61948083001516384795123339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82597444002021846393497785 61948083001516384795123339)
          ·
            refine ⟨92922124502274577192685009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61948083001516384795123339 92922124502274577192685009)
            ·
              refine ⟨69691593376705932894513757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92922124502274577192685009 69691593376705932894513757)
              ·
                refine ⟨26134347516264724835442659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69691593376705932894513757 26134347516264724835442659)
                ·
                  refine ⟨39201521274397087253163989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26134347516264724835442659 39201521274397087253163989)
                  ·
                    refine ⟨918785654868681732496031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39201521274397087253163989 918785654868681732496031)
                    ·
                      rfl

theorem cell22_2683993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_2683993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2683993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2683993 prefixEnd_2683993 := by exact prefixLift 2683993
  have htrace : WordTrace (prefixWord ++ tailWord_2683993) baseStart_2683993 baseEnd_2683993 := by
    simpa [prefixWord, tailWord_2683993, baseEnd_2683993] using wordTrace_append hprefix tailTrace_2683993
  have hstable : (prefixWord ++ tailWord_2683993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683993).length < 2 ^ (prefixWord ++ tailWord_2683993).sum := by decide
  have hdescent : baseEnd_2683993 < baseStart_2683993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684089 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_2684089 : Nat := 118140960795 + 2684089 * 2 ^ 59
def prefixEnd_2684089 : Nat := 4983230072969 + 3 ^ 40 * 2684089 * 2
def baseEnd_2684089 : Nat := 918818517630569482095737

theorem tailTrace_2684089 : CollatzResearch.WordTrace tailWord_2684089 prefixEnd_2684089 918818517630569482095737 := by
  unfold tailWord_2684089
  simp only [CollatzResearch.WordTrace]
  refine ⟨97896768373011433750751321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65264512248674289167167547 97896768373011433750751321)
  ·
    refine ⟨73422576279758575313063491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97896768373011433750751321 73422576279758575313063491)
    ·
      refine ⟨110133864419637862969595237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73422576279758575313063491 110133864419637862969595237)
      ·
        refine ⟨20650099578682099306799107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110133864419637862969595237 20650099578682099306799107)
        ·
          refine ⟨30975149368023148960198661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20650099578682099306799107 30975149368023148960198661)
          ·
            refine ⟨5807840506504340430037249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30975149368023148960198661 5807840506504340430037249)
            ·
              refine ⟨4355880379878255322527937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5807840506504340430037249 4355880379878255322527937)
              ·
                refine ⟨3266910284908691491895953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355880379878255322527937 3266910284908691491895953)
                ·
                  refine ⟨2450182713681518618921965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3266910284908691491895953 2450182713681518618921965)
                  ·
                    refine ⟨918818517630569482095737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2450182713681518618921965 918818517630569482095737)
                    ·
                      rfl

theorem cell22_2684089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_2684089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684089 prefixEnd_2684089 := by exact prefixLift 2684089
  have htrace : WordTrace (prefixWord ++ tailWord_2684089) baseStart_2684089 baseEnd_2684089 := by
    simpa [prefixWord, tailWord_2684089, baseEnd_2684089] using wordTrace_append hprefix tailTrace_2684089
  have hstable : (prefixWord ++ tailWord_2684089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684089).length < 2 ^ (prefixWord ++ tailWord_2684089).sum := by decide
  have hdescent : baseEnd_2684089 < baseStart_2684089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684147 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 5]
def baseStart_2684147 : Nat := 118140960795 + 2684147 * 2 ^ 59
def prefixEnd_2684147 : Nat := 4983230072969 + 3 ^ 40 * 2684147 * 2
def baseEnd_2684147 : Nat := 306279457405292221381853

theorem tailTrace_2684147 : CollatzResearch.WordTrace tailWord_2684147 prefixEnd_2684147 306279457405292221381853 := by
  unfold tailWord_2684147
  simp only [CollatzResearch.WordTrace]
  refine ⟨97898883806801309656362695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65265922537867539770908463 97898883806801309656362695)
  ·
    refine ⟨146848325710201964484544043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97898883806801309656362695 146848325710201964484544043)
    ·
      refine ⟨220272488565302946726816065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146848325710201964484544043 220272488565302946726816065)
      ·
        refine ⟨165204366423977210045112049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220272488565302946726816065 165204366423977210045112049)
        ·
          refine ⟨123903274817982907533834037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165204366423977210045112049 123903274817982907533834037)
          ·
            refine ⟨11615932014185897581296941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123903274817982907533834037 11615932014185897581296941)
            ·
              refine ⟨4355974505319711592986353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11615932014185897581296941 4355974505319711592986353)
              ·
                refine ⟨3266980878989783694739765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355974505319711592986353 3266980878989783694739765)
                ·
                  refine ⟨306279457405292221381853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266980878989783694739765 306279457405292221381853)
                  ·
                    rfl

theorem cell22_2684147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 5].length) (baseStart_2684147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684147 prefixEnd_2684147 := by exact prefixLift 2684147
  have htrace : WordTrace (prefixWord ++ tailWord_2684147) baseStart_2684147 baseEnd_2684147 := by
    simpa [prefixWord, tailWord_2684147, baseEnd_2684147] using wordTrace_append hprefix tailTrace_2684147
  have hstable : (prefixWord ++ tailWord_2684147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684147).length < 2 ^ (prefixWord ++ tailWord_2684147).sum := by decide
  have hdescent : baseEnd_2684147 < baseStart_2684147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684209 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 6]
def baseStart_2684209 : Nat := 118140960795 + 2684209 * 2 ^ 59
def prefixEnd_2684209 : Nat := 4983230072969 + 3 ^ 40 * 2684209 * 2
def baseEnd_2684209 : Nat := 306286532027643056365123

theorem tailTrace_2684209 : CollatzResearch.WordTrace tailWord_2684209 prefixEnd_2684209 306286532027643056365123 := by
  unfold tailWord_2684209
  simp only [CollatzResearch.WordTrace]
  refine ⟨97901145132576694245119681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65267430088384462830079787 97901145132576694245119681)
  ·
    refine ⟨73425858849432520683839761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97901145132576694245119681 73425858849432520683839761)
    ·
      refine ⟨55069394137074390512879821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73425858849432520683839761 55069394137074390512879821)
      ·
        refine ⟨20651022801402896442329933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55069394137074390512879821 20651022801402896442329933)
        ·
          refine ⟨7744133550526086165873725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20651022801402896442329933 7744133550526086165873725)
          ·
            refine ⟨2904050081447282312202647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7744133550526086165873725 2904050081447282312202647)
            ·
              refine ⟨4356075122170923468303971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904050081447282312202647 4356075122170923468303971)
              ·
                refine ⟨6534112683256385202455957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356075122170923468303971 6534112683256385202455957)
                ·
                  refine ⟨306286532027643056365123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6534112683256385202455957 306286532027643056365123)
                  ·
                    rfl

theorem cell22_2684209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_2684209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684209 prefixEnd_2684209 := by exact prefixLift 2684209
  have htrace : WordTrace (prefixWord ++ tailWord_2684209) baseStart_2684209 baseEnd_2684209 := by
    simpa [prefixWord, tailWord_2684209, baseEnd_2684209] using wordTrace_append hprefix tailTrace_2684209
  have hstable : (prefixWord ++ tailWord_2684209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684209).length < 2 ^ (prefixWord ++ tailWord_2684209).sum := by decide
  have hdescent : baseEnd_2684209 < baseStart_2684209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684224 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_2684224 : Nat := 118140960795 + 2684224 * 2 ^ 59
def prefixEnd_2684224 : Nat := 4983230072969 + 3 ^ 40 * 2684224 * 2
def baseEnd_2684224 : Nat := 918864730889474129970323

theorem tailTrace_2684224 : CollatzResearch.WordTrace tailWord_2684224 prefixEnd_2684224 918864730889474129970323 := by
  unfold tailWord_2684224
  simp only [CollatzResearch.WordTrace]
  refine ⟨48950846113761175903457863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65267794818348234537943817 48950846113761175903457863)
  ·
    refine ⟨73426269170641763855186795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48950846113761175903457863 73426269170641763855186795)
    ·
      refine ⟨110139403755962645782780193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73426269170641763855186795 110139403755962645782780193)
      ·
        refine ⟨82604552816971984337085145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110139403755962645782780193 82604552816971984337085145)
        ·
          refine ⟨61953414612728988252813859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82604552816971984337085145 61953414612728988252813859)
          ·
            refine ⟨92930121919093482379220789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61953414612728988252813859 92930121919093482379220789)
            ·
              refine ⟨8712198929915013973051949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92930121919093482379220789 8712198929915013973051949)
              ·
                refine ⟨3267074598718130239894481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8712198929915013973051949 3267074598718130239894481)
                ·
                  refine ⟨2450305949038597679920861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267074598718130239894481 2450305949038597679920861)
                  ·
                    refine ⟨918864730889474129970323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2450305949038597679920861 918864730889474129970323)
                    ·
                      rfl

theorem cell22_2684224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_2684224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684224 prefixEnd_2684224 := by exact prefixLift 2684224
  have htrace : WordTrace (prefixWord ++ tailWord_2684224) baseStart_2684224 baseEnd_2684224 := by
    simpa [prefixWord, tailWord_2684224, baseEnd_2684224] using wordTrace_append hprefix tailTrace_2684224
  have hstable : (prefixWord ++ tailWord_2684224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684224).length < 2 ^ (prefixWord ++ tailWord_2684224).sum := by decide
  have hdescent : baseEnd_2684224 < baseStart_2684224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684228 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2684228 : Nat := 118140960795 + 2684228 * 2 ^ 59
def prefixEnd_2684228 : Nat := 4983230072969 + 3 ^ 40 * 2684228 * 2
def baseEnd_2684228 : Nat := 918866100171219452870311

theorem tailTrace_2684228 : CollatzResearch.WordTrace tailWord_2684228 prefixEnd_2684228 918866100171219452870311 := by
  unfold tailWord_2684228
  simp only [CollatzResearch.WordTrace]
  refine ⟨48950919059753930245030669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65267892079671906993374225 48950919059753930245030669)
  ·
    refine ⟨18356594647407723841886501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48950919059753930245030669 18356594647407723841886501)
    ·
      refine ⟨3441861496388948220353719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18356594647407723841886501 3441861496388948220353719)
      ·
        refine ⟨5162792244583422330530579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441861496388948220353719 5162792244583422330530579)
        ·
          refine ⟨7744188366875133495795869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162792244583422330530579 7744188366875133495795869)
          ·
            refine ⟨2904070637578175060923451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7744188366875133495795869 2904070637578175060923451)
            ·
              refine ⟨4356105956367262591385177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904070637578175060923451 4356105956367262591385177)
              ·
                refine ⟨3267079467275446943538883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356105956367262591385177 3267079467275446943538883)
                ·
                  refine ⟨4900619200913170415308325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267079467275446943538883 4900619200913170415308325)
                  ·
                    refine ⟨918866100171219452870311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4900619200913170415308325 918866100171219452870311)
                    ·
                      rfl

theorem cell22_2684228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2684228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684228 prefixEnd_2684228 := by exact prefixLift 2684228
  have htrace : WordTrace (prefixWord ++ tailWord_2684228) baseStart_2684228 baseEnd_2684228 := by
    simpa [prefixWord, tailWord_2684228, baseEnd_2684228] using wordTrace_append hprefix tailTrace_2684228
  have hstable : (prefixWord ++ tailWord_2684228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684228).length < 2 ^ (prefixWord ++ tailWord_2684228).sum := by decide
  have hdescent : baseEnd_2684228 < baseStart_2684228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684316 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 7]
def baseStart_2684316 : Nat := 118140960795 + 2684316 * 2 ^ 59
def prefixEnd_2684316 : Nat := 4983230072969 + 3 ^ 40 * 2684316 * 2
def baseEnd_2684316 : Nat := 306298741456538852223347

theorem tailTrace_2684316 : CollatzResearch.WordTrace tailWord_2684316 prefixEnd_2684316 306298741456538852223347 := by
  unfold tailWord_2684316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48952523871594525759632401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65270031828792701012843201 48952523871594525759632401)
  ·
    refine ⟨36714392903695894319724301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48952523871594525759632401 36714392903695894319724301)
    ·
      refine ⟨13767897338885960369896613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36714392903695894319724301 13767897338885960369896613)
      ·
        refine ⟨2581480751041117569355615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13767897338885960369896613 2581480751041117569355615)
        ·
          refine ⟨3872221126561676354033423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581480751041117569355615 3872221126561676354033423)
          ·
            refine ⟨5808331689842514531050135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872221126561676354033423 5808331689842514531050135)
            ·
              refine ⟨8712497534763771796575203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808331689842514531050135 8712497534763771796575203)
              ·
                refine ⟨13068746302145657694862805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8712497534763771796575203 13068746302145657694862805)
                ·
                  refine ⟨306298741456538852223347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13068746302145657694862805 306298741456538852223347)
                  ·
                    rfl

theorem cell22_2684316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_2684316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684316 prefixEnd_2684316 := by exact prefixLift 2684316
  have htrace : WordTrace (prefixWord ++ tailWord_2684316) baseStart_2684316 baseEnd_2684316 := by
    simpa [prefixWord, tailWord_2684316, baseEnd_2684316] using wordTrace_append hprefix tailTrace_2684316
  have hstable : (prefixWord ++ tailWord_2684316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684316).length < 2 ^ (prefixWord ++ tailWord_2684316).sum := by decide
  have hdescent : baseEnd_2684316 < baseStart_2684316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684333 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 5]
def baseStart_2684333 : Nat := 118140960795 + 2684333 * 2 ^ 59
def prefixEnd_2684333 : Nat := 4983230072969 + 3 ^ 40 * 2684333 * 2
def baseEnd_2684333 : Nat := 306300681272344726331663

theorem tailTrace_2684333 : CollatzResearch.WordTrace tailWord_2684333 prefixEnd_2684333 306300681272344726331663 := by
  unfold tailWord_2684333
  simp only [CollatzResearch.WordTrace]
  refine ⟨97905667784127463422633653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65270445189418308948422435 97905667784127463422633653)
  ·
    refine ⟨9178656354761949695871905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97905667784127463422633653 9178656354761949695871905)
    ·
      refine ⟨6883992266071462271903929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9178656354761949695871905 6883992266071462271903929)
      ·
        refine ⟨5162994199553596703927947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6883992266071462271903929 5162994199553596703927947)
        ·
          refine ⟨7744491299330395055891921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162994199553596703927947 7744491299330395055891921)
          ·
            refine ⟨5808368474497796291918941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744491299330395055891921 5808368474497796291918941)
            ·
              refine ⟨2178138177936673609469603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5808368474497796291918941 2178138177936673609469603)
              ·
                refine ⟨3267207266905010414204405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178138177936673609469603 3267207266905010414204405)
                ·
                  refine ⟨306300681272344726331663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267207266905010414204405 306300681272344726331663)
                  ·
                    rfl

theorem cell22_2684333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_2684333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684333 prefixEnd_2684333 := by exact prefixLift 2684333
  have htrace : WordTrace (prefixWord ++ tailWord_2684333) baseStart_2684333 baseEnd_2684333 := by
    simpa [prefixWord, tailWord_2684333, baseEnd_2684333] using wordTrace_append hprefix tailTrace_2684333
  have hstable : (prefixWord ++ tailWord_2684333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684333).length < 2 ^ (prefixWord ++ tailWord_2684333).sum := by decide
  have hdescent : baseEnd_2684333 < baseStart_2684333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684359 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2684359 : Nat := 118140960795 + 2684359 * 2 ^ 59
def prefixEnd_2684359 : Nat := 4983230072969 + 3 ^ 40 * 2684359 * 2
def baseEnd_2684359 : Nat := 918910944148378777844909

theorem tailTrace_2684359 : CollatzResearch.WordTrace tailWord_2684359 prefixEnd_2684359 918910944148378777844909 := by
  unfold tailWord_2684359
  simp only [CollatzResearch.WordTrace]
  refine ⟨97906616082033269863080131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65271077388022179908720087 97906616082033269863080131)
  ·
    refine ⟨146859924123049904794620197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97906616082033269863080131 146859924123049904794620197)
    ·
      refine ⟨27536235773071857148991287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146859924123049904794620197 27536235773071857148991287)
      ·
        refine ⟨41304353659607785723486931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27536235773071857148991287 41304353659607785723486931)
        ·
          refine ⟨61956530489411678585230397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41304353659607785723486931 61956530489411678585230397)
          ·
            refine ⟨23233698933529379469461399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61956530489411678585230397 23233698933529379469461399)
            ·
              refine ⟨34850548400294069204192099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23233698933529379469461399 34850548400294069204192099)
              ·
                refine ⟨52275822600441103806288149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34850548400294069204192099 52275822600441103806288149)
                ·
                  refine ⟨2450429184395676740919757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52275822600441103806288149 2450429184395676740919757)
                  ·
                    refine ⟨918910944148378777844909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2450429184395676740919757 918910944148378777844909)
                    ·
                      rfl

theorem cell22_2684359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2684359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684359 prefixEnd_2684359 := by exact prefixLift 2684359
  have htrace : WordTrace (prefixWord ++ tailWord_2684359) baseStart_2684359 baseEnd_2684359 := by
    simpa [prefixWord, tailWord_2684359, baseEnd_2684359] using wordTrace_append hprefix tailTrace_2684359
  have hstable : (prefixWord ++ tailWord_2684359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684359).length < 2 ^ (prefixWord ++ tailWord_2684359).sum := by decide
  have hdescent : baseEnd_2684359 < baseStart_2684359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684378 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_2684378 : Nat := 118140960795 + 2684378 * 2 ^ 59
def prefixEnd_2684378 : Nat := 4983230072969 + 3 ^ 40 * 2684378 * 2
def baseEnd_2684378 : Nat := 306305816078889687206617

theorem tailTrace_2684378 : CollatzResearch.WordTrace tailWord_2684378 prefixEnd_2684378 306305816078889687206617 := by
  unfold tailWord_2684378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24476827267241109027005447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65271539379309624072014525 24476827267241109027005447)
  ·
    refine ⟨36715240900861663540508171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24476827267241109027005447 36715240900861663540508171)
    ·
      refine ⟨55072861351292495310762257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36715240900861663540508171 55072861351292495310762257)
      ·
        refine ⟨41304646013469371483071693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55072861351292495310762257 41304646013469371483071693)
        ·
          refine ⟨15489242255051014306151885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41304646013469371483071693 15489242255051014306151885)
          ·
            refine ⟨5808465845644130364806957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15489242255051014306151885 5808465845644130364806957)
            ·
              refine ⟨2178174692116548886802609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5808465845644130364806957 2178174692116548886802609)
              ·
                refine ⟨1633631019087411665101957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178174692116548886802609 1633631019087411665101957)
                ·
                  refine ⟨306305816078889687206617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633631019087411665101957 306305816078889687206617)
                  ·
                    rfl

theorem cell22_2684378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_2684378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684378 prefixEnd_2684378 := by exact prefixLift 2684378
  have htrace : WordTrace (prefixWord ++ tailWord_2684378) baseStart_2684378 baseEnd_2684378 := by
    simpa [prefixWord, tailWord_2684378, baseEnd_2684378] using wordTrace_append hprefix tailTrace_2684378
  have hstable : (prefixWord ++ tailWord_2684378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684378).length < 2 ^ (prefixWord ++ tailWord_2684378).sum := by decide
  have hdescent : baseEnd_2684378 < baseStart_2684378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684389 : List Nat := [1, 3, 1, 5, 1, 1, 1, 9]
def baseStart_2684389 : Nat := 118140960795 + 2684389 * 2 ^ 59
def prefixEnd_2684389 : Nat := 4983230072969 + 3 ^ 40 * 2684389 * 2
def baseEnd_2684389 : Nat := 102102357084607633288313

theorem tailTrace_2684389 : CollatzResearch.WordTrace tailWord_2684389 prefixEnd_2684389 102102357084607633288313 := by
  unfold tailWord_2684389
  simp only [CollatzResearch.WordTrace]
  refine ⟨97907710271924584986672221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65271806847949723324448147 97907710271924584986672221)
  ·
    refine ⟨36715391351971719370002083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97907710271924584986672221 36715391351971719370002083)
    ·
      refine ⟨55073087027957579055003125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36715391351971719370002083 55073087027957579055003125)
      ·
        refine ⟨5163101908871023036406543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55073087027957579055003125 5163101908871023036406543)
        ·
          refine ⟨7744652863306534554609815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163101908871023036406543 7744652863306534554609815)
          ·
            refine ⟨11616979294959801831914723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7744652863306534554609815 11616979294959801831914723)
            ·
              refine ⟨17425468942439702747872085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11616979294959801831914723 17425468942439702747872085)
              ·
                refine ⟨102102357084607633288313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17425468942439702747872085 102102357084607633288313)
                ·
                  rfl

theorem cell22_2684389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 9].length) (baseStart_2684389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684389 prefixEnd_2684389 := by exact prefixLift 2684389
  have htrace : WordTrace (prefixWord ++ tailWord_2684389) baseStart_2684389 baseEnd_2684389 := by
    simpa [prefixWord, tailWord_2684389, baseEnd_2684389] using wordTrace_append hprefix tailTrace_2684389
  have hstable : (prefixWord ++ tailWord_2684389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684389).length < 2 ^ (prefixWord ++ tailWord_2684389).sum := by decide
  have hdescent : baseEnd_2684389 < baseStart_2684389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684429 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2684429 : Nat := 118140960795 + 2684429 * 2 ^ 59
def prefixEnd_2684429 : Nat := 4983230072969 + 3 ^ 40 * 2684429 * 2
def baseEnd_2684429 : Nat := 306311635526307309531565

theorem tailTrace_2684429 : CollatzResearch.WordTrace tailWord_2684429 prefixEnd_2684429 306311635526307309531565 := by
  unfold tailWord_2684429
  simp only [CollatzResearch.WordTrace]
  refine ⟨97909169191779671818128341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65272779461186447878752227 97909169191779671818128341)
  ·
    refine ⟨2294746152932336058237383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 97909169191779671818128341 2294746152932336058237383)
    ·
      refine ⟨3442119229398504087356075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294746152932336058237383 3442119229398504087356075)
      ·
        refine ⟨5163178844097756131034113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442119229398504087356075 5163178844097756131034113)
        ·
          refine ⟨3872384133073317098275585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5163178844097756131034113 3872384133073317098275585)
          ·
            refine ⟨2904288099804987823706689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872384133073317098275585 2904288099804987823706689)
            ·
              refine ⟨2178216074853740867780017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904288099804987823706689 2178216074853740867780017)
              ·
                refine ⟨1633662056140305650835013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178216074853740867780017 1633662056140305650835013)
                ·
                  refine ⟨306311635526307309531565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633662056140305650835013 306311635526307309531565)
                  ·
                    rfl

theorem cell22_2684429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2684429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684429 prefixEnd_2684429 := by exact prefixLift 2684429
  have htrace : WordTrace (prefixWord ++ tailWord_2684429) baseStart_2684429 baseEnd_2684429 := by
    simpa [prefixWord, tailWord_2684429, baseEnd_2684429] using wordTrace_append hprefix tailTrace_2684429
  have hstable : (prefixWord ++ tailWord_2684429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684429).length < 2 ^ (prefixWord ++ tailWord_2684429).sum := by decide
  have hdescent : baseEnd_2684429 < baseStart_2684429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684449 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2684449 : Nat := 118140960795 + 2684449 * 2 ^ 59
def prefixEnd_2684449 : Nat := 4983230072969 + 3 ^ 40 * 2684449 * 2
def baseEnd_2684449 : Nat := 918941752987648543094633

theorem tailTrace_2684449 : CollatzResearch.WordTrace tailWord_2684449 prefixEnd_2684449 918941752987648543094633 := by
  unfold tailWord_2684449
  simp only [CollatzResearch.WordTrace]
  refine ⟨97909898651707215233856401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65273265767804810155904267 97909898651707215233856401)
  ·
    refine ⟨73432423988780411425392301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97909898651707215233856401 73432423988780411425392301)
    ·
      refine ⟨27537158995792654284522113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73432423988780411425392301 27537158995792654284522113)
      ·
        refine ⟨20652869246844490713391585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27537158995792654284522113 20652869246844490713391585)
        ·
          refine ⟨15489651935133368035043689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20652869246844490713391585 15489651935133368035043689)
          ·
            refine ⟨11617238951350026026282767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15489651935133368035043689 11617238951350026026282767)
            ·
              refine ⟨17425858427025039039424151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11617238951350026026282767 17425858427025039039424151)
              ·
                refine ⟨26138787640537558559136227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17425858427025039039424151 26138787640537558559136227)
                ·
                  refine ⟨39208181460806337838704341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26138787640537558559136227 39208181460806337838704341)
                  ·
                    refine ⟨918941752987648543094633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39208181460806337838704341 918941752987648543094633)
                    ·
                      rfl

theorem cell22_2684449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2684449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684449 prefixEnd_2684449 := by exact prefixLift 2684449
  have htrace : WordTrace (prefixWord ++ tailWord_2684449) baseStart_2684449 baseEnd_2684449 := by
    simpa [prefixWord, tailWord_2684449, baseEnd_2684449] using wordTrace_append hprefix tailTrace_2684449
  have hstable : (prefixWord ++ tailWord_2684449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684449).length < 2 ^ (prefixWord ++ tailWord_2684449).sum := by decide
  have hdescent : baseEnd_2684449 < baseStart_2684449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684496 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 4]
def baseStart_2684496 : Nat := 118140960795 + 2684496 * 2 ^ 59
def prefixEnd_2684496 : Nat := 4983230072969 + 3 ^ 40 * 2684496 * 2
def baseEnd_2684496 : Nat := 306319280682718695723163

theorem tailTrace_2684496 : CollatzResearch.WordTrace tailWord_2684496 prefixEnd_2684496 306319280682718695723163 := by
  unfold tailWord_2684496
  simp only [CollatzResearch.WordTrace]
  refine ⟨48955806441268471130408671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65274408588357961507211561 48955806441268471130408671)
  ·
    refine ⟨73433709661902706695613007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48955806441268471130408671 73433709661902706695613007)
    ·
      refine ⟨110150564492854060043419511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73433709661902706695613007 110150564492854060043419511)
      ·
        refine ⟨165225846739281090065129267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110150564492854060043419511 165225846739281090065129267)
        ·
          refine ⟨247838770108921635097693901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165225846739281090065129267 247838770108921635097693901)
          ·
            refine ⟨92939538790845613161635213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247838770108921635097693901 92939538790845613161635213)
            ·
              refine ⟨34852327046567104935613205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92939538790845613161635213 34852327046567104935613205)
              ·
                refine ⟨1633702830307833043856869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34852327046567104935613205 1633702830307833043856869)
                ·
                  refine ⟨306319280682718695723163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633702830307833043856869 306319280682718695723163)
                  ·
                    rfl

theorem cell22_2684496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_2684496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684496 prefixEnd_2684496 := by exact prefixLift 2684496
  have htrace : WordTrace (prefixWord ++ tailWord_2684496) baseStart_2684496 baseEnd_2684496 := by
    simpa [prefixWord, tailWord_2684496, baseEnd_2684496] using wordTrace_append hprefix tailTrace_2684496
  have hstable : (prefixWord ++ tailWord_2684496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684496).length < 2 ^ (prefixWord ++ tailWord_2684496).sum := by decide
  have hdescent : baseEnd_2684496 < baseStart_2684496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684530 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_2684530 : Nat := 118140960795 + 2684530 * 2 ^ 59
def prefixEnd_2684530 : Nat := 4983230072969 + 3 ^ 40 * 2684530 * 2
def baseEnd_2684530 : Nat := 306323160314330443939795

theorem tailTrace_2684530 : CollatzResearch.WordTrace tailWord_2684530 prefixEnd_2684530 306323160314330443939795 := by
  unfold tailWord_2684530
  simp only [CollatzResearch.WordTrace]
  refine ⟨24478213241103441516888761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65275235309609177378370029 24478213241103441516888761)
  ·
    refine ⟨18358659930827581137666571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24478213241103441516888761 18358659930827581137666571)
    ·
      refine ⟨27537989896241371706499857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18358659930827581137666571 27537989896241371706499857)
      ·
        refine ⟨20653492422181028779874893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27537989896241371706499857 20653492422181028779874893)
        ·
          refine ⟨7745059658317885792453085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20653492422181028779874893 7745059658317885792453085)
          ·
            refine ⟨2904397371869207172169907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7745059658317885792453085 2904397371869207172169907)
            ·
              refine ⟨4356596057803810758254861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904397371869207172169907 4356596057803810758254861)
              ·
                refine ⟨1633723521676429034345573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4356596057803810758254861 1633723521676429034345573)
                ·
                  refine ⟨306323160314330443939795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633723521676429034345573 306323160314330443939795)
                  ·
                    rfl

theorem cell22_2684530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_2684530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684530 prefixEnd_2684530 := by exact prefixLift 2684530
  have htrace : WordTrace (prefixWord ++ tailWord_2684530) baseStart_2684530 baseEnd_2684530 := by
    simpa [prefixWord, tailWord_2684530, baseEnd_2684530] using wordTrace_append hprefix tailTrace_2684530
  have hstable : (prefixWord ++ tailWord_2684530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684530).length < 2 ^ (prefixWord ++ tailWord_2684530).sum := by decide
  have hdescent : baseEnd_2684530 < baseStart_2684530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684541 : List Nat := [1, 4, 1, 1, 4, 3, 8]
def baseStart_2684541 : Nat := 118140960795 + 2684541 * 2 ^ 59
def prefixEnd_2684541 : Nat := 4983230072969 + 3 ^ 40 * 2684541 * 2
def baseEnd_2684541 : Nat := 34036046165473739622013

theorem tailTrace_2684541 : CollatzResearch.WordTrace tailWord_2684541 prefixEnd_2684541 34036046165473739622013 := by
  unfold tailWord_2684541
  simp only [CollatzResearch.WordTrace]
  refine ⟨97913254167373914946205477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65275502778249276630803651 97913254167373914946205477)
  ·
    refine ⟨18358735156382609052413527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97913254167373914946205477 18358735156382609052413527)
    ·
      refine ⟨27538102734573913578620291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18358735156382609052413527 27538102734573913578620291)
      ·
        refine ⟨41307154101860870367930437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27538102734573913578620291 41307154101860870367930437)
        ·
          refine ⟨7745091394098913193986957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41307154101860870367930437 7745091394098913193986957)
          ·
            refine ⟨2904409272787092447745109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7745091394098913193986957 2904409272787092447745109)
            ·
              refine ⟨34036046165473739622013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2904409272787092447745109 34036046165473739622013)
              ·
                rfl

theorem cell22_2684541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 8].length) (baseStart_2684541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684541 prefixEnd_2684541 := by exact prefixLift 2684541
  have htrace : WordTrace (prefixWord ++ tailWord_2684541) baseStart_2684541 baseEnd_2684541 := by
    simpa [prefixWord, tailWord_2684541, baseEnd_2684541] using wordTrace_append hprefix tailTrace_2684541
  have hstable : (prefixWord ++ tailWord_2684541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684541).length < 2 ^ (prefixWord ++ tailWord_2684541).sum := by decide
  have hdescent : baseEnd_2684541 < baseStart_2684541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684569 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 9]
def baseStart_2684569 : Nat := 118140960795 + 2684569 * 2 ^ 59
def prefixEnd_2684569 : Nat := 4983230072969 + 3 ^ 40 * 2684569 * 2
def baseEnd_2684569 : Nat := 306327610480002743364755

theorem tailTrace_2684569 : CollatzResearch.WordTrace tailWord_2684569 prefixEnd_2684569 306327610480002743364755 := by
  unfold tailWord_2684569
  simp only [CollatzResearch.WordTrace]
  refine ⟨97914275411272475728224761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65276183607514983818816507 97914275411272475728224761)
  ·
    refine ⟨73435706558454356796168571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97914275411272475728224761 73435706558454356796168571)
    ·
      refine ⟨110153559837681535194252857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73435706558454356796168571 110153559837681535194252857)
      ·
        refine ⟨82615169878261151395689643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110153559837681535194252857 82615169878261151395689643)
        ·
          refine ⟨123922754817391727093534465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82615169878261151395689643 123922754817391727093534465)
          ·
            refine ⟨92942066113043795320150849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123922754817391727093534465 92942066113043795320150849)
            ·
              refine ⟨69706549584782846490113137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92942066113043795320150849 69706549584782846490113137)
              ·
                refine ⟨52279912188587134867584853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69706549584782846490113137 52279912188587134867584853)
                ·
                  refine ⟨306327610480002743364755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52279912188587134867584853 306327610480002743364755)
                  ·
                    rfl

theorem cell22_2684569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_2684569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684569 prefixEnd_2684569 := by exact prefixLift 2684569
  have htrace : WordTrace (prefixWord ++ tailWord_2684569) baseStart_2684569 baseEnd_2684569 := by
    simpa [prefixWord, tailWord_2684569, baseEnd_2684569] using wordTrace_append hprefix tailTrace_2684569
  have hstable : (prefixWord ++ tailWord_2684569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684569).length < 2 ^ (prefixWord ++ tailWord_2684569).sum := by decide
  have hdescent : baseEnd_2684569 < baseStart_2684569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
