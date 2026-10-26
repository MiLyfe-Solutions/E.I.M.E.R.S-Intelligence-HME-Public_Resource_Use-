import V185TrunkScan22Chunk414

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3700266 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_3700266 : Nat := 118140960795 + 3700266 * 2 ^ 59
def prefixEnd_3700266 : Nat := 4983230072969 + 3 ^ 40 * 3700266 * 2
def baseEnd_3700266 : Nat := 422225557219938872435065

theorem tailTrace_3700266 : CollatzResearch.WordTrace tailWord_3700266 prefixEnd_3700266 422225557219938872435065 := by
  unfold tailWord_3700266
  simp only [CollatzResearch.WordTrace]
  refine ⟨33739947103143927991348163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89973192275050474643595101 33739947103143927991348163)
  ·
    refine ⟨50609920654715891987022245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33739947103143927991348163 50609920654715891987022245)
    ·
      refine ⟨9489360122759229747566671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50609920654715891987022245 9489360122759229747566671)
      ·
        refine ⟨14234040184138844621350007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489360122759229747566671 14234040184138844621350007)
        ·
          refine ⟨21351060276208266932025011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14234040184138844621350007 21351060276208266932025011)
          ·
            refine ⟨32026590414312400398037517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21351060276208266932025011 32026590414312400398037517)
            ·
              refine ⟨12009971405367150149264069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32026590414312400398037517 12009971405367150149264069)
              ·
                refine ⟨2251869638506340652987013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12009971405367150149264069 2251869638506340652987013)
                ·
                  refine ⟨422225557219938872435065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251869638506340652987013 422225557219938872435065)
                  ·
                    rfl

theorem cell22_3700266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_3700266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700266 prefixEnd_3700266 := by exact prefixLift 3700266
  have htrace : WordTrace (prefixWord ++ tailWord_3700266) baseStart_3700266 baseEnd_3700266 := by
    simpa [prefixWord, tailWord_3700266, baseEnd_3700266] using wordTrace_append hprefix tailTrace_3700266
  have hstable : (prefixWord ++ tailWord_3700266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700266).length < 2 ^ (prefixWord ++ tailWord_3700266).sum := by decide
  have hdescent : baseEnd_3700266 < baseStart_3700266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700281 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_3700281 : Nat := 118140960795 + 3700281 * 2 ^ 59
def prefixEnd_3700281 : Nat := 4983230072969 + 3 ^ 40 * 3700281 * 2
def baseEnd_3700281 : Nat := 1266681806466361578180149

theorem tailTrace_3700281 : CollatzResearch.WordTrace tailWord_3700281 prefixEnd_3700281 1266681806466361578180149 := by
  unfold tailWord_3700281
  simp only [CollatzResearch.WordTrace]
  refine ⟨134960335507521369527188697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89973557005014246351459131 134960335507521369527188697)
  ·
    refine ⟨101220251630641027145391523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134960335507521369527188697 101220251630641027145391523)
    ·
      refine ⟨151830377445961540718087285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101220251630641027145391523 151830377445961540718087285)
      ·
        refine ⟨14234097885558894442320683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151830377445961540718087285 14234097885558894442320683)
        ·
          refine ⟨21351146828338341663481025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14234097885558894442320683 21351146828338341663481025)
          ·
            refine ⟨16013360121253756247610769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21351146828338341663481025 16013360121253756247610769)
            ·
              refine ⟨12010020090940317185708077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16013360121253756247610769 12010020090940317185708077)
              ·
                refine ⟨4503757534102618944640529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12010020090940317185708077 4503757534102618944640529)
                ·
                  refine ⟨3377818150576964208480397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4503757534102618944640529 3377818150576964208480397)
                  ·
                    refine ⟨1266681806466361578180149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377818150576964208480397 1266681806466361578180149)
                    ·
                      rfl

theorem cell22_3700281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_3700281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700281 prefixEnd_3700281 := by exact prefixLift 3700281
  have htrace : WordTrace (prefixWord ++ tailWord_3700281) baseStart_3700281 baseEnd_3700281 := by
    simpa [prefixWord, tailWord_3700281, baseEnd_3700281] using wordTrace_append hprefix tailTrace_3700281
  have hstable : (prefixWord ++ tailWord_3700281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700281).length < 2 ^ (prefixWord ++ tailWord_3700281).sum := by decide
  have hdescent : baseEnd_3700281 < baseStart_3700281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700309 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3700309 : Nat := 118140960795 + 3700309 * 2 ^ 59
def prefixEnd_3700309 : Nat := 4983230072969 + 3 ^ 40 * 3700309 * 2
def baseEnd_3700309 : Nat := 1266691391438578838480063

theorem tailTrace_3700309 : CollatzResearch.WordTrace tailWord_3700309 prefixEnd_3700309 1266691391438578838480063 := by
  unfold tailWord_3700309
  simp only [CollatzResearch.WordTrace]
  refine ⟨134961356751419930309207981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89974237834279953539471987 134961356751419930309207981)
  ·
    refine ⟨50610508781782473865952993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134961356751419930309207981 50610508781782473865952993)
    ·
      refine ⟨37957881586336855399464745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50610508781782473865952993 37957881586336855399464745)
      ·
        refine ⟨28468411189752641549598559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37957881586336855399464745 28468411189752641549598559)
        ·
          refine ⟨42702616784628962324397839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28468411189752641549598559 42702616784628962324397839)
          ·
            refine ⟨64053925176943443486596759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42702616784628962324397839 64053925176943443486596759)
            ·
              refine ⟨96080887765415165229895139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64053925176943443486596759 96080887765415165229895139)
              ·
                refine ⟨144121331648122747844842709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96080887765415165229895139 144121331648122747844842709)
                ·
                  refine ⟨3377843710502876902613501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 144121331648122747844842709 3377843710502876902613501)
                  ·
                    refine ⟨1266691391438578838480063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377843710502876902613501 1266691391438578838480063)
                    ·
                      rfl

theorem cell22_3700309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3700309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700309 prefixEnd_3700309 := by exact prefixLift 3700309
  have htrace : WordTrace (prefixWord ++ tailWord_3700309) baseStart_3700309 baseEnd_3700309 := by
    simpa [prefixWord, tailWord_3700309, baseEnd_3700309] using wordTrace_append hprefix tailTrace_3700309
  have hstable : (prefixWord ++ tailWord_3700309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700309).length < 2 ^ (prefixWord ++ tailWord_3700309).sum := by decide
  have hdescent : baseEnd_3700309 < baseStart_3700309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700399 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 1, 5]
def baseStart_3700399 : Nat := 118140960795 + 3700399 * 2 ^ 59
def prefixEnd_3700399 : Nat := 4983230072969 + 3 ^ 40 * 3700399 * 2
def baseEnd_3700399 : Nat := 1266722200277848603729787

theorem tailTrace_3700399 : CollatzResearch.WordTrace tailWord_3700399 prefixEnd_3700399 1266722200277848603729787 := by
  unfold tailWord_3700399
  simp only [CollatzResearch.WordTrace]
  refine ⟨134964639321093875679984251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89976426214062583786656167 134964639321093875679984251)
  ·
    refine ⟨202446958981640813519976377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134964639321093875679984251 202446958981640813519976377)
    ·
      refine ⟨151835219236230610139982283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202446958981640813519976377 151835219236230610139982283)
      ·
        refine ⟨227752828854345915209973425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151835219236230610139982283 227752828854345915209973425)
        ·
          refine ⟨170814621640759436407480069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227752828854345915209973425 170814621640759436407480069)
          ·
            refine ⟨32027741557642394326402513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170814621640759436407480069 32027741557642394326402513)
            ·
              refine ⟨24020806168231795744801885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32027741557642394326402513 24020806168231795744801885)
              ·
                refine ⟨9007802313086923404300707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24020806168231795744801885 9007802313086923404300707)
                ·
                  refine ⟨13511703469630385106451061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9007802313086923404300707 13511703469630385106451061)
                  ·
                    refine ⟨1266722200277848603729787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13511703469630385106451061 1266722200277848603729787)
                    ·
                      rfl

theorem cell22_3700399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_3700399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700399 prefixEnd_3700399 := by exact prefixLift 3700399
  have htrace : WordTrace (prefixWord ++ tailWord_3700399) baseStart_3700399 baseEnd_3700399 := by
    simpa [prefixWord, tailWord_3700399, baseEnd_3700399] using wordTrace_append hprefix tailTrace_3700399
  have hstable : (prefixWord ++ tailWord_3700399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700399).length < 2 ^ (prefixWord ++ tailWord_3700399).sum := by decide
  have hdescent : baseEnd_3700399 < baseStart_3700399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700433 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_3700433 : Nat := 118140960795 + 3700433 * 2 ^ 59
def prefixEnd_3700433 : Nat := 4983230072969 + 3 ^ 40 * 3700433 * 2
def baseEnd_3700433 : Nat := 1266733839172683848379683

theorem tailTrace_3700433 : CollatzResearch.WordTrace tailWord_3700433 prefixEnd_3700433 1266733839172683848379683 := by
  unfold tailWord_3700433
  simp only [CollatzResearch.WordTrace]
  refine ⟨134965879402970699486721953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89977252935313799657814635 134965879402970699486721953)
  ·
    refine ⟨101224409552228024615041465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134965879402970699486721953 101224409552228024615041465)
    ·
      refine ⟨75918307164171018461281099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101224409552228024615041465 75918307164171018461281099)
      ·
        refine ⟨113877460746256527691921649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75918307164171018461281099 113877460746256527691921649)
        ·
          refine ⟨85408095559692395768941237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113877460746256527691921649 85408095559692395768941237)
          ·
            refine ⟨8007008958721162103338241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85408095559692395768941237 8007008958721162103338241)
            ·
              refine ⟨6005256719040871577503681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8007008958721162103338241 6005256719040871577503681)
              ·
                refine ⟨4503942539280653683127761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005256719040871577503681 4503942539280653683127761)
                ·
                  refine ⟨3377956904460490262345821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4503942539280653683127761 3377956904460490262345821)
                  ·
                    refine ⟨1266733839172683848379683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377956904460490262345821 1266733839172683848379683)
                    ·
                      rfl

theorem cell22_3700433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_3700433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700433 prefixEnd_3700433 := by exact prefixLift 3700433
  have htrace : WordTrace (prefixWord ++ tailWord_3700433) baseStart_3700433 baseEnd_3700433 := by
    simpa [prefixWord, tailWord_3700433, baseEnd_3700433] using wordTrace_append hprefix tailTrace_3700433
  have hstable : (prefixWord ++ tailWord_3700433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700433).length < 2 ^ (prefixWord ++ tailWord_3700433).sum := by decide
  have hdescent : baseEnd_3700433 < baseStart_3700433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700474 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_3700474 : Nat := 118140960795 + 3700474 * 2 ^ 59
def prefixEnd_3700474 : Nat := 4983230072969 + 3 ^ 40 * 3700474 * 2
def baseEnd_3700474 : Nat := 422249291436857802701519

theorem tailTrace_3700474 : CollatzResearch.WordTrace tailWord_3700474 prefixEnd_3700474 422249291436857802701519 := by
  unfold tailWord_3700474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33741843698955540872241119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89978249863881442325976317 33741843698955540872241119)
  ·
    refine ⟨50612765548433311308361679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33741843698955540872241119 50612765548433311308361679)
    ·
      refine ⟨75919148322649966962542519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50612765548433311308361679 75919148322649966962542519)
      ·
        refine ⟨113878722483974950443813779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75919148322649966962542519 113878722483974950443813779)
        ·
          refine ⟨170818083725962425665720669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113878722483974950443813779 170818083725962425665720669)
          ·
            refine ⟨64056781397235909624645251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170818083725962425665720669 64056781397235909624645251)
            ·
              refine ⟨96085172095853864436967877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64056781397235909624645251 96085172095853864436967877)
              ·
                refine ⟨18015969767972599581931477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96085172095853864436967877 18015969767972599581931477)
                ·
                  refine ⟨422249291436857802701519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18015969767972599581931477 422249291436857802701519)
                  ·
                    rfl

theorem cell22_3700474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_3700474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700474 prefixEnd_3700474 := by exact prefixLift 3700474
  have htrace : WordTrace (prefixWord ++ tailWord_3700474) baseStart_3700474 baseEnd_3700474 := by
    simpa [prefixWord, tailWord_3700474, baseEnd_3700474] using wordTrace_append hprefix tailTrace_3700474
  have hstable : (prefixWord ++ tailWord_3700474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700474).length < 2 ^ (prefixWord ++ tailWord_3700474).sum := by decide
  have hdescent : baseEnd_3700474 < baseStart_3700474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700491 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 5]
def baseStart_3700491 : Nat := 118140960795 + 3700491 * 2 ^ 59
def prefixEnd_3700491 : Nat := 4983230072969 + 3 ^ 40 * 3700491 * 2
def baseEnd_3700491 : Nat := 422251231252663676809835

theorem tailTrace_3700491 : CollatzResearch.WordTrace tailWord_3700491 prefixEnd_3700491 422251231252663676809835 := by
  unfold tailWord_3700491
  simp only [CollatzResearch.WordTrace]
  refine ⟨134967994836760575392333327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89978663224507050261555551 134967994836760575392333327)
  ·
    refine ⟨202451992255140863088499991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134967994836760575392333327 202451992255140863088499991)
    ·
      refine ⟨303677988382711294632749987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202451992255140863088499991 303677988382711294632749987)
      ·
        refine ⟨455516982574066941949124981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303677988382711294632749987 455516982574066941949124981)
        ·
          refine ⟨42704717116318775807730467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 455516982574066941949124981 42704717116318775807730467)
          ·
            refine ⟨64057075674478163711595701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42704717116318775807730467 64057075674478163711595701)
            ·
              refine ⟨6005350844482327847962097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64057075674478163711595701 6005350844482327847962097)
              ·
                refine ⟨4504013133361745885971573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005350844482327847962097 4504013133361745885971573)
                ·
                  refine ⟨422251231252663676809835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504013133361745885971573 422251231252663676809835)
                  ·
                    rfl

theorem cell22_3700491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 5].length) (baseStart_3700491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700491 prefixEnd_3700491 := by exact prefixLift 3700491
  have htrace : WordTrace (prefixWord ++ tailWord_3700491) baseStart_3700491 baseEnd_3700491 := by
    simpa [prefixWord, tailWord_3700491, baseEnd_3700491] using wordTrace_append hprefix tailTrace_3700491
  have hstable : (prefixWord ++ tailWord_3700491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700491).length < 2 ^ (prefixWord ++ tailWord_3700491).sum := by decide
  have hdescent : baseEnd_3700491 < baseStart_3700491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700506 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3700506 : Nat := 118140960795 + 3700506 * 2 ^ 59
def prefixEnd_3700506 : Nat := 4983230072969 + 3 ^ 40 * 3700506 * 2
def baseEnd_3700506 : Nat := 1266758828564535991304459

theorem tailTrace_3700506 : CollatzResearch.WordTrace tailWord_3700506 prefixEnd_3700506 1266758828564535991304459 := by
  unfold tailWord_3700506
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742135482926558238532343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89979027954470821969419581 33742135482926558238532343)
  ·
    refine ⟨50613203224389837357798515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33742135482926558238532343 50613203224389837357798515)
    ·
      refine ⟨75919804836584756036697773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50613203224389837357798515 75919804836584756036697773)
      ·
        refine ⟨28469926813719283513761665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75919804836584756036697773 28469926813719283513761665)
        ·
          refine ⟨21352445110289462635321249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28469926813719283513761665 21352445110289462635321249)
          ·
            refine ⟨16014333832717096976490937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21352445110289462635321249 16014333832717096976490937)
            ·
              refine ⟨12010750374537822732368203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16014333832717096976490937 12010750374537822732368203)
              ·
                refine ⟨18016125561806734098552305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12010750374537822732368203 18016125561806734098552305)
                ·
                  refine ⟨13512094171355050573914229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18016125561806734098552305 13512094171355050573914229)
                  ·
                    refine ⟨1266758828564535991304459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13512094171355050573914229 1266758828564535991304459)
                    ·
                      rfl

theorem cell22_3700506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3700506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700506 prefixEnd_3700506 := by exact prefixLift 3700506
  have htrace : WordTrace (prefixWord ++ tailWord_3700506) baseStart_3700506 baseEnd_3700506 := by
    simpa [prefixWord, tailWord_3700506, baseEnd_3700506] using wordTrace_append hprefix tailTrace_3700506
  have hstable : (prefixWord ++ tailWord_3700506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700506).length < 2 ^ (prefixWord ++ tailWord_3700506).sum := by decide
  have hdescent : baseEnd_3700506 < baseStart_3700506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700508 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 5]
def baseStart_3700508 : Nat := 118140960795 + 3700508 * 2 ^ 59
def prefixEnd_3700508 : Nat := 4983230072969 + 3 ^ 40 * 3700508 * 2
def baseEnd_3700508 : Nat := 422253171068469550918151

theorem tailTrace_3700508 : CollatzResearch.WordTrace tailWord_3700508 prefixEnd_3700508 422253171068469550918151 := by
  unfold tailWord_3700508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67484307438849493647851089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89979076585132658197134785 67484307438849493647851089)
  ·
    refine ⟨50613230579137120235888317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67484307438849493647851089 50613230579137120235888317)
    ·
      refine ⟨18979961467176420088458119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50613230579137120235888317 18979961467176420088458119)
      ·
        refine ⟨28469942200764630132687179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18979961467176420088458119 28469942200764630132687179)
        ·
          refine ⟨42704913301146945199030769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28469942200764630132687179 42704913301146945199030769)
          ·
            refine ⟨32028684975860208899273077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42704913301146945199030769 32028684975860208899273077)
            ·
              refine ⟨3002689216486894584306851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32028684975860208899273077 3002689216486894584306851)
              ·
                refine ⟨4504033824730341876460277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002689216486894584306851 4504033824730341876460277)
                ·
                  refine ⟨422253171068469550918151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504033824730341876460277 422253171068469550918151)
                  ·
                    rfl

theorem cell22_3700508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_3700508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700508 prefixEnd_3700508 := by exact prefixLift 3700508
  have htrace : WordTrace (prefixWord ++ tailWord_3700508) baseStart_3700508 baseEnd_3700508 := by
    simpa [prefixWord, tailWord_3700508, baseEnd_3700508] using wordTrace_append hprefix tailTrace_3700508
  have hstable : (prefixWord ++ tailWord_3700508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700508).length < 2 ^ (prefixWord ++ tailWord_3700508).sum := by decide
  have hdescent : baseEnd_3700508 < baseStart_3700508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700538 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_3700538 : Nat := 118140960795 + 3700538 * 2 ^ 59
def prefixEnd_3700538 : Nat := 4983230072969 + 3 ^ 40 * 3700538 * 2
def baseEnd_3700538 : Nat := 1266769782818498574504361

theorem tailTrace_3700538 : CollatzResearch.WordTrace tailWord_3700538 prefixEnd_3700538 1266769782818498574504361 := by
  unfold tailWord_3700538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742427266897575604823567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89979806045060201612862845 33742427266897575604823567)
  ·
    refine ⟨50613640900346363407235351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33742427266897575604823567 50613640900346363407235351)
    ·
      refine ⟨75920461350519545110853027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50613640900346363407235351 75920461350519545110853027)
      ·
        refine ⟨113880692025779317666279541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75920461350519545110853027 113880692025779317666279541)
        ·
          refine ⟨10676314877416811031213707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113880692025779317666279541 10676314877416811031213707)
          ·
            refine ⟨16014472316125216546820561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676314877416811031213707 16014472316125216546820561)
            ·
              refine ⟨12010854237093912410115421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16014472316125216546820561 12010854237093912410115421)
              ·
                refine ⟨4504070338910217153793283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12010854237093912410115421 4504070338910217153793283)
                ·
                  refine ⟨6756105508365325730689925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504070338910217153793283 6756105508365325730689925)
                  ·
                    refine ⟨1266769782818498574504361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756105508365325730689925 1266769782818498574504361)
                    ·
                      rfl

theorem cell22_3700538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_3700538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700538 prefixEnd_3700538 := by exact prefixLift 3700538
  have htrace : WordTrace (prefixWord ++ tailWord_3700538) baseStart_3700538 baseEnd_3700538 := by
    simpa [prefixWord, tailWord_3700538, baseEnd_3700538] using wordTrace_append hprefix tailTrace_3700538
  have hstable : (prefixWord ++ tailWord_3700538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700538).length < 2 ^ (prefixWord ++ tailWord_3700538).sum := by decide
  have hdescent : baseEnd_3700538 < baseStart_3700538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700572 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3700572 : Nat := 118140960795 + 3700572 * 2 ^ 59
def prefixEnd_3700572 : Nat := 4983230072969 + 3 ^ 40 * 3700572 * 2
def baseEnd_3700572 : Nat := 1266781421713333819154257

theorem tailTrace_3700572 : CollatzResearch.WordTrace tailWord_3700572 prefixEnd_3700572 1266781421713333819154257 := by
  unfold tailWord_3700572
  simp only [CollatzResearch.WordTrace]
  refine ⟨67485474574733563113015985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89980632766311417484021313 67485474574733563113015985)
  ·
    refine ⟨50614105931050172334761989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67485474574733563113015985 50614105931050172334761989)
    ·
      refine ⟨9490144862071907312767873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50614105931050172334761989 9490144862071907312767873)
      ·
        refine ⟨7117608646553930484575905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9490144862071907312767873 7117608646553930484575905)
        ·
          refine ⟨5338206484915447863431929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7117608646553930484575905 5338206484915447863431929)
          ·
            refine ⟨4003654863686585897573947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5338206484915447863431929 4003654863686585897573947)
            ·
              refine ⟨6005482295529878846360921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003654863686585897573947 6005482295529878846360921)
              ·
                refine ⟨4504111721647409134770691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005482295529878846360921 4504111721647409134770691)
                ·
                  refine ⟨6756167582471113702156037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504111721647409134770691 6756167582471113702156037)
                  ·
                    refine ⟨1266781421713333819154257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756167582471113702156037 1266781421713333819154257)
                    ·
                      rfl

theorem cell22_3700572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3700572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700572 prefixEnd_3700572 := by exact prefixLift 3700572
  have htrace : WordTrace (prefixWord ++ tailWord_3700572) baseStart_3700572 baseEnd_3700572 := by
    simpa [prefixWord, tailWord_3700572, baseEnd_3700572] using wordTrace_append hprefix tailTrace_3700572
  have hstable : (prefixWord ++ tailWord_3700572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700572).length < 2 ^ (prefixWord ++ tailWord_3700572).sum := by decide
  have hdescent : baseEnd_3700572 < baseStart_3700572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700583 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3700583 : Nat := 118140960795 + 3700583 * 2 ^ 59
def prefixEnd_3700583 : Nat := 4983230072969 + 3 ^ 40 * 3700583 * 2
def baseEnd_3700583 : Nat := 1266785187238133457129223

theorem tailTrace_3700583 : CollatzResearch.WordTrace tailWord_3700583 prefixEnd_3700583 1266785187238133457129223 := by
  unfold tailWord_3700583
  simp only [CollatzResearch.WordTrace]
  refine ⟨134971350352427275104682403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89980900234951516736454935 134971350352427275104682403)
  ·
    refine ⟨202457025528640912657023605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134971350352427275104682403 202457025528640912657023605)
    ·
      refine ⟨18980346143310085561595963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202457025528640912657023605 18980346143310085561595963)
      ·
        refine ⟨28470519214965128342393945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18980346143310085561595963 28470519214965128342393945)
        ·
          refine ⟨21352889411223846256795459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28470519214965128342393945 21352889411223846256795459)
          ·
            refine ⟨32029334116835769385193189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21352889411223846256795459 32029334116835769385193189)
            ·
              refine ⟨6005500146906706759723723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32029334116835769385193189 6005500146906706759723723)
              ·
                refine ⟨9008250220360060139585585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6005500146906706759723723 9008250220360060139585585)
                ·
                  refine ⟨6756187665270045104689189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9008250220360060139585585 6756187665270045104689189)
                  ·
                    refine ⟨1266785187238133457129223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756187665270045104689189 1266785187238133457129223)
                    ·
                      rfl

theorem cell22_3700583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3700583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700583 prefixEnd_3700583 := by exact prefixLift 3700583
  have htrace : WordTrace (prefixWord ++ tailWord_3700583) baseStart_3700583 baseEnd_3700583 := by
    simpa [prefixWord, tailWord_3700583, baseEnd_3700583] using wordTrace_append hprefix tailTrace_3700583
  have hstable : (prefixWord ++ tailWord_3700583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700583).length < 2 ^ (prefixWord ++ tailWord_3700583).sum := by decide
  have hdescent : baseEnd_3700583 < baseStart_3700583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700598 : List Nat := [5, 1, 1, 3, 2, 10]
def baseStart_3700598 : Nat := 118140960795 + 3700598 * 2 ^ 59
def prefixEnd_3700598 : Nat := 4983230072969 + 3 ^ 40 * 3700598 * 2
def baseEnd_3700598 : Nat := 15639386691909610098817

theorem tailTrace_3700598 : CollatzResearch.WordTrace tailWord_3700598 prefixEnd_3700598 15639386691909610098817 := by
  unfold tailWord_3700598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8435743590460808291654903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89981264964915288444318965 8435743590460808291654903)
  ·
    refine ⟨12653615385691212437482355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8435743590460808291654903 12653615385691212437482355)
    ·
      refine ⟨18980423078536818656223533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12653615385691212437482355 18980423078536818656223533)
      ·
        refine ⟨7117658654451306996083825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18980423078536818656223533 7117658654451306996083825)
        ·
          refine ⟨5338243990838480247062869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7117658654451306996083825 5338243990838480247062869)
          ·
            refine ⟨15639386691909610098817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5338243990838480247062869 15639386691909610098817)
            ·
              rfl

theorem cell22_3700598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 10].length) (baseStart_3700598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700598 prefixEnd_3700598 := by exact prefixLift 3700598
  have htrace : WordTrace (prefixWord ++ tailWord_3700598) baseStart_3700598 baseEnd_3700598 := by
    simpa [prefixWord, tailWord_3700598, baseEnd_3700598] using wordTrace_append hprefix tailTrace_3700598
  have hstable : (prefixWord ++ tailWord_3700598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700598).length < 2 ^ (prefixWord ++ tailWord_3700598).sum := by decide
  have hdescent : baseEnd_3700598 < baseStart_3700598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700611 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_3700611 : Nat := 118140960795 + 3700611 * 2 ^ 59
def prefixEnd_3700611 : Nat := 4983230072969 + 3 ^ 40 * 3700611 * 2
def baseEnd_3700611 : Nat := 1266794772210350717429137

theorem tailTrace_3700611 : CollatzResearch.WordTrace tailWord_3700611 prefixEnd_3700611 1266794772210350717429137 := by
  unfold tailWord_3700611
  simp only [CollatzResearch.WordTrace]
  refine ⟨134972371596325835886701687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89981581064217223924467791 134972371596325835886701687)
  ·
    refine ⟨202458557394488753830052531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134972371596325835886701687 202458557394488753830052531)
    ·
      refine ⟨303687836091733130745078797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202458557394488753830052531 303687836091733130745078797)
      ·
        refine ⟨113882938534399924029404549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303687836091733130745078797 113882938534399924029404549)
        ·
          refine ⟨21353050975199985755513353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113882938534399924029404549 21353050975199985755513353)
          ·
            refine ⟨16014788231399989316635015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21353050975199985755513353 16014788231399989316635015)
            ·
              refine ⟨24022182347099983974952523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16014788231399989316635015 24022182347099983974952523)
              ·
                refine ⟨36033273520649975962428785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24022182347099983974952523 36033273520649975962428785)
                ·
                  refine ⟨27024955140487481971821589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36033273520649975962428785 27024955140487481971821589)
                  ·
                    refine ⟨1266794772210350717429137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27024955140487481971821589 1266794772210350717429137)
                    ·
                      rfl

theorem cell22_3700611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_3700611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700611 prefixEnd_3700611 := by exact prefixLift 3700611
  have htrace : WordTrace (prefixWord ++ tailWord_3700611) baseStart_3700611 baseEnd_3700611 := by
    simpa [prefixWord, tailWord_3700611, baseEnd_3700611] using wordTrace_append hprefix tailTrace_3700611
  have hstable : (prefixWord ++ tailWord_3700611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700611).length < 2 ^ (prefixWord ++ tailWord_3700611).sum := by decide
  have hdescent : baseEnd_3700611 < baseStart_3700611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700613 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_3700613 : Nat := 118140960795 + 3700613 * 2 ^ 59
def prefixEnd_3700613 : Nat := 4983230072969 + 3 ^ 40 * 3700613 * 2
def baseEnd_3700613 : Nat := 1266795456851223378879131

theorem tailTrace_3700613 : CollatzResearch.WordTrace tailWord_3700613 prefixEnd_3700613 1266795456851223378879131 := by
  unfold tailWord_3700613
  simp only [CollatzResearch.WordTrace]
  refine ⟨134972444542318590228274493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89981629694879060152182995 134972444542318590228274493)
  ·
    refine ⟨50614666703369471335602935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134972444542318590228274493 50614666703369471335602935)
    ·
      refine ⟨75922000055054207003404403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50614666703369471335602935 75922000055054207003404403)
      ·
        refine ⟨113883000082581310505106605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75922000055054207003404403 113883000082581310505106605)
        ·
          refine ⟨42706125030967991439414977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113883000082581310505106605 42706125030967991439414977)
          ·
            refine ⟨32029593773225993579561233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42706125030967991439414977 32029593773225993579561233)
            ·
              refine ⟨24022195329919495184670925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32029593773225993579561233 24022195329919495184670925)
              ·
                refine ⟨9008323248719810694251597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24022195329919495184670925 9008323248719810694251597)
                ·
                  refine ⟨3378121218269929010344349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9008323248719810694251597 3378121218269929010344349)
                  ·
                    refine ⟨1266795456851223378879131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378121218269929010344349 1266795456851223378879131)
                    ·
                      rfl

theorem cell22_3700613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_3700613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700613 prefixEnd_3700613 := by exact prefixLift 3700613
  have htrace : WordTrace (prefixWord ++ tailWord_3700613) baseStart_3700613 baseEnd_3700613 := by
    simpa [prefixWord, tailWord_3700613, baseEnd_3700613] using wordTrace_append hprefix tailTrace_3700613
  have hstable : (prefixWord ++ tailWord_3700613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700613).length < 2 ^ (prefixWord ++ tailWord_3700613).sum := by decide
  have hdescent : baseEnd_3700613 < baseStart_3700613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700615 : List Nat := [1, 1, 4, 2, 5, 1, 1, 7]
def baseStart_3700615 : Nat := 118140960795 + 3700615 * 2 ^ 59
def prefixEnd_3700615 : Nat := 4983230072969 + 3 ^ 40 * 3700615 * 2
def baseEnd_3700615 : Nat := 140755126832455115592125

theorem tailTrace_3700615 : CollatzResearch.WordTrace tailWord_3700615 prefixEnd_3700615 140755126832455115592125 := by
  unfold tailWord_3700615
  simp only [CollatzResearch.WordTrace]
  refine ⟨134972517488311344569847299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89981678325540896379898199 134972517488311344569847299)
  ·
    refine ⟨202458776232467016854770949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134972517488311344569847299 202458776232467016854770949)
    ·
      refine ⟨37961020543587565660269553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202458776232467016854770949 37961020543587565660269553)
      ·
        refine ⟨28470765407690674245202165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37961020543587565660269553 28470765407690674245202165)
        ·
          refine ⟨2669134256971000710487703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28470765407690674245202165 2669134256971000710487703)
          ·
            refine ⟨4003701385456501065731555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669134256971000710487703 4003701385456501065731555)
            ·
              refine ⟨6005552078184751598597333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003701385456501065731555 6005552078184751598597333)
              ·
                refine ⟨140755126832455115592125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6005552078184751598597333 140755126832455115592125)
                ·
                  rfl

theorem cell22_3700615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 7].length) (baseStart_3700615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700615 prefixEnd_3700615 := by exact prefixLift 3700615
  have htrace : WordTrace (prefixWord ++ tailWord_3700615) baseStart_3700615 baseEnd_3700615 := by
    simpa [prefixWord, tailWord_3700615, baseEnd_3700615] using wordTrace_append hprefix tailTrace_3700615
  have hstable : (prefixWord ++ tailWord_3700615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700615).length < 2 ^ (prefixWord ++ tailWord_3700615).sum := by decide
  have hdescent : baseEnd_3700615 < baseStart_3700615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700647 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3700647 : Nat := 118140960795 + 3700647 * 2 ^ 59
def prefixEnd_3700647 : Nat := 4983230072969 + 3 ^ 40 * 3700647 * 2
def baseEnd_3700647 : Nat := 1266807095746058623529027

theorem tailTrace_3700647 : CollatzResearch.WordTrace tailWord_3700647 prefixEnd_3700647 1266807095746058623529027 := by
  unfold tailWord_3700647
  simp only [CollatzResearch.WordTrace]
  refine ⟨134973684624195414035012195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89982456416130276023341463 134973684624195414035012195)
  ·
    refine ⟨202460526936293121052518293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134973684624195414035012195 202460526936293121052518293)
    ·
      refine ⟨9490337200138740049336795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202460526936293121052518293 9490337200138740049336795)
      ·
        refine ⟨14235505800208110074005193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490337200138740049336795 14235505800208110074005193)
        ·
          refine ⟨10676629350156082555503895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14235505800208110074005193 10676629350156082555503895)
          ·
            refine ⟨16014944025234123833255843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676629350156082555503895 16014944025234123833255843)
            ·
              refine ⟨24022416037851185749883765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16014944025234123833255843 24022416037851185749883765)
              ·
                refine ⟨2252101503548548664051603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24022416037851185749883765 2252101503548548664051603)
                ·
                  refine ⟨3378152255322822996077405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252101503548548664051603 3378152255322822996077405)
                  ·
                    refine ⟨1266807095746058623529027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378152255322822996077405 1266807095746058623529027)
                    ·
                      rfl

theorem cell22_3700647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3700647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700647 prefixEnd_3700647 := by exact prefixLift 3700647
  have htrace : WordTrace (prefixWord ++ tailWord_3700647) baseStart_3700647 baseEnd_3700647 := by
    simpa [prefixWord, tailWord_3700647, baseEnd_3700647] using wordTrace_append hprefix tailTrace_3700647
  have hstable : (prefixWord ++ tailWord_3700647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700647).length < 2 ^ (prefixWord ++ tailWord_3700647).sum := by decide
  have hdescent : baseEnd_3700647 < baseStart_3700647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700705 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 4]
def baseStart_3700705 : Nat := 118140960795 + 3700705 * 2 ^ 59
def prefixEnd_3700705 : Nat := 4983230072969 + 3 ^ 40 * 3700705 * 2
def baseEnd_3700705 : Nat := 422275650110455268526283

theorem tailTrace_3700705 : CollatzResearch.WordTrace tailWord_3700705 prefixEnd_3700705 422275650110455268526283 := by
  unfold tailWord_3700705
  simp only [CollatzResearch.WordTrace]
  refine ⟨134975800057985289940623569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89983866705323526627082379 134975800057985289940623569)
  ·
    refine ⟨101231850043488967455467677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134975800057985289940623569 101231850043488967455467677)
    ·
      refine ⟨37961943766308362795800379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101231850043488967455467677 37961943766308362795800379)
      ·
        refine ⟨56942915649462544193700569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37961943766308362795800379 56942915649462544193700569)
        ·
          refine ⟨42707186737096908145275427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56942915649462544193700569 42707186737096908145275427)
          ·
            refine ⟨64060780105645362217913141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42707186737096908145275427 64060780105645362217913141)
            ·
              refine ⟨6005698134904252707929357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64060780105645362217913141 6005698134904252707929357)
              ·
                refine ⟨2252136800589094765473509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6005698134904252707929357 2252136800589094765473509)
                ·
                  refine ⟨422275650110455268526283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252136800589094765473509 422275650110455268526283)
                  ·
                    rfl

theorem cell22_3700705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_3700705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700705 prefixEnd_3700705 := by exact prefixLift 3700705
  have htrace : WordTrace (prefixWord ++ tailWord_3700705) baseStart_3700705 baseEnd_3700705 := by
    simpa [prefixWord, tailWord_3700705, baseEnd_3700705] using wordTrace_append hprefix tailTrace_3700705
  have hstable : (prefixWord ++ tailWord_3700705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700705).length < 2 ^ (prefixWord ++ tailWord_3700705).sum := by decide
  have hdescent : baseEnd_3700705 < baseStart_3700705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700825 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_3700825 : Nat := 118140960795 + 3700825 * 2 ^ 59
def prefixEnd_3700825 : Nat := 4983230072969 + 3 ^ 40 * 3700825 * 2
def baseEnd_3700825 : Nat := 1266868028783725492578481

theorem tailTrace_3700825 : CollatzResearch.WordTrace tailWord_3700825 prefixEnd_3700825 1266868028783725492578481 := by
  unfold tailWord_3700825
  simp only [CollatzResearch.WordTrace]
  refine ⟨134980176817550550434991929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89986784545033700289994619 134980176817550550434991929)
  ·
    refine ⟨101235132613162912826243947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134980176817550550434991929 101235132613162912826243947)
    ·
      refine ⟨151852698919744369239365921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101235132613162912826243947 151852698919744369239365921)
      ·
        refine ⟨113889524189808276929524441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151852698919744369239365921 113889524189808276929524441)
        ·
          refine ⟨85417143142356207697143331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113889524189808276929524441 85417143142356207697143331)
          ·
            refine ⟨128125714713534311545714997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85417143142356207697143331 128125714713534311545714997)
            ·
              refine ⟨12011785754393841707410781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128125714713534311545714997 12011785754393841707410781)
              ·
                refine ⟨4504419657897690640279043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12011785754393841707410781 4504419657897690640279043)
                ·
                  refine ⟨6756629486846535960418565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504419657897690640279043 6756629486846535960418565)
                  ·
                    refine ⟨1266868028783725492578481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756629486846535960418565 1266868028783725492578481)
                    ·
                      rfl

theorem cell22_3700825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_3700825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700825 prefixEnd_3700825 := by exact prefixLift 3700825
  have htrace : WordTrace (prefixWord ++ tailWord_3700825) baseStart_3700825 baseEnd_3700825 := by
    simpa [prefixWord, tailWord_3700825, baseEnd_3700825] using wordTrace_append hprefix tailTrace_3700825
  have hstable : (prefixWord ++ tailWord_3700825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700825).length < 2 ^ (prefixWord ++ tailWord_3700825).sum := by decide
  have hdescent : baseEnd_3700825 < baseStart_3700825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700829 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 5]
def baseStart_3700829 : Nat := 118140960795 + 3700829 * 2 ^ 59
def prefixEnd_3700829 : Nat := 4983230072969 + 3 ^ 40 * 3700829 * 2
def baseEnd_3700829 : Nat := 422289799355156938492823

theorem tailTrace_3700829 : CollatzResearch.WordTrace tailWord_3700829 prefixEnd_3700829 422289799355156938492823 := by
  unfold tailWord_3700829
  simp only [CollatzResearch.WordTrace]
  refine ⟨134980322709536059118137541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89986881806357372745425027 134980322709536059118137541)
  ·
    refine ⟨25308810508038011084650789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134980322709536059118137541 25308810508038011084650789)
    ·
      refine ⟨4745401970257127078372023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25308810508038011084650789 4745401970257127078372023)
      ·
        refine ⟨7118102955385690617558035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745401970257127078372023 7118102955385690617558035)
        ·
          refine ⟨10677154433078535926337053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118102955385690617558035 10677154433078535926337053)
          ·
            refine ⟨4003932912404450972376395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10677154433078535926337053 4003932912404450972376395)
            ·
              refine ⟨6005899368606676458564593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003932912404450972376395 6005899368606676458564593)
              ·
                refine ⟨4504424526455007343923445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005899368606676458564593 4504424526455007343923445)
                ·
                  refine ⟨422289799355156938492823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504424526455007343923445 422289799355156938492823)
                  ·
                    rfl

theorem cell22_3700829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_3700829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700829 prefixEnd_3700829 := by exact prefixLift 3700829
  have htrace : WordTrace (prefixWord ++ tailWord_3700829) baseStart_3700829 baseEnd_3700829 := by
    simpa [prefixWord, tailWord_3700829, baseEnd_3700829] using wordTrace_append hprefix tailTrace_3700829
  have hstable : (prefixWord ++ tailWord_3700829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700829).length < 2 ^ (prefixWord ++ tailWord_3700829).sum := by decide
  have hdescent : baseEnd_3700829 < baseStart_3700829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700855 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 1, 5]
def baseStart_3700855 : Nat := 118140960795 + 3700855 * 2 ^ 59
def prefixEnd_3700855 : Nat := 4983230072969 + 3 ^ 40 * 3700855 * 2
def baseEnd_3700855 : Nat := 1266878298396815414328389

theorem tailTrace_3700855 : CollatzResearch.WordTrace tailWord_3700855 prefixEnd_3700855 1266878298396815414328389 := by
  unfold tailWord_3700855
  simp only [CollatzResearch.WordTrace]
  refine ⟨134981271007441865558584019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89987514004961243705722679 134981271007441865558584019)
  ·
    refine ⟨202471906511162798337876029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134981271007441865558584019 202471906511162798337876029)
    ·
      refine ⟨75926964941686049376703511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202471906511162798337876029 75926964941686049376703511)
      ·
        refine ⟨113890447412529074065055267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75926964941686049376703511 113890447412529074065055267)
        ·
          refine ⟨170835671118793611097582901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113890447412529074065055267 170835671118793611097582901)
          ·
            refine ⟨16015844167386901040398397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170835671118793611097582901 16015844167386901040398397)
            ·
              refine ⟨6005941562770087890149399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16015844167386901040398397 6005941562770087890149399)
              ·
                refine ⟨9008912344155131835224099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6005941562770087890149399 9008912344155131835224099)
                ·
                  refine ⟨13513368516232697752836149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9008912344155131835224099 13513368516232697752836149)
                  ·
                    refine ⟨1266878298396815414328389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13513368516232697752836149 1266878298396815414328389)
                    ·
                      rfl

theorem cell22_3700855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_3700855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700855 prefixEnd_3700855 := by exact prefixLift 3700855
  have htrace : WordTrace (prefixWord ++ tailWord_3700855) baseStart_3700855 baseEnd_3700855 := by
    simpa [prefixWord, tailWord_3700855, baseEnd_3700855] using wordTrace_append hprefix tailTrace_3700855
  have hstable : (prefixWord ++ tailWord_3700855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700855).length < 2 ^ (prefixWord ++ tailWord_3700855).sum := by decide
  have hdescent : baseEnd_3700855 < baseStart_3700855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700872 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_3700872 : Nat := 118140960795 + 3700872 * 2 ^ 59
def prefixEnd_3700872 : Nat := 4983230072969 + 3 ^ 40 * 3700872 * 2
def baseEnd_3700872 : Nat := 1266884117844233036653337

theorem tailTrace_3700872 : CollatzResearch.WordTrace tailWord_3700872 prefixEnd_3700872 1266884117844233036653337 := by
  unfold tailWord_3700872
  simp only [CollatzResearch.WordTrace]
  refine ⟨67490945524190138730976435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89987927365586851641301913 67490945524190138730976435)
  ·
    refine ⟨101236418286285208096464653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67490945524190138730976435 101236418286285208096464653)
    ·
      refine ⟨37963656857356953036174245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101236418286285208096464653 37963656857356953036174245)
      ·
        refine ⟨7118185660754428694282671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37963656857356953036174245 7118185660754428694282671)
        ·
          refine ⟨10677278491131643041424007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118185660754428694282671 10677278491131643041424007)
          ·
            refine ⟨16015917736697464562136011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10677278491131643041424007 16015917736697464562136011)
            ·
              refine ⟨24023876605046196843204017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16015917736697464562136011 24023876605046196843204017)
              ·
                refine ⟨18017907453784647632403013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24023876605046196843204017 18017907453784647632403013)
                ·
                  refine ⟨3378357647584621431075565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18017907453784647632403013 3378357647584621431075565)
                  ·
                    refine ⟨1266884117844233036653337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378357647584621431075565 1266884117844233036653337)
                    ·
                      rfl

theorem cell22_3700872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_3700872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700872 prefixEnd_3700872 := by exact prefixLift 3700872
  have htrace : WordTrace (prefixWord ++ tailWord_3700872) baseStart_3700872 baseEnd_3700872 := by
    simpa [prefixWord, tailWord_3700872, baseEnd_3700872] using wordTrace_append hprefix tailTrace_3700872
  have hstable : (prefixWord ++ tailWord_3700872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700872).length < 2 ^ (prefixWord ++ tailWord_3700872).sum := by decide
  have hdescent : baseEnd_3700872 < baseStart_3700872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700874 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_3700874 : Nat := 118140960795 + 3700874 * 2 ^ 59
def prefixEnd_3700874 : Nat := 4983230072969 + 3 ^ 40 * 3700874 * 2
def baseEnd_3700874 : Nat := 422294934161701899367777

theorem tailTrace_3700874 : CollatzResearch.WordTrace tailWord_3700874 prefixEnd_3700874 422294934161701899367777 := by
  unfold tailWord_3700874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33745490998593257950881419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89987975996248687869017117 33745490998593257950881419)
  ·
    refine ⟨50618236497889886926322129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33745490998593257950881419 50618236497889886926322129)
    ·
      refine ⟨37963677373417415194741597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50618236497889886926322129 37963677373417415194741597)
      ·
        refine ⟨14236379015031530698028099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37963677373417415194741597 14236379015031530698028099)
        ·
          refine ⟨21354568522547296047042149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14236379015031530698028099 21354568522547296047042149)
          ·
            refine ⟨4003981597977618008820403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21354568522547296047042149 4003981597977618008820403)
            ·
              refine ⟨6005972396966427013230605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003981597977618008820403 6005972396966427013230605)
              ·
                refine ⟨2252239648862410129961477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6005972396966427013230605 2252239648862410129961477)
                ·
                  refine ⟨422294934161701899367777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252239648862410129961477 422294934161701899367777)
                  ·
                    rfl

theorem cell22_3700874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_3700874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700874 prefixEnd_3700874 := by exact prefixLift 3700874
  have htrace : WordTrace (prefixWord ++ tailWord_3700874) baseStart_3700874 baseEnd_3700874 := by
    simpa [prefixWord, tailWord_3700874, baseEnd_3700874] using wordTrace_append hprefix tailTrace_3700874
  have hstable : (prefixWord ++ tailWord_3700874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700874).length < 2 ^ (prefixWord ++ tailWord_3700874).sum := by decide
  have hdescent : baseEnd_3700874 < baseStart_3700874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700887 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 2, 4]
def baseStart_3700887 : Nat := 118140960795 + 3700887 * 2 ^ 59
def prefixEnd_3700887 : Nat := 4983230072969 + 3 ^ 40 * 3700887 * 2
def baseEnd_3700887 : Nat := 1266889252650777997528291

theorem tailTrace_3700887 : CollatzResearch.WordTrace tailWord_3700887 prefixEnd_3700887 1266889252650777997528291 := by
  unfold tailWord_3700887
  simp only [CollatzResearch.WordTrace]
  refine ⟨134982438143325935023748915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89988292095550623349165943 134982438143325935023748915)
  ·
    refine ⟨202473657214988902535623373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134982438143325935023748915 202473657214988902535623373)
    ·
      refine ⟨75927621455620838450858765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202473657214988902535623373 75927621455620838450858765)
      ·
        refine ⟨28472858045857814419072037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75927621455620838450858765 28472858045857814419072037)
        ·
          refine ⟨5338660883598340203576007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28472858045857814419072037 5338660883598340203576007)
          ·
            refine ⟨8007991325397510305364011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338660883598340203576007 8007991325397510305364011)
            ·
              refine ⟨12011986988096265458046017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007991325397510305364011 12011986988096265458046017)
              ·
                refine ⟨9008990241072199093534513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12011986988096265458046017 9008990241072199093534513)
                ·
                  refine ⟨6756742680804149320150885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9008990241072199093534513 6756742680804149320150885)
                  ·
                    refine ⟨1266889252650777997528291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756742680804149320150885 1266889252650777997528291)
                    ·
                      rfl

theorem cell22_3700887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_3700887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700887 prefixEnd_3700887 := by exact prefixLift 3700887
  have htrace : WordTrace (prefixWord ++ tailWord_3700887) baseStart_3700887 baseEnd_3700887 := by
    simpa [prefixWord, tailWord_3700887, baseEnd_3700887] using wordTrace_append hprefix tailTrace_3700887
  have hstable : (prefixWord ++ tailWord_3700887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700887).length < 2 ^ (prefixWord ++ tailWord_3700887).sum := by decide
  have hdescent : baseEnd_3700887 < baseStart_3700887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700906 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3700906 : Nat := 118140960795 + 3700906 * 2 ^ 59
def prefixEnd_3700906 : Nat := 4983230072969 + 3 ^ 40 * 3700906 * 2
def baseEnd_3700906 : Nat := 1266895756739068281303233

theorem tailTrace_3700906 : CollatzResearch.WordTrace tailWord_3700906 prefixEnd_3700906 1266895756739068281303233 := by
  unfold tailWord_3700906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33745782782564275317172643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89988754086838067512460381 33745782782564275317172643)
  ·
    refine ⟨50618674173846412975758965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33745782782564275317172643 50618674173846412975758965)
    ·
      refine ⟨4745500703798101216477403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50618674173846412975758965 4745500703798101216477403)
      ·
        refine ⟨7118251055697151824716105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745500703798101216477403 7118251055697151824716105)
        ·
          refine ⟨5338688291772863868537079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7118251055697151824716105 5338688291772863868537079)
          ·
            refine ⟨8008032437659295802805619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338688291772863868537079 8008032437659295802805619)
            ·
              refine ⟨12012048656488943704208429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008032437659295802805619 12012048656488943704208429)
              ·
                refine ⟨4504518246183353889078161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12012048656488943704208429 4504518246183353889078161)
                ·
                  refine ⟨3378388684637515416808621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4504518246183353889078161 3378388684637515416808621)
                  ·
                    refine ⟨1266895756739068281303233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378388684637515416808621 1266895756739068281303233)
                    ·
                      rfl

theorem cell22_3700906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3700906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700906 prefixEnd_3700906 := by exact prefixLift 3700906
  have htrace : WordTrace (prefixWord ++ tailWord_3700906) baseStart_3700906 baseEnd_3700906 := by
    simpa [prefixWord, tailWord_3700906, baseEnd_3700906] using wordTrace_append hprefix tailTrace_3700906
  have hstable : (prefixWord ++ tailWord_3700906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700906).length < 2 ^ (prefixWord ++ tailWord_3700906).sum := by decide
  have hdescent : baseEnd_3700906 < baseStart_3700906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700960 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_3700960 : Nat := 118140960795 + 3700960 * 2 ^ 59
def prefixEnd_3700960 : Nat := 4983230072969 + 3 ^ 40 * 3700960 * 2
def baseEnd_3700960 : Nat := 1266914242042630140453067

theorem tailTrace_3700960 : CollatzResearch.WordTrace tailWord_3700960 prefixEnd_3700960 1266914242042630140453067 := by
  unfold tailWord_3700960
  simp only [CollatzResearch.WordTrace]
  refine ⟨67492550336030734245578167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89990067114707645660770889 67492550336030734245578167)
  ·
    refine ⟨101238825504046101368367251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67492550336030734245578167 101238825504046101368367251)
    ·
      refine ⟨151858238256069152052550877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101238825504046101368367251 151858238256069152052550877)
      ·
        refine ⟨56946839346025932019706579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151858238256069152052550877 56946839346025932019706579)
        ·
          refine ⟨85420259019038898029559869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56946839346025932019706579 85420259019038898029559869)
          ·
            refine ⟨32032597132139586761084951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85420259019038898029559869 32032597132139586761084951)
            ·
              refine ⟨48048895698209380141627427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32032597132139586761084951 48048895698209380141627427)
              ·
                refine ⟨72073343547314070212441141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48048895698209380141627427 72073343547314070212441141)
                ·
                  refine ⟨6756875957560694082416357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72073343547314070212441141 6756875957560694082416357)
                  ·
                    refine ⟨1266914242042630140453067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756875957560694082416357 1266914242042630140453067)
                    ·
                      rfl

theorem cell22_3700960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_3700960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700960 prefixEnd_3700960 := by exact prefixLift 3700960
  have htrace : WordTrace (prefixWord ++ tailWord_3700960) baseStart_3700960 baseEnd_3700960 := by
    simpa [prefixWord, tailWord_3700960, baseEnd_3700960] using wordTrace_append hprefix tailTrace_3700960
  have hstable : (prefixWord ++ tailWord_3700960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700960).length < 2 ^ (prefixWord ++ tailWord_3700960).sum := by decide
  have hdescent : baseEnd_3700960 < baseStart_3700960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700975 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 8]
def baseStart_3700975 : Nat := 118140960795 + 3700975 * 2 ^ 59
def prefixEnd_3700975 : Nat := 4983230072969 + 3 ^ 40 * 3700975 * 2
def baseEnd_3700975 : Nat := 422306458949725033776007

theorem tailTrace_3700975 : CollatzResearch.WordTrace tailWord_3700975 prefixEnd_3700975 422306458949725033776007 := by
  unfold tailWord_3700975
  simp only [CollatzResearch.WordTrace]
  refine ⟨134985647767007126052952379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89990431844671417368634919 134985647767007126052952379)
  ·
    refine ⟨202478471650510689079428569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134985647767007126052952379 202478471650510689079428569)
    ·
      refine ⟨151858853737883016809571427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202478471650510689079428569 151858853737883016809571427)
      ·
        refine ⟨227788280606824525214357141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151858853737883016809571427 227788280606824525214357141)
        ·
          refine ⟨10677575653444899619422991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227788280606824525214357141 10677575653444899619422991)
          ·
            refine ⟨16016363480167349429134487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10677575653444899619422991 16016363480167349429134487)
            ·
              refine ⟨24024545220251024143701731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16016363480167349429134487 24024545220251024143701731)
              ·
                refine ⟨36036817830376536215552597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24024545220251024143701731 36036817830376536215552597)
                ·
                  refine ⟨422306458949725033776007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36036817830376536215552597 422306458949725033776007)
                  ·
                    rfl

theorem cell22_3700975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 8].length) (baseStart_3700975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700975 prefixEnd_3700975 := by exact prefixLift 3700975
  have htrace : WordTrace (prefixWord ++ tailWord_3700975) baseStart_3700975 baseEnd_3700975 := by
    simpa [prefixWord, tailWord_3700975, baseEnd_3700975] using wordTrace_append hprefix tailTrace_3700975
  have hstable : (prefixWord ++ tailWord_3700975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700975).length < 2 ^ (prefixWord ++ tailWord_3700975).sum := by decide
  have hdescent : baseEnd_3700975 < baseStart_3700975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700992 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 4]
def baseStart_3700992 : Nat := 118140960795 + 3700992 * 2 ^ 59
def prefixEnd_3700992 : Nat := 4983230072969 + 3 ^ 40 * 3700992 * 2
def baseEnd_3700992 : Nat := 422308398765530907884323

theorem tailTrace_3700992 : CollatzResearch.WordTrace tailWord_3700992 prefixEnd_3700992 422308398765530907884323 := by
  unfold tailWord_3700992
  simp only [CollatzResearch.WordTrace]
  refine ⟨67493133903972768978160615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89990845205297025304214153 67493133903972768978160615)
  ·
    refine ⟨101239700855959153467240923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67493133903972768978160615 101239700855959153467240923)
    ·
      refine ⟨151859551283938730200861385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101239700855959153467240923 151859551283938730200861385)
      ·
        refine ⟨113894663462954047650646039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151859551283938730200861385 113894663462954047650646039)
        ·
          refine ⟨170841995194431071475969059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113894663462954047650646039 170841995194431071475969059)
          ·
            refine ⟨256262992791646607213953589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170841995194431071475969059 256262992791646607213953589)
            ·
              refine ⟨24024655574216869426308149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256262992791646607213953589 24024655574216869426308149)
              ·
                refine ⟨2252311460082831508716389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24024655574216869426308149 2252311460082831508716389)
                ·
                  refine ⟨422308398765530907884323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252311460082831508716389 422308398765530907884323)
                  ·
                    rfl

theorem cell22_3700992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_3700992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700992 prefixEnd_3700992 := by exact prefixLift 3700992
  have htrace : WordTrace (prefixWord ++ tailWord_3700992) baseStart_3700992 baseEnd_3700992 := by
    simpa [prefixWord, tailWord_3700992, baseEnd_3700992] using wordTrace_append hprefix tailTrace_3700992
  have hstable : (prefixWord ++ tailWord_3700992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700992).length < 2 ^ (prefixWord ++ tailWord_3700992).sum := by decide
  have hdescent : baseEnd_3700992 < baseStart_3700992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701020 : List Nat := [2, 2, 3, 1, 1, 1, 1, 11]
def baseStart_3701020 : Nat := 118140960795 + 3701020 * 2 ^ 59
def prefixEnd_3701020 : Nat := 4983230072969 + 3 ^ 40 * 3701020 * 2
def baseEnd_3701020 : Nat := 140770531252089998216987

theorem tailTrace_3701020 : CollatzResearch.WordTrace tailWord_3701020 prefixEnd_3701020 140770531252089998216987 := by
  unfold tailWord_3701020
  simp only [CollatzResearch.WordTrace]
  refine ⟨67493644525922049369170257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89991526034562732492227009 67493644525922049369170257)
  ·
    refine ⟨50620233394441537026877693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67493644525922049369170257 50620233394441537026877693)
    ·
      refine ⟨18982587522915576385079135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50620233394441537026877693 18982587522915576385079135)
      ·
        refine ⟨28473881284373364577618703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18982587522915576385079135 28473881284373364577618703)
        ·
          refine ⟨42710821926560046866428055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28473881284373364577618703 42710821926560046866428055)
          ·
            refine ⟨64066232889840070299642083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42710821926560046866428055 64066232889840070299642083)
            ·
              refine ⟨96099349334760105449463125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64066232889840070299642083 96099349334760105449463125)
              ·
                refine ⟨140770531252089998216987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 96099349334760105449463125 140770531252089998216987)
                ·
                  rfl

theorem cell22_3701020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_3701020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701020 prefixEnd_3701020 := by exact prefixLift 3701020
  have htrace : WordTrace (prefixWord ++ tailWord_3701020) baseStart_3701020 baseEnd_3701020 := by
    simpa [prefixWord, tailWord_3701020, baseEnd_3701020] using wordTrace_append hprefix tailTrace_3701020
  have hstable : (prefixWord ++ tailWord_3701020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701020).length < 2 ^ (prefixWord ++ tailWord_3701020).sum := by decide
  have hdescent : baseEnd_3701020 < baseStart_3701020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701024 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_3701024 : Nat := 118140960795 + 3701024 * 2 ^ 59
def prefixEnd_3701024 : Nat := 4983230072969 + 3 ^ 40 * 3701024 * 2
def baseEnd_3701024 : Nat := 1266936150550555306852871

theorem tailTrace_3701024 : CollatzResearch.WordTrace tailWord_3701024 prefixEnd_3701024 1266936150550555306852871 := by
  unfold tailWord_3701024
  simp only [CollatzResearch.WordTrace]
  refine ⟨67493717471914803710743063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89991623295886404947657417 67493717471914803710743063)
  ·
    refine ⟨101240576207872205566114595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67493717471914803710743063 101240576207872205566114595)
    ·
      refine ⟨151860864311808308349171893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101240576207872205566114595 151860864311808308349171893)
      ·
        refine ⟨14236956029232028907734865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151860864311808308349171893 14236956029232028907734865)
        ·
          refine ⟨10677717021924021680801149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14236956029232028907734865 10677717021924021680801149)
          ·
            refine ⟨4004143883221508130300431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10677717021924021680801149 4004143883221508130300431)
            ·
              refine ⟨6006215824832262195450647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004143883221508130300431 6006215824832262195450647)
              ·
                refine ⟨9009323737248393293175971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006215824832262195450647 9009323737248393293175971)
                ·
                  refine ⟨13513985605872589939763957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009323737248393293175971 13513985605872589939763957)
                  ·
                    refine ⟨1266936150550555306852871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13513985605872589939763957 1266936150550555306852871)
                    ·
                      rfl

theorem cell22_3701024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_3701024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701024 prefixEnd_3701024 := by exact prefixLift 3701024
  have htrace : WordTrace (prefixWord ++ tailWord_3701024) baseStart_3701024 baseEnd_3701024 := by
    simpa [prefixWord, tailWord_3701024, baseEnd_3701024] using wordTrace_append hprefix tailTrace_3701024
  have hstable : (prefixWord ++ tailWord_3701024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701024).length < 2 ^ (prefixWord ++ tailWord_3701024).sum := by decide
  have hdescent : baseEnd_3701024 < baseStart_3701024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701127 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 6]
def baseStart_3701127 : Nat := 118140960795 + 3701127 * 2 ^ 59
def prefixEnd_3701127 : Nat := 4983230072969 + 3 ^ 40 * 3701127 * 2
def baseEnd_3701127 : Nat := 422323803185165790509185

theorem tailTrace_3701127 : CollatzResearch.WordTrace tailWord_3701127 prefixEnd_3701127 422323803185165790509185 := by
  unfold tailWord_3701127
  simp only [CollatzResearch.WordTrace]
  refine ⟨134991191662456456012485635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89994127774970970674990423 134991191662456456012485635)
  ·
    refine ⟨202486787493684684018728453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134991191662456456012485635 202486787493684684018728453)
    ·
      refine ⟨37966272655065878253511585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202486787493684684018728453 37966272655065878253511585)
      ·
        refine ⟨28474704491299408690133689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37966272655065878253511585 28474704491299408690133689)
        ·
          refine ⟨21356028368474556517600267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28474704491299408690133689 21356028368474556517600267)
          ·
            refine ⟨32034042552711834776400401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21356028368474556517600267 32034042552711834776400401)
            ·
              refine ⟨24025531914533876082300301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32034042552711834776400401 24025531914533876082300301)
              ·
                refine ⟨9009574467950203530862613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24025531914533876082300301 9009574467950203530862613)
                ·
                  refine ⟨422323803185165790509185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9009574467950203530862613 422323803185165790509185)
                  ·
                    rfl

theorem cell22_3701127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 6].length) (baseStart_3701127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701127 prefixEnd_3701127 := by exact prefixLift 3701127
  have htrace : WordTrace (prefixWord ++ tailWord_3701127) baseStart_3701127 baseEnd_3701127 := by
    simpa [prefixWord, tailWord_3701127, baseEnd_3701127] using wordTrace_append hprefix tailTrace_3701127
  have hstable : (prefixWord ++ tailWord_3701127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701127).length < 2 ^ (prefixWord ++ tailWord_3701127).sum := by decide
  have hdescent : baseEnd_3701127 < baseStart_3701127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701144 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_3701144 : Nat := 118140960795 + 3701144 * 2 ^ 59
def prefixEnd_3701144 : Nat := 4983230072969 + 3 ^ 40 * 3701144 * 2
def baseEnd_3701144 : Nat := 422325743000971664617501

theorem tailTrace_3701144 : CollatzResearch.WordTrace tailWord_3701144 prefixEnd_3701144 422325743000971664617501 := by
  unfold tailWord_3701144
  simp only [CollatzResearch.WordTrace]
  refine ⟨67495905851697433957927243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89994541135596578610569657 67495905851697433957927243)
  ·
    refine ⟨101243858777546150936890865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67495905851697433957927243 101243858777546150936890865)
    ·
      refine ⟨75932894083159613202668149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101243858777546150936890865 75932894083159613202668149)
      ·
        refine ⟨7118708820296213737750139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75932894083159613202668149 7118708820296213737750139)
        ·
          refine ⟨10678063230444320606625209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118708820296213737750139 10678063230444320606625209)
          ·
            refine ⟨8008547422833240454968907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10678063230444320606625209 8008547422833240454968907)
            ·
              refine ⟨12012821134249860682453361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008547422833240454968907 12012821134249860682453361)
              ·
                refine ⟨9009615850687395511840021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12012821134249860682453361 9009615850687395511840021)
                ·
                  refine ⟨422325743000971664617501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9009615850687395511840021 422325743000971664617501)
                  ·
                    rfl

theorem cell22_3701144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_3701144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701144 prefixEnd_3701144 := by exact prefixLift 3701144
  have htrace : WordTrace (prefixWord ++ tailWord_3701144) baseStart_3701144 baseEnd_3701144 := by
    simpa [prefixWord, tailWord_3701144, baseEnd_3701144] using wordTrace_append hprefix tailTrace_3701144
  have hstable : (prefixWord ++ tailWord_3701144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701144).length < 2 ^ (prefixWord ++ tailWord_3701144).sum := by decide
  have hdescent : baseEnd_3701144 < baseStart_3701144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701157 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3701157 : Nat := 118140960795 + 3701157 * 2 ^ 59
def prefixEnd_3701157 : Nat := 4983230072969 + 3 ^ 40 * 3701157 * 2
def baseEnd_3701157 : Nat := 1266981679168587293277463

theorem tailTrace_3701157 : CollatzResearch.WordTrace tailWord_3701157 prefixEnd_3701157 1266981679168587293277463 := by
  unfold tailWord_3701157
  simp only [CollatzResearch.WordTrace]
  refine ⟨134992285852347771136077725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89994857234898514090718483 134992285852347771136077725)
  ·
    refine ⟨50622107194630414176029147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134992285852347771136077725 50622107194630414176029147)
    ·
      refine ⟨75933160791945621264043721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50622107194630414176029147 75933160791945621264043721)
      ·
        refine ⟨56949870593959215948032791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75933160791945621264043721 56949870593959215948032791)
        ·
          refine ⟨85424805890938823922049187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56949870593959215948032791 85424805890938823922049187)
          ·
            refine ⟨128137208836408235883073781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85424805890938823922049187 128137208836408235883073781)
            ·
              refine ⟨12012863328413272114038167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128137208836408235883073781 12012863328413272114038167)
              ·
                refine ⟨18019294992619908171057251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012863328413272114038167 18019294992619908171057251)
                ·
                  refine ⟨27028942488929862256585877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18019294992619908171057251 27028942488929862256585877)
                  ·
                    refine ⟨1266981679168587293277463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27028942488929862256585877 1266981679168587293277463)
                    ·
                      rfl

theorem cell22_3701157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3701157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701157 prefixEnd_3701157 := by exact prefixLift 3701157
  have htrace : WordTrace (prefixWord ++ tailWord_3701157) baseStart_3701157 baseEnd_3701157 := by
    simpa [prefixWord, tailWord_3701157, baseEnd_3701157] using wordTrace_append hprefix tailTrace_3701157
  have hstable : (prefixWord ++ tailWord_3701157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701157).length < 2 ^ (prefixWord ++ tailWord_3701157).sum := by decide
  have hdescent : baseEnd_3701157 < baseStart_3701157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701159 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3701159 : Nat := 118140960795 + 3701159 * 2 ^ 59
def prefixEnd_3701159 : Nat := 4983230072969 + 3 ^ 40 * 3701159 * 2
def baseEnd_3701159 : Nat := 1266982363809459954727457

theorem tailTrace_3701159 : CollatzResearch.WordTrace tailWord_3701159 prefixEnd_3701159 1266982363809459954727457 := by
  unfold tailWord_3701159
  simp only [CollatzResearch.WordTrace]
  refine ⟨134992358798340525477650531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89994905865560350318433687 134992358798340525477650531)
  ·
    refine ⟨202488538197510788216475797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134992358798340525477650531 202488538197510788216475797)
    ·
      refine ⟨9491650228008318197647303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202488538197510788216475797 9491650228008318197647303)
      ·
        refine ⟨14237475342012477296470955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491650228008318197647303 14237475342012477296470955)
        ·
          refine ⟨21356213013018715944706433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237475342012477296470955 21356213013018715944706433)
          ·
            refine ⟨16017159759764036958529825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21356213013018715944706433 16017159759764036958529825)
            ·
              refine ⟨12012869819823027718897369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16017159759764036958529825 12012869819823027718897369)
              ·
                refine ⟨9009652364867270789173027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12012869819823027718897369 9009652364867270789173027)
                ·
                  refine ⟨13514478547300906183759541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009652364867270789173027 13514478547300906183759541)
                  ·
                    refine ⟨1266982363809459954727457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13514478547300906183759541 1266982363809459954727457)
                    ·
                      rfl

theorem cell22_3701159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3701159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701159 prefixEnd_3701159 := by exact prefixLift 3701159
  have htrace : WordTrace (prefixWord ++ tailWord_3701159) baseStart_3701159 baseEnd_3701159 := by
    simpa [prefixWord, tailWord_3701159, baseEnd_3701159] using wordTrace_append hprefix tailTrace_3701159
  have hstable : (prefixWord ++ tailWord_3701159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701159).length < 2 ^ (prefixWord ++ tailWord_3701159).sum := by decide
  have hdescent : baseEnd_3701159 < baseStart_3701159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701217 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 9]
def baseStart_3701217 : Nat := 118140960795 + 3701217 * 2 ^ 59
def prefixEnd_3701217 : Nat := 4983230072969 + 3 ^ 40 * 3701217 * 2
def baseEnd_3701217 : Nat := 422334072798255712259093

theorem tailTrace_3701217 : CollatzResearch.WordTrace tailWord_3701217 prefixEnd_3701217 422334072798255712259093 := by
  unfold tailWord_3701217
  simp only [CollatzResearch.WordTrace]
  refine ⟨134994474232130401383261905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89996316154753600922174603 134994474232130401383261905)
  ·
    refine ⟨101245855674097801037446429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134994474232130401383261905 101245855674097801037446429)
    ·
      refine ⟨37967195877786675389042411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101245855674097801037446429 37967195877786675389042411)
      ·
        refine ⟨56950793816680013083563617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37967195877786675389042411 56950793816680013083563617)
        ·
          refine ⟨42713095362510009812672713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56950793816680013083563617 42713095362510009812672713)
          ·
            refine ⟨32034821521882507359504535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42713095362510009812672713 32034821521882507359504535)
            ·
              refine ⟨48052232282823761039256803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32034821521882507359504535 48052232282823761039256803)
              ·
                refine ⟨72078348424235641558885205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48052232282823761039256803 72078348424235641558885205)
                ·
                  refine ⟨422334072798255712259093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72078348424235641558885205 422334072798255712259093)
                  ·
                    rfl

theorem cell22_3701217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_3701217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701217 prefixEnd_3701217 := by exact prefixLift 3701217
  have htrace : WordTrace (prefixWord ++ tailWord_3701217) baseStart_3701217 baseEnd_3701217 := by
    simpa [prefixWord, tailWord_3701217, baseEnd_3701217] using wordTrace_append hprefix tailTrace_3701217
  have hstable : (prefixWord ++ tailWord_3701217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701217).length < 2 ^ (prefixWord ++ tailWord_3701217).sum := by decide
  have hdescent : baseEnd_3701217 < baseStart_3701217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701311 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 2, 3]
def baseStart_3701311 : Nat := 118140960795 + 3701311 * 2 ^ 59
def prefixEnd_3701311 : Nat := 4983230072969 + 3 ^ 40 * 3701311 * 2
def baseEnd_3701311 : Nat := 1267034396515782224926991

theorem tailTrace_3701311 : CollatzResearch.WordTrace tailWord_3701311 prefixEnd_3701311 1267034396515782224926991 := by
  unfold tailWord_3701311
  simp only [CollatzResearch.WordTrace]
  refine ⟨134997902693789855437183787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89998601795859903624789191 134997902693789855437183787)
  ·
    refine ⟨202496854040684783155775681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134997902693789855437183787 202496854040684783155775681)
    ·
      refine ⟨151872640530513587366831761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202496854040684783155775681 151872640530513587366831761)
      ·
        refine ⟨113904480397885190525123821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151872640530513587366831761 113904480397885190525123821)
        ·
          refine ⟨42714180149206946446921433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113904480397885190525123821 42714180149206946446921433)
          ·
            refine ⟨32035635111905209835191075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42714180149206946446921433 32035635111905209835191075)
            ·
              refine ⟨48053452667857814752786613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32035635111905209835191075 48053452667857814752786613)
              ·
                refine ⟨4505011187611670133073745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48053452667857814752786613 4505011187611670133073745)
                ·
                  refine ⟨3378758390708752599805309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505011187611670133073745 3378758390708752599805309)
                  ·
                    refine ⟨1267034396515782224926991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378758390708752599805309 1267034396515782224926991)
                    ·
                      rfl

theorem cell22_3701311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_3701311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701311 prefixEnd_3701311 := by exact prefixLift 3701311
  have htrace : WordTrace (prefixWord ++ tailWord_3701311) baseStart_3701311 baseEnd_3701311 := by
    simpa [prefixWord, tailWord_3701311, baseEnd_3701311] using wordTrace_append hprefix tailTrace_3701311
  have hstable : (prefixWord ++ tailWord_3701311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701311).length < 2 ^ (prefixWord ++ tailWord_3701311).sum := by decide
  have hdescent : baseEnd_3701311 < baseStart_3701311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701326 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3701326 : Nat := 118140960795 + 3701326 * 2 ^ 59
def prefixEnd_3701326 : Nat := 4983230072969 + 3 ^ 40 * 3701326 * 2
def baseEnd_3701326 : Nat := 1267039531322327185801945

theorem tailTrace_3701326 : CollatzResearch.WordTrace tailWord_3701326 prefixEnd_3701326 1267039531322327185801945 := by
  unfold tailWord_3701326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16874806223591939124872479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89998966525823675332653221 16874806223591939124872479)
  ·
    refine ⟨25312209335387908687308719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16874806223591939124872479 25312209335387908687308719)
    ·
      refine ⟨37968314003081863030963079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25312209335387908687308719 37968314003081863030963079)
      ·
        refine ⟨56952471004622794546444619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37968314003081863030963079 56952471004622794546444619)
        ·
          refine ⟨85428706506934191819666929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56952471004622794546444619 85428706506934191819666929)
          ·
            refine ⟨64071529880200643864750197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85428706506934191819666929 64071529880200643864750197)
            ·
              refine ⟨6006705926268810362320331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64071529880200643864750197 6006705926268810362320331)
              ·
                refine ⟨9010058889403215543480497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006705926268810362320331 9010058889403215543480497)
                ·
                  refine ⟨6757544167052411657610373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9010058889403215543480497 6757544167052411657610373)
                  ·
                    refine ⟨1267039531322327185801945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6757544167052411657610373 1267039531322327185801945)
                    ·
                      rfl

theorem cell22_3701326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3701326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701326 prefixEnd_3701326 := by exact prefixLift 3701326
  have htrace : WordTrace (prefixWord ++ tailWord_3701326) baseStart_3701326 baseEnd_3701326 := by
    simpa [prefixWord, tailWord_3701326, baseEnd_3701326] using wordTrace_append hprefix tailTrace_3701326
  have hstable : (prefixWord ++ tailWord_3701326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701326).length < 2 ^ (prefixWord ++ tailWord_3701326).sum := by decide
  have hdescent : baseEnd_3701326 < baseStart_3701326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701356 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_3701356 : Nat := 118140960795 + 3701356 * 2 ^ 59
def prefixEnd_3701356 : Nat := 4983230072969 + 3 ^ 40 * 3701356 * 2
def baseEnd_3701356 : Nat := 1267049800935417107551853

theorem tailTrace_3701356 : CollatzResearch.WordTrace tailWord_3701356 prefixEnd_3701356 1267049800935417107551853 := by
  unfold tailWord_3701356
  simp only [CollatzResearch.WordTrace]
  refine ⟨67499771989313414061285961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89999695985751218748381281 67499771989313414061285961)
  ·
    refine ⟨50624828991985060545964471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67499771989313414061285961 50624828991985060545964471)
    ·
      refine ⟨75937243487977590818946707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50624828991985060545964471 75937243487977590818946707)
      ·
        refine ⟨113905865231966386228420061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75937243487977590818946707 113905865231966386228420061)
        ·
          refine ⟨42714699461987394835657523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113905865231966386228420061 42714699461987394835657523)
          ·
            refine ⟨64072049192981092253486285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42714699461987394835657523 64072049192981092253486285)
            ·
              refine ⟨24027018447367909595057357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64072049192981092253486285 24027018447367909595057357)
              ·
                refine ⟨9010131917762966098146509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24027018447367909595057357 9010131917762966098146509)
                ·
                  refine ⟨3378799469161112286804941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9010131917762966098146509 3378799469161112286804941)
                  ·
                    refine ⟨1267049800935417107551853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378799469161112286804941 1267049800935417107551853)
                    ·
                      rfl

theorem cell22_3701356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_3701356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701356 prefixEnd_3701356 := by exact prefixLift 3701356
  have htrace : WordTrace (prefixWord ++ tailWord_3701356) baseStart_3701356 baseEnd_3701356 := by
    simpa [prefixWord, tailWord_3701356, baseEnd_3701356] using wordTrace_append hprefix tailTrace_3701356
  have hstable : (prefixWord ++ tailWord_3701356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701356).length < 2 ^ (prefixWord ++ tailWord_3701356).sum := by decide
  have hdescent : baseEnd_3701356 < baseStart_3701356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701450 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_3701450 : Nat := 118140960795 + 3701450 * 2 ^ 59
def prefixEnd_3701450 : Nat := 4983230072969 + 3 ^ 40 * 3701450 * 2
def baseEnd_3701450 : Nat := 1267081979056432195701565

theorem tailTrace_3701450 : CollatzResearch.WordTrace tailWord_3701450 prefixEnd_3701450 1267081979056432195701565 := by
  unfold tailWord_3701450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33750743110071570544123451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90001981626857521450995869 33750743110071570544123451)
  ·
    refine ⟨50626114665107355816185177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33750743110071570544123451 50626114665107355816185177)
    ·
      refine ⟨37969585998830516862138883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50626114665107355816185177 37969585998830516862138883)
      ·
        refine ⟨56954378998245775293208325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37969585998830516862138883 56954378998245775293208325)
        ·
          refine ⟨10678946062171082867476561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56954378998245775293208325 10678946062171082867476561)
          ·
            refine ⟨8009209546628312150607421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10678946062171082867476561 8009209546628312150607421)
            ·
              refine ⟨3003453579985617056477783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8009209546628312150607421 3003453579985617056477783)
              ·
                refine ⟨4505180369978425584716675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003453579985617056477783 4505180369978425584716675)
                ·
                  refine ⟨6757770554967638377075013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505180369978425584716675 6757770554967638377075013)
                  ·
                    refine ⟨1267081979056432195701565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6757770554967638377075013 1267081979056432195701565)
                    ·
                      rfl

theorem cell22_3701450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_3701450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701450 prefixEnd_3701450 := by exact prefixLift 3701450
  have htrace : WordTrace (prefixWord ++ tailWord_3701450) baseStart_3701450 baseEnd_3701450 := by
    simpa [prefixWord, tailWord_3701450, baseEnd_3701450] using wordTrace_append hprefix tailTrace_3701450
  have hstable : (prefixWord ++ tailWord_3701450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701450).length < 2 ^ (prefixWord ++ tailWord_3701450).sum := by decide
  have hdescent : baseEnd_3701450 < baseStart_3701450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701463 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 2, 3]
def baseStart_3701463 : Nat := 118140960795 + 3701463 * 2 ^ 59
def prefixEnd_3701463 : Nat := 4983230072969 + 3 ^ 40 * 3701463 * 2
def baseEnd_3701463 : Nat := 1267086429222104495126525

theorem tailTrace_3701463 : CollatzResearch.WordTrace tailWord_3701463 prefixEnd_3701463 1267086429222104495126525 := by
  unfold tailWord_3701463
  simp only [CollatzResearch.WordTrace]
  refine ⟨135003446589239185396717043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90002297726159456931144695 135003446589239185396717043)
  ·
    refine ⟨202505169883858778095075565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135003446589239185396717043 202505169883858778095075565)
    ·
      refine ⟨75939438706447041785653337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202505169883858778095075565 75939438706447041785653337)
      ·
        refine ⟨56954579029835281339240003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75939438706447041785653337 56954579029835281339240003)
        ·
          refine ⟨85431868544752922008860005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56954579029835281339240003 85431868544752922008860005)
          ·
            refine ⟨16018475352141172876661251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85431868544752922008860005 16018475352141172876661251)
            ·
              refine ⟨24027713028211759314991877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16018475352141172876661251 24027713028211759314991877)
              ·
                refine ⟨4505196192789704871560977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24027713028211759314991877 4505196192789704871560977)
                ·
                  refine ⟨3378897144592278653670733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505196192789704871560977 3378897144592278653670733)
                  ·
                    refine ⟨1267086429222104495126525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378897144592278653670733 1267086429222104495126525)
                    ·
                      rfl

theorem cell22_3701463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_3701463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701463 prefixEnd_3701463 := by exact prefixLift 3701463
  have htrace : WordTrace (prefixWord ++ tailWord_3701463) baseStart_3701463 baseEnd_3701463 := by
    simpa [prefixWord, tailWord_3701463, baseEnd_3701463] using wordTrace_append hprefix tailTrace_3701463
  have hstable : (prefixWord ++ tailWord_3701463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701463).length < 2 ^ (prefixWord ++ tailWord_3701463).sum := by decide
  have hdescent : baseEnd_3701463 < baseStart_3701463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701476 : List Nat := [2, 3, 1, 1, 1, 4, 3, 7]
def baseStart_3701476 : Nat := 118140960795 + 3701476 * 2 ^ 59
def prefixEnd_3701476 : Nat := 4983230072969 + 3 ^ 40 * 3701476 * 2
def baseEnd_3701476 : Nat := 140787875487530754950165

theorem tailTrace_3701476 : CollatzResearch.WordTrace tailWord_3701476 prefixEnd_3701476 140787875487530754950165 := by
  unfold tailWord_3701476
  simp only [CollatzResearch.WordTrace]
  refine ⟨67501960369096044308470141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90002613825461392411293521 67501960369096044308470141)
  ·
    refine ⟨25313235138411016615676303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67501960369096044308470141 25313235138411016615676303)
    ·
      refine ⟨37969852707616524923514455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25313235138411016615676303 37969852707616524923514455)
      ·
        refine ⟨56954779061424787385271683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37969852707616524923514455 56954779061424787385271683)
        ·
          refine ⟨85432168592137181077907525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56954779061424787385271683 85432168592137181077907525)
          ·
            refine ⟨16018531611025721452107661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85432168592137181077907525 16018531611025721452107661)
            ·
              refine ⟨6006949354134645544540373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16018531611025721452107661 6006949354134645544540373)
              ·
                refine ⟨140787875487530754950165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6006949354134645544540373 140787875487530754950165)
                ·
                  rfl

theorem cell22_3701476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_3701476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701476 prefixEnd_3701476 := by exact prefixLift 3701476
  have htrace : WordTrace (prefixWord ++ tailWord_3701476) baseStart_3701476 baseEnd_3701476 := by
    simpa [prefixWord, tailWord_3701476, baseEnd_3701476] using wordTrace_append hprefix tailTrace_3701476
  have hstable : (prefixWord ++ tailWord_3701476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701476).length < 2 ^ (prefixWord ++ tailWord_3701476).sum := by decide
  have hdescent : baseEnd_3701476 < baseStart_3701476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701508 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_3701508 : Nat := 118140960795 + 3701508 * 2 ^ 59
def prefixEnd_3701508 : Nat := 4983230072969 + 3 ^ 40 * 3701508 * 2
def baseEnd_3701508 : Nat := 1267101833641739377751387

theorem tailTrace_3701508 : CollatzResearch.WordTrace tailWord_3701508 prefixEnd_3701508 1267101833641739377751387 := by
  unfold tailWord_3701508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67502543937038079041052589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90003391916050772054736785 67502543937038079041052589)
  ·
    refine ⟨25313453976389279640394721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67502543937038079041052589 25313453976389279640394721)
    ·
      refine ⟨18985090482291959730296041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25313453976389279640394721 18985090482291959730296041)
      ·
        refine ⟨14238817861718969797722031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18985090482291959730296041 14238817861718969797722031)
        ·
          refine ⟨21358226792578454696583047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238817861718969797722031 21358226792578454696583047)
          ·
            refine ⟨32037340188867682044874571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21358226792578454696583047 32037340188867682044874571)
            ·
              refine ⟨48056010283301523067311857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32037340188867682044874571 48056010283301523067311857)
              ·
                refine ⟨36042007712476142300483893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48056010283301523067311857 36042007712476142300483893)
                ·
                  refine ⟨3378938223044638340670365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36042007712476142300483893 3378938223044638340670365)
                  ·
                    refine ⟨1267101833641739377751387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378938223044638340670365 1267101833641739377751387)
                    ·
                      rfl

theorem cell22_3701508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_3701508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701508 prefixEnd_3701508 := by exact prefixLift 3701508
  have htrace : WordTrace (prefixWord ++ tailWord_3701508) baseStart_3701508 baseEnd_3701508 := by
    simpa [prefixWord, tailWord_3701508, baseEnd_3701508] using wordTrace_append hprefix tailTrace_3701508
  have hstable : (prefixWord ++ tailWord_3701508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701508).length < 2 ^ (prefixWord ++ tailWord_3701508).sum := by decide
  have hdescent : baseEnd_3701508 < baseStart_3701508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701525 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_3701525 : Nat := 118140960795 + 3701525 * 2 ^ 59
def prefixEnd_3701525 : Nat := 4983230072969 + 3 ^ 40 * 3701525 * 2
def baseEnd_3701525 : Nat := 1267107653089157000076335

theorem tailTrace_3701525 : CollatzResearch.WordTrace tailWord_3701525 prefixEnd_3701525 1267107653089157000076335 := by
  unfold tailWord_3701525
  simp only [CollatzResearch.WordTrace]
  refine ⟨135005707915014569985474029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90003805276676379990316019 135005707915014569985474029)
  ·
    refine ⟨50627140468130463744552761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135005707915014569985474029 50627140468130463744552761)
    ·
      refine ⟨37970355351097847808414571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50627140468130463744552761 37970355351097847808414571)
      ·
        refine ⟨56955533026646771712621857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37970355351097847808414571 56955533026646771712621857)
        ·
          refine ⟨42716649769985078784466393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56955533026646771712621857 42716649769985078784466393)
          ·
            refine ⟨32037487327488809088349795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42716649769985078784466393 32037487327488809088349795)
            ·
              refine ⟨48056230991233213632524693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32037487327488809088349795 48056230991233213632524693)
              ·
                refine ⟨2252635827714056889024595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48056230991233213632524693 2252635827714056889024595)
                ·
                  refine ⟨3378953741571085333536893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252635827714056889024595 3378953741571085333536893)
                  ·
                    refine ⟨1267107653089157000076335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3378953741571085333536893 1267107653089157000076335)
                    ·
                      rfl

theorem cell22_3701525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_3701525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701525 prefixEnd_3701525 := by exact prefixLift 3701525
  have htrace : WordTrace (prefixWord ++ tailWord_3701525) baseStart_3701525 baseEnd_3701525 := by
    simpa [prefixWord, tailWord_3701525, baseEnd_3701525] using wordTrace_append hprefix tailTrace_3701525
  have hstable : (prefixWord ++ tailWord_3701525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701525).length < 2 ^ (prefixWord ++ tailWord_3701525).sum := by decide
  have hdescent : baseEnd_3701525 < baseStart_3701525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701611 : List Nat := [1, 1, 1, 1, 2, 2, 6, 8]
def baseStart_3701611 : Nat := 118140960795 + 3701611 * 2 ^ 59
def prefixEnd_3701611 : Nat := 4983230072969 + 3 ^ 40 * 3701611 * 2
def baseEnd_3701611 : Nat := 140793010294075715825119

theorem tailTrace_3701611 : CollatzResearch.WordTrace tailWord_3701611 prefixEnd_3701611 140793010294075715825119 := by
  unfold tailWord_3701611
  simp only [CollatzResearch.WordTrace]
  refine ⟨135008844592703006673104687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90005896395135337782069791 135008844592703006673104687)
  ·
    refine ⟨202513266889054510009657031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135008844592703006673104687 202513266889054510009657031)
    ·
      refine ⟨303769900333581765014485547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202513266889054510009657031 303769900333581765014485547)
      ·
        refine ⟨455654850500372647521728321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303769900333581765014485547 455654850500372647521728321)
        ·
          refine ⟨341741137875279485641296241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455654850500372647521728321 341741137875279485641296241)
          ·
            refine ⟨256305853406459614230972181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341741137875279485641296241 256305853406459614230972181)
            ·
              refine ⟨12014336878427794417076821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256305853406459614230972181 12014336878427794417076821)
              ·
                refine ⟨140793010294075715825119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12014336878427794417076821 140793010294075715825119)
                ·
                  rfl

theorem cell22_3701611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 8].length) (baseStart_3701611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701611 prefixEnd_3701611 := by exact prefixLift 3701611
  have htrace : WordTrace (prefixWord ++ tailWord_3701611) baseStart_3701611 baseEnd_3701611 := by
    simpa [prefixWord, tailWord_3701611, baseEnd_3701611] using wordTrace_append hprefix tailTrace_3701611
  have hstable : (prefixWord ++ tailWord_3701611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701611).length < 2 ^ (prefixWord ++ tailWord_3701611).sum := by decide
  have hdescent : baseEnd_3701611 < baseStart_3701611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701688 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_3701688 : Nat := 118140960795 + 3701688 * 2 ^ 59
def prefixEnd_3701688 : Nat := 4983230072969 + 3 ^ 40 * 3701688 * 2
def baseEnd_3701688 : Nat := 1267163451320278908250835

theorem tailTrace_3701688 : CollatzResearch.WordTrace tailWord_3701688 prefixEnd_3701688 1267163451320278908250835 := by
  unfold tailWord_3701688
  simp only [CollatzResearch.WordTrace]
  refine ⟨67505826506712024411828859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90007768675616032549105145 67505826506712024411828859)
  ·
    refine ⟨101258739760068036617743289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67505826506712024411828859 101258739760068036617743289)
    ·
      refine ⟨75944054820051027463307467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101258739760068036617743289 75944054820051027463307467)
      ·
        refine ⟨113916082230076541194961201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75944054820051027463307467 113916082230076541194961201)
        ·
          refine ⟨85437061672557405896220901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113916082230076541194961201 85437061672557405896220901)
          ·
            refine ⟨16019449063604513605541419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85437061672557405896220901 16019449063604513605541419)
            ·
              refine ⟨24029173595406770408312129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16019449063604513605541419 24029173595406770408312129)
              ·
                refine ⟨18021880196555077806234097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24029173595406770408312129 18021880196555077806234097)
                ·
                  refine ⟨13516410147416308354675573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18021880196555077806234097 13516410147416308354675573)
                  ·
                    refine ⟨1267163451320278908250835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13516410147416308354675573 1267163451320278908250835)
                    ·
                      rfl

theorem cell22_3701688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_3701688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701688 prefixEnd_3701688 := by exact prefixLift 3701688
  have htrace : WordTrace (prefixWord ++ tailWord_3701688) baseStart_3701688 baseEnd_3701688 := by
    simpa [prefixWord, tailWord_3701688, baseEnd_3701688] using wordTrace_append hprefix tailTrace_3701688
  have hstable : (prefixWord ++ tailWord_3701688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701688).length < 2 ^ (prefixWord ++ tailWord_3701688).sum := by decide
  have hdescent : baseEnd_3701688 < baseStart_3701688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701703 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3701703 : Nat := 118140960795 + 3701703 * 2 ^ 59
def prefixEnd_3701703 : Nat := 4983230072969 + 3 ^ 40 * 3701703 * 2
def baseEnd_3701703 : Nat := 1267168586126823869125789

theorem tailTrace_3701703 : CollatzResearch.WordTrace tailWord_3701703 prefixEnd_3701703 1267168586126823869125789 := by
  unfold tailWord_3701703
  simp only [CollatzResearch.WordTrace]
  refine ⟨135012200108369706385453763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90008133405579804256969175 135012200108369706385453763)
  ·
    refine ⟨202518300162554559578180645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135012200108369706385453763 202518300162554559578180645)
    ·
      refine ⟨37972181280478979920908871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202518300162554559578180645 37972181280478979920908871)
      ·
        refine ⟨56958271920718469881363307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37972181280478979920908871 56958271920718469881363307)
        ·
          refine ⟨85437407881077704822044961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56958271920718469881363307 85437407881077704822044961)
          ·
            refine ⟨64078055910808278616533721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85437407881077704822044961 64078055910808278616533721)
            ·
              refine ⟨48058541933106208962400291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64078055910808278616533721 48058541933106208962400291)
              ·
                refine ⟨72087812899659313443600437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48058541933106208962400291 72087812899659313443600437)
                ·
                  refine ⟨6758232459343060635337541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72087812899659313443600437 6758232459343060635337541)
                  ·
                    refine ⟨1267168586126823869125789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758232459343060635337541 1267168586126823869125789)
                    ·
                      rfl

theorem cell22_3701703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3701703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701703 prefixEnd_3701703 := by exact prefixLift 3701703
  have htrace : WordTrace (prefixWord ++ tailWord_3701703) baseStart_3701703 baseEnd_3701703 := by
    simpa [prefixWord, tailWord_3701703, baseEnd_3701703] using wordTrace_append hprefix tailTrace_3701703
  have hstable : (prefixWord ++ tailWord_3701703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701703).length < 2 ^ (prefixWord ++ tailWord_3701703).sum := by decide
  have hdescent : baseEnd_3701703 < baseStart_3701703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701720 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_3701720 : Nat := 118140960795 + 3701720 * 2 ^ 59
def prefixEnd_3701720 : Nat := 4983230072969 + 3 ^ 40 * 3701720 * 2
def baseEnd_3701720 : Nat := 1267174405574241491450737

theorem tailTrace_3701720 : CollatzResearch.WordTrace tailWord_3701720 prefixEnd_3701720 1267174405574241491450737 := by
  unfold tailWord_3701720
  simp only [CollatzResearch.WordTrace]
  refine ⟨67506410074654059144411307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90008546766205412192548409 67506410074654059144411307)
  ·
    refine ⟨101259615111981088716616961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67506410074654059144411307 101259615111981088716616961)
    ·
      refine ⟨75944711333985816537462721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101259615111981088716616961 75944711333985816537462721)
      ·
        refine ⟨56958533500489362403097041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75944711333985816537462721 56958533500489362403097041)
        ·
          refine ⟨42718900125367021802322781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56958533500489362403097041 42718900125367021802322781)
          ·
            refine ⟨16019587547012633175871043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42718900125367021802322781 16019587547012633175871043)
            ·
              refine ⟨24029381320518949763806565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16019587547012633175871043 24029381320518949763806565)
              ·
                refine ⟨4505508997597303080713731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24029381320518949763806565 4505508997597303080713731)
                ·
                  refine ⟨6758263496395954621070597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505508997597303080713731 6758263496395954621070597)
                  ·
                    refine ⟨1267174405574241491450737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758263496395954621070597 1267174405574241491450737)
                    ·
                      rfl

theorem cell22_3701720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_3701720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701720 prefixEnd_3701720 := by exact prefixLift 3701720
  have htrace : WordTrace (prefixWord ++ tailWord_3701720) baseStart_3701720 baseEnd_3701720 := by
    simpa [prefixWord, tailWord_3701720, baseEnd_3701720] using wordTrace_append hprefix tailTrace_3701720
  have hstable : (prefixWord ++ tailWord_3701720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701720).length < 2 ^ (prefixWord ++ tailWord_3701720).sum := by decide
  have hdescent : baseEnd_3701720 < baseStart_3701720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701767 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3701767 : Nat := 118140960795 + 3701767 * 2 ^ 59
def prefixEnd_3701767 : Nat := 4983230072969 + 3 ^ 40 * 3701767 * 2
def baseEnd_3701767 : Nat := 1267190494634749035525593

theorem tailTrace_3701767 : CollatzResearch.WordTrace tailWord_3701767 prefixEnd_3701767 1267190494634749035525593 := by
  unfold tailWord_3701767
  simp only [CollatzResearch.WordTrace]
  refine ⟨135014534380137845315783555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90009689586758563543855703 135014534380137845315783555)
  ·
    refine ⟨202521801570206767973675333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135014534380137845315783555 202521801570206767973675333)
    ·
      refine ⟨37972837794413768995064125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202521801570206767973675333 37972837794413768995064125)
      ·
        refine ⟨14239814172905163373149047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37972837794413768995064125 14239814172905163373149047)
        ·
          refine ⟨21359721259357745059723571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14239814172905163373149047 21359721259357745059723571)
          ·
            refine ⟨32039581889036617589585357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21359721259357745059723571 32039581889036617589585357)
            ·
              refine ⟨12014843208388731596094509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32039581889036617589585357 12014843208388731596094509)
              ·
                refine ⟨4505566203145774348535441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12014843208388731596094509 4505566203145774348535441)
                ·
                  refine ⟨3379174652359330761401581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4505566203145774348535441 3379174652359330761401581)
                  ·
                    refine ⟨1267190494634749035525593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3379174652359330761401581 1267190494634749035525593)
                    ·
                      rfl

theorem cell22_3701767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3701767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701767 prefixEnd_3701767 := by exact prefixLift 3701767
  have htrace : WordTrace (prefixWord ++ tailWord_3701767) baseStart_3701767 baseEnd_3701767 := by
    simpa [prefixWord, tailWord_3701767, baseEnd_3701767] using wordTrace_append hprefix tailTrace_3701767
  have hstable : (prefixWord ++ tailWord_3701767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701767).length < 2 ^ (prefixWord ++ tailWord_3701767).sum := by decide
  have hdescent : baseEnd_3701767 < baseStart_3701767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701889 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3701889 : Nat := 118140960795 + 3701889 * 2 ^ 59
def prefixEnd_3701889 : Nat := 4983230072969 + 3 ^ 40 * 3701889 * 2
def baseEnd_3701889 : Nat := 1267232257727981383975219

theorem tailTrace_3701889 : CollatzResearch.WordTrace tailWord_3701889 prefixEnd_3701889 1267232257727981383975219 := by
  unfold tailWord_3701889
  simp only [CollatzResearch.WordTrace]
  refine ⟨135018984085695860151724721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90012656057130573434483147 135018984085695860151724721)
  ·
    refine ⟨101264238064271895113793541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135018984085695860151724721 101264238064271895113793541)
    ·
      refine ⟨18987044637050980333836289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101264238064271895113793541 18987044637050980333836289)
      ·
        refine ⟨14240283477788235250377217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18987044637050980333836289 14240283477788235250377217)
        ·
          refine ⟨10680212608341176437782913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14240283477788235250377217 10680212608341176437782913)
          ·
            refine ⟨8010159456255882328337185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10680212608341176437782913 8010159456255882328337185)
            ·
              refine ⟨6007619592191911746252889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8010159456255882328337185 6007619592191911746252889)
              ·
                refine ⟨4505714694143933809689667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6007619592191911746252889 4505714694143933809689667)
                ·
                  refine ⟨6758572041215900714534501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505714694143933809689667 6758572041215900714534501)
                  ·
                    refine ⟨1267232257727981383975219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758572041215900714534501 1267232257727981383975219)
                    ·
                      rfl

theorem cell22_3701889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3701889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701889 prefixEnd_3701889 := by exact prefixLift 3701889
  have htrace : WordTrace (prefixWord ++ tailWord_3701889) baseStart_3701889 baseEnd_3701889 := by
    simpa [prefixWord, tailWord_3701889, baseEnd_3701889] using wordTrace_append hprefix tailTrace_3701889
  have hstable : (prefixWord ++ tailWord_3701889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701889).length < 2 ^ (prefixWord ++ tailWord_3701889).sum := by decide
  have hdescent : baseEnd_3701889 < baseStart_3701889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701900 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_3701900 : Nat := 118140960795 + 3701900 * 2 ^ 59
def prefixEnd_3701900 : Nat := 4983230072969 + 3 ^ 40 * 3701900 * 2
def baseEnd_3701900 : Nat := 1267236023252781021950185

theorem tailTrace_3701900 : CollatzResearch.WordTrace tailWord_3701900 prefixEnd_3701900 1267236023252781021950185 := by
  unfold tailWord_3701900
  simp only [CollatzResearch.WordTrace]
  refine ⟨67509692644328004515187577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90012923525770672686916769 67509692644328004515187577)
  ·
    refine ⟨50632269483246003386390683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67509692644328004515187577 50632269483246003386390683)
    ·
      refine ⟨75948404224869005079586025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50632269483246003386390683 75948404224869005079586025)
      ·
        refine ⟨56961303168651753809689519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75948404224869005079586025 56961303168651753809689519)
        ·
          refine ⟨85441954752977630714534279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56961303168651753809689519 85441954752977630714534279)
          ·
            refine ⟨128162932129466446071801419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85441954752977630714534279 128162932129466446071801419)
            ·
              refine ⟨192244398194199669107702129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128162932129466446071801419 192244398194199669107702129)
              ·
                refine ⟨144183298645649751830776597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192244398194199669107702129 144183298645649751830776597)
                ·
                  refine ⟨6758592124014832117067653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144183298645649751830776597 6758592124014832117067653)
                  ·
                    refine ⟨1267236023252781021950185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758592124014832117067653 1267236023252781021950185)
                    ·
                      rfl

theorem cell22_3701900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_3701900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701900 prefixEnd_3701900 := by exact prefixLift 3701900
  have htrace : WordTrace (prefixWord ++ tailWord_3701900) baseStart_3701900 baseEnd_3701900 := by
    simpa [prefixWord, tailWord_3701900, baseEnd_3701900] using wordTrace_append hprefix tailTrace_3701900
  have hstable : (prefixWord ++ tailWord_3701900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701900).length < 2 ^ (prefixWord ++ tailWord_3701900).sum := by decide
  have hdescent : baseEnd_3701900 < baseStart_3701900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701917 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3701917 : Nat := 118140960795 + 3701917 * 2 ^ 59
def prefixEnd_3701917 : Nat := 4983230072969 + 3 ^ 40 * 3701917 * 2
def baseEnd_3701917 : Nat := 1267241842700198644275133

theorem tailTrace_3701917 : CollatzResearch.WordTrace tailWord_3701917 prefixEnd_3701917 1267241842700198644275133 := by
  unfold tailWord_3701917
  simp only [CollatzResearch.WordTrace]
  refine ⟨135020005329594420933744005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90013336886396280622496003 135020005329594420933744005)
  ·
    refine ⟨25316250999298953925077001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135020005329594420933744005 25316250999298953925077001)
    ·
      refine ⟨18987188249474215443807751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25316250999298953925077001 18987188249474215443807751)
      ·
        refine ⟨28480782374211323165711627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18987188249474215443807751 28480782374211323165711627)
        ·
          refine ⟨42721173561316984748567441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28480782374211323165711627 42721173561316984748567441)
          ·
            refine ⟨32040880170987738561425581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42721173561316984748567441 32040880170987738561425581)
            ·
              refine ⟨12015330064120401960534593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32040880170987738561425581 12015330064120401960534593)
              ·
                refine ⟨9011497548090301470400945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12015330064120401960534593 9011497548090301470400945)
                ·
                  refine ⟨6758623161067726102800709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9011497548090301470400945 6758623161067726102800709)
                  ·
                    refine ⟨1267241842700198644275133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758623161067726102800709 1267241842700198644275133)
                    ·
                      rfl

theorem cell22_3701917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3701917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701917 prefixEnd_3701917 := by exact prefixLift 3701917
  have htrace : WordTrace (prefixWord ++ tailWord_3701917) baseStart_3701917 baseEnd_3701917 := by
    simpa [prefixWord, tailWord_3701917, baseEnd_3701917] using wordTrace_append hprefix tailTrace_3701917
  have hstable : (prefixWord ++ tailWord_3701917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701917).length < 2 ^ (prefixWord ++ tailWord_3701917).sum := by decide
  have hdescent : baseEnd_3701917 < baseStart_3701917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701960 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_3701960 : Nat := 118140960795 + 3701960 * 2 ^ 59
def prefixEnd_3701960 : Nat := 4983230072969 + 3 ^ 40 * 3701960 * 2
def baseEnd_3701960 : Nat := 422418854159653621816667

theorem tailTrace_3701960 : CollatzResearch.WordTrace tailWord_3701960 prefixEnd_3701960 422418854159653621816667 := by
  unfold tailWord_3701960
  simp only [CollatzResearch.WordTrace]
  refine ⟨67510786834219319638779667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90014382445625759518372889 67510786834219319638779667)
  ·
    refine ⟨101266180251328979458169501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67510786834219319638779667 101266180251328979458169501)
    ·
      refine ⟨37974817594248367296813563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101266180251328979458169501 37974817594248367296813563)
      ·
        refine ⟨56962226391372550945220345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37974817594248367296813563 56962226391372550945220345)
        ·
          refine ⟨42721669793529413208915259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56962226391372550945220345 42721669793529413208915259)
          ·
            refine ⟨64082504690294119813372889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42721669793529413208915259 64082504690294119813372889)
            ·
              refine ⟨48061878517720589860029667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64082504690294119813372889 48061878517720589860029667)
              ·
                refine ⟨72092817776580884790044501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48061878517720589860029667 72092817776580884790044501)
                ·
                  refine ⟨422418854159653621816667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72092817776580884790044501 422418854159653621816667)
                  ·
                    rfl

theorem cell22_3701960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_3701960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701960 prefixEnd_3701960 := by exact prefixLift 3701960
  have htrace : WordTrace (prefixWord ++ tailWord_3701960) baseStart_3701960 baseEnd_3701960 := by
    simpa [prefixWord, tailWord_3701960, baseEnd_3701960] using wordTrace_append hprefix tailTrace_3701960
  have hstable : (prefixWord ++ tailWord_3701960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701960).length < 2 ^ (prefixWord ++ tailWord_3701960).sum := by decide
  have hdescent : baseEnd_3701960 < baseStart_3701960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3701992 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3701992 : Nat := 118140960795 + 3701992 * 2 ^ 59
def prefixEnd_3701992 : Nat := 4983230072969 + 3 ^ 40 * 3701992 * 2
def baseEnd_3701992 : Nat := 1267267516732923448649903

theorem tailTrace_3701992 : CollatzResearch.WordTrace tailWord_3701992 prefixEnd_3701992 1267267516732923448649903 := by
  unfold tailWord_3701992
  simp only [CollatzResearch.WordTrace]
  refine ⟨67511370402161354371362115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90015160536215139161816153 67511370402161354371362115)
  ·
    refine ⟨101267055603242031557043173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67511370402161354371362115 101267055603242031557043173)
    ·
      refine ⟨18987572925607880916945595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101267055603242031557043173 18987572925607880916945595)
      ·
        refine ⟨28481359388411821375418393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18987572925607880916945595 28481359388411821375418393)
        ·
          refine ⟨21361019541308866031563795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28481359388411821375418393 21361019541308866031563795)
          ·
            refine ⟨32041529311963299047345693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21361019541308866031563795 32041529311963299047345693)
            ·
              refine ⟨12015573491986237142754635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32041529311963299047345693 12015573491986237142754635)
              ·
                refine ⟨18023360237979355714131953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12015573491986237142754635 18023360237979355714131953)
                ·
                  refine ⟨13517520178484516785598965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18023360237979355714131953 13517520178484516785598965)
                  ·
                    refine ⟨1267267516732923448649903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13517520178484516785598965 1267267516732923448649903)
                    ·
                      rfl

theorem cell22_3701992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3701992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3701992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3701992 prefixEnd_3701992 := by exact prefixLift 3701992
  have htrace : WordTrace (prefixWord ++ tailWord_3701992) baseStart_3701992 baseEnd_3701992 := by
    simpa [prefixWord, tailWord_3701992, baseEnd_3701992] using wordTrace_append hprefix tailTrace_3701992
  have hstable : (prefixWord ++ tailWord_3701992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3701992).length < 2 ^ (prefixWord ++ tailWord_3701992).sum := by decide
  have hdescent : baseEnd_3701992 < baseStart_3701992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3701992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702039 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 4]
def baseStart_3702039 : Nat := 118140960795 + 3702039 * 2 ^ 59
def prefixEnd_3702039 : Nat := 4983230072969 + 3 ^ 40 * 3702039 * 2
def baseEnd_3702039 : Nat := 422427868597810330908253

theorem tailTrace_3702039 : CollatzResearch.WordTrace tailWord_3702039 prefixEnd_3702039 422427868597810330908253 := by
  unfold tailWord_3702039
  simp only [CollatzResearch.WordTrace]
  refine ⟨135024455035152435769685171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90016303356768290513123447 135024455035152435769685171)
  ·
    refine ⟨202536682552728653654527757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135024455035152435769685171 202536682552728653654527757)
    ·
      refine ⟨75951255957273245120447909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202536682552728653654527757 75951255957273245120447909)
      ·
        refine ⟨14240860491988733460083983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75951255957273245120447909 14240860491988733460083983)
        ·
          refine ⟨21361290737983100190125975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240860491988733460083983 21361290737983100190125975)
          ·
            refine ⟨32041936106974650285188963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21361290737983100190125975 32041936106974650285188963)
            ·
              refine ⟨48062904160461975427783445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32041936106974650285188963 48062904160461975427783445)
              ·
                refine ⟨2252948632521655098177349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48062904160461975427783445 2252948632521655098177349)
                ·
                  refine ⟨422427868597810330908253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252948632521655098177349 422427868597810330908253)
                  ·
                    rfl

theorem cell22_3702039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 4].length) (baseStart_3702039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702039 prefixEnd_3702039 := by exact prefixLift 3702039
  have htrace : WordTrace (prefixWord ++ tailWord_3702039) baseStart_3702039 baseEnd_3702039 := by
    simpa [prefixWord, tailWord_3702039, baseEnd_3702039] using wordTrace_append hprefix tailTrace_3702039
  have hstable : (prefixWord ++ tailWord_3702039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702039).length < 2 ^ (prefixWord ++ tailWord_3702039).sum := by decide
  have hdescent : baseEnd_3702039 < baseStart_3702039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702052 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3702052 : Nat := 118140960795 + 3702052 * 2 ^ 59
def prefixEnd_3702052 : Nat := 4983230072969 + 3 ^ 40 * 3702052 * 2
def baseEnd_3702052 : Nat := 1267288055959103292149719

theorem tailTrace_3702052 : CollatzResearch.WordTrace tailWord_3702052 prefixEnd_3702052 1267288055959103292149719 := by
  unfold tailWord_3702052
  simp only [CollatzResearch.WordTrace]
  refine ⟨67512464592052669494954205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90016619456070225993272273 67512464592052669494954205)
  ·
    refine ⟨25317174222019751060607827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67512464592052669494954205 25317174222019751060607827)
    ·
      refine ⟨37975761333029626590911741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25317174222019751060607827 37975761333029626590911741)
      ·
        refine ⟨14240910499886109971591903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37975761333029626590911741 14240910499886109971591903)
        ·
          refine ⟨21361365749829164957387855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240910499886109971591903 21361365749829164957387855)
          ·
            refine ⟨32042048624743747436081783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21361365749829164957387855 32042048624743747436081783)
            ·
              refine ⟨48063072937115621154122675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32042048624743747436081783 48063072937115621154122675)
              ·
                refine ⟨72094609405673431731184013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48063072937115621154122675 72094609405673431731184013)
                ·
                  refine ⟨27035478527127536899194005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72094609405673431731184013 27035478527127536899194005)
                  ·
                    refine ⟨1267288055959103292149719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27035478527127536899194005 1267288055959103292149719)
                    ·
                      rfl

theorem cell22_3702052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3702052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702052 prefixEnd_3702052 := by exact prefixLift 3702052
  have htrace : WordTrace (prefixWord ++ tailWord_3702052) baseStart_3702052 baseEnd_3702052 := by
    simpa [prefixWord, tailWord_3702052, baseEnd_3702052] using wordTrace_append hprefix tailTrace_3702052
  have hstable : (prefixWord ++ tailWord_3702052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702052).length < 2 ^ (prefixWord ++ tailWord_3702052).sum := by decide
  have hdescent : baseEnd_3702052 < baseStart_3702052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702067 : List Nat := [1, 1, 1, 2, 5, 3, 1, 8]
def baseStart_3702067 : Nat := 118140960795 + 3702067 * 2 ^ 59
def prefixEnd_3702067 : Nat := 4983230072969 + 3 ^ 40 * 3702067 * 2
def baseEnd_3702067 : Nat := 140810354529516472558297

theorem tailTrace_3702067 : CollatzResearch.WordTrace tailWord_3702067 prefixEnd_3702067 140810354529516472558297 := by
  unfold tailWord_3702067
  simp only [CollatzResearch.WordTrace]
  refine ⟨135025476279050996551704455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90016984186033997701136303 135025476279050996551704455)
  ·
    refine ⟨202538214418576494827556683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135025476279050996551704455 202538214418576494827556683)
    ·
      refine ⟨303807321627864742241335025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202538214418576494827556683 303807321627864742241335025)
      ·
        refine ⟨227855491220898556681001269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303807321627864742241335025 227855491220898556681001269)
        ·
          refine ⟨21361452301959239688843869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227855491220898556681001269 21361452301959239688843869)
          ·
            refine ⟨8010544613234714883316451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21361452301959239688843869 8010544613234714883316451)
            ·
              refine ⟨12015816919852072324974677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8010544613234714883316451 12015816919852072324974677)
              ·
                refine ⟨140810354529516472558297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12015816919852072324974677 140810354529516472558297)
                ·
                  rfl

theorem cell22_3702067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 8].length) (baseStart_3702067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702067 prefixEnd_3702067 := by exact prefixLift 3702067
  have htrace : WordTrace (prefixWord ++ tailWord_3702067) baseStart_3702067 baseEnd_3702067 := by
    simpa [prefixWord, tailWord_3702067, baseEnd_3702067] using wordTrace_append hprefix tailTrace_3702067
  have hstable : (prefixWord ++ tailWord_3702067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702067).length < 2 ^ (prefixWord ++ tailWord_3702067).sum := by decide
  have hdescent : baseEnd_3702067 < baseStart_3702067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702073 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 4]
def baseStart_3702073 : Nat := 118140960795 + 3702073 * 2 ^ 59
def prefixEnd_3702073 : Nat := 4983230072969 + 3 ^ 40 * 3702073 * 2
def baseEnd_3702073 : Nat := 422431748229422079124885

theorem tailTrace_3702073 : CollatzResearch.WordTrace tailWord_3702073 prefixEnd_3702073 422431748229422079124885 := by
  unfold tailWord_3702073
  simp only [CollatzResearch.WordTrace]
  refine ⟨135025695117029259576422873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90017130078019506384281915 135025695117029259576422873)
  ·
    refine ⟨101269271337771944682317155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135025695117029259576422873 101269271337771944682317155)
    ·
      refine ⟨151903907006657917023475733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101269271337771944682317155 151903907006657917023475733)
      ·
        refine ⟨7120495640937089860475425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151903907006657917023475733 7120495640937089860475425)
        ·
          refine ⟨5340371730702817395356569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7120495640937089860475425 5340371730702817395356569)
          ·
            refine ⟨4005278798027113046517427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340371730702817395356569 4005278798027113046517427)
            ·
              refine ⟨6007918197040669569776141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005278798027113046517427 6007918197040669569776141)
              ·
                refine ⟨2252969323890251088666053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6007918197040669569776141 2252969323890251088666053)
                ·
                  refine ⟨422431748229422079124885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252969323890251088666053 422431748229422079124885)
                  ·
                    rfl

theorem cell22_3702073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_3702073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702073 prefixEnd_3702073 := by exact prefixLift 3702073
  have htrace : WordTrace (prefixWord ++ tailWord_3702073) baseStart_3702073 baseEnd_3702073 := by
    simpa [prefixWord, tailWord_3702073, baseEnd_3702073] using wordTrace_append hprefix tailTrace_3702073
  have hstable : (prefixWord ++ tailWord_3702073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702073).length < 2 ^ (prefixWord ++ tailWord_3702073).sum := by decide
  have hdescent : baseEnd_3702073 < baseStart_3702073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702084 : List Nat := [2, 3, 4, 1, 1, 1, 10]
def baseStart_3702084 : Nat := 118140960795 + 3702084 * 2 ^ 59
def prefixEnd_3702084 : Nat := 4983230072969 + 3 ^ 40 * 3702084 * 2
def baseEnd_3702084 : Nat := 46937000378261699087023

theorem tailTrace_3702084 : CollatzResearch.WordTrace tailWord_3702084 prefixEnd_3702084 46937000378261699087023 := by
  unfold tailWord_3702084
  simp only [CollatzResearch.WordTrace]
  refine ⟨67513048159994704227536653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90017397546659605636715537 67513048159994704227536653)
  ·
    refine ⟨25317393059998014085326245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67513048159994704227536653 25317393059998014085326245)
    ·
      refine ⟨4747011198749627640998671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25317393059998014085326245 4747011198749627640998671)
      ·
        refine ⟨7120516798124441461498007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747011198749627640998671 7120516798124441461498007)
        ·
          refine ⟨10680775197186662192247011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120516798124441461498007 10680775197186662192247011)
          ·
            refine ⟨16021162795779993288370517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680775197186662192247011 16021162795779993288370517)
            ·
              refine ⟨46937000378261699087023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16021162795779993288370517 46937000378261699087023)
              ·
                rfl

theorem cell22_3702084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 10].length) (baseStart_3702084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702084 prefixEnd_3702084 := by exact prefixLift 3702084
  have htrace : WordTrace (prefixWord ++ tailWord_3702084) baseStart_3702084 baseEnd_3702084 := by
    simpa [prefixWord, tailWord_3702084, baseEnd_3702084] using wordTrace_append hprefix tailTrace_3702084
  have hstable : (prefixWord ++ tailWord_3702084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702084).length < 2 ^ (prefixWord ++ tailWord_3702084).sum := by decide
  have hdescent : baseEnd_3702084 < baseStart_3702084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702097 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3702097 : Nat := 118140960795 + 3702097 * 2 ^ 59
def prefixEnd_3702097 : Nat := 4983230072969 + 3 ^ 40 * 3702097 * 2
def baseEnd_3702097 : Nat := 1267303460378738174774581

theorem tailTrace_3702097 : CollatzResearch.WordTrace tailWord_3702097 prefixEnd_3702097 1267303460378738174774581 := by
  unfold tailWord_3702097
  simp only [CollatzResearch.WordTrace]
  refine ⟨135026570468942311675296545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90017713645961541116864363 135026570468942311675296545)
  ·
    refine ⟨101269927851706733756472409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135026570468942311675296545 101269927851706733756472409)
    ·
      refine ⟨75952445888780050317354307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101269927851706733756472409 75952445888780050317354307)
      ·
        refine ⟨113928668833170075476031461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75952445888780050317354307 113928668833170075476031461)
        ·
          refine ⟨21361625406219389151755899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113928668833170075476031461 21361625406219389151755899)
          ·
            refine ⟨32042438109329083727633849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21361625406219389151755899 32042438109329083727633849)
            ·
              refine ⟨24031828581996812795725387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32042438109329083727633849 24031828581996812795725387)
              ·
                refine ⟨36047742872995219193588081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24031828581996812795725387 36047742872995219193588081)
                ·
                  refine ⟨27035807154746414395191061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36047742872995219193588081 27035807154746414395191061)
                  ·
                    refine ⟨1267303460378738174774581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27035807154746414395191061 1267303460378738174774581)
                    ·
                      rfl

theorem cell22_3702097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3702097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702097 prefixEnd_3702097 := by exact prefixLift 3702097
  have htrace : WordTrace (prefixWord ++ tailWord_3702097) baseStart_3702097 baseEnd_3702097 := by
    simpa [prefixWord, tailWord_3702097, baseEnd_3702097] using wordTrace_append hprefix tailTrace_3702097
  have hstable : (prefixWord ++ tailWord_3702097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702097).length < 2 ^ (prefixWord ++ tailWord_3702097).sum := by decide
  have hdescent : baseEnd_3702097 < baseStart_3702097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702253 : List Nat := [1, 5, 1, 3, 3, 1, 8]
def baseStart_3702253 : Nat := 118140960795 + 3702253 * 2 ^ 59
def prefixEnd_3702253 : Nat := 4983230072969 + 3 ^ 40 * 3702253 * 2
def baseEnd_3702253 : Nat := 46939143050622435847189

theorem tailTrace_3702253 : CollatzResearch.WordTrace tailWord_3702253 prefixEnd_3702253 46939143050622435847189 := by
  unfold tailWord_3702253
  simp only [CollatzResearch.WordTrace]
  refine ⟨135032260256377150317975413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90021506837584766878650275 135032260256377150317975413)
  ·
    refine ⟨12659274399035357842310195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135032260256377150317975413 12659274399035357842310195)
    ·
      refine ⟨18988911598553036763465293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659274399035357842310195 18988911598553036763465293)
      ·
        refine ⟨7120841849457388786299485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18988911598553036763465293 7120841849457388786299485)
        ·
          refine ⟨2670315693546520794862307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7120841849457388786299485 2670315693546520794862307)
          ·
            refine ⟨4005473540319781192293461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670315693546520794862307 4005473540319781192293461)
            ·
              refine ⟨46939143050622435847189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4005473540319781192293461 46939143050622435847189)
              ·
                rfl

theorem cell22_3702253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 8].length) (baseStart_3702253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702253 prefixEnd_3702253 := by exact prefixLift 3702253
  have htrace : WordTrace (prefixWord ++ tailWord_3702253) baseStart_3702253 baseEnd_3702253 := by
    simpa [prefixWord, tailWord_3702253, baseEnd_3702253] using wordTrace_append hprefix tailTrace_3702253
  have hstable : (prefixWord ++ tailWord_3702253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702253).length < 2 ^ (prefixWord ++ tailWord_3702253).sum := by decide
  have hdescent : baseEnd_3702253 < baseStart_3702253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702264 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_3702264 : Nat := 118140960795 + 3702264 * 2 ^ 59
def prefixEnd_3702264 : Nat := 4983230072969 + 3 ^ 40 * 3702264 * 2
def baseEnd_3702264 : Nat := 422453542630535135283023

theorem tailTrace_3702264 : CollatzResearch.WordTrace tailWord_3702264 prefixEnd_3702264 422453542630535135283023 := by
  unfold tailWord_3702264
  simp only [CollatzResearch.WordTrace]
  refine ⟨67516330729668649598312923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90021774306224866131083897 67516330729668649598312923)
  ·
    refine ⟨101274496094502974397469385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67516330729668649598312923 101274496094502974397469385)
    ·
      refine ⟨75955872070877230798102039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101274496094502974397469385 75955872070877230798102039)
      ·
        refine ⟨113933808106315846197153059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75955872070877230798102039 113933808106315846197153059)
        ·
          refine ⟨170900712159473769295729589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113933808106315846197153059 170900712159473769295729589)
          ·
            refine ⟨16021941764950665871474649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170900712159473769295729589 16021941764950665871474649)
            ·
              refine ⟨12016456323712999403605987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16021941764950665871474649 12016456323712999403605987)
              ·
                refine ⟨18024684485569499105408981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016456323712999403605987 18024684485569499105408981)
                ·
                  refine ⟨422453542630535135283023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18024684485569499105408981 422453542630535135283023)
                  ·
                    rfl

theorem cell22_3702264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_3702264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702264 prefixEnd_3702264 := by exact prefixLift 3702264
  have htrace : WordTrace (prefixWord ++ tailWord_3702264) baseStart_3702264 baseEnd_3702264 := by
    simpa [prefixWord, tailWord_3702264, baseEnd_3702264] using wordTrace_append hprefix tailTrace_3702264
  have hstable : (prefixWord ++ tailWord_3702264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702264).length < 2 ^ (prefixWord ++ tailWord_3702264).sum := by decide
  have hdescent : baseEnd_3702264 < baseStart_3702264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702268 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_3702268 : Nat := 118140960795 + 3702268 * 2 ^ 59
def prefixEnd_3702268 : Nat := 4983230072969 + 3 ^ 40 * 3702268 * 2
def baseEnd_3702268 : Nat := 1267361997173350728749057

theorem tailTrace_3702268 : CollatzResearch.WordTrace tailWord_3702268 prefixEnd_3702268 1267361997173350728749057 := by
  unfold tailWord_3702268
  simp only [CollatzResearch.WordTrace]
  refine ⟨67516403675661403939885729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90021871567548538586514305 67516403675661403939885729)
  ·
    refine ⟨50637302756746052954914297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67516403675661403939885729 50637302756746052954914297)
    ·
      refine ⟨37977977067559539716185723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50637302756746052954914297 37977977067559539716185723)
      ·
        refine ⟨56966965601339309574278585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37977977067559539716185723 56966965601339309574278585)
        ·
          refine ⟨42725224201004482180708939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56966965601339309574278585 42725224201004482180708939)
          ·
            refine ⟨64087836301506723271063409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42725224201004482180708939 64087836301506723271063409)
            ·
              refine ⟨48065877226130042453297557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64087836301506723271063409 48065877226130042453297557)
              ·
                refine ⟨2253087994974845739998323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48065877226130042453297557 2253087994974845739998323)
                ·
                  refine ⟨3379631992462268609997485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253087994974845739998323 3379631992462268609997485)
                  ·
                    refine ⟨1267361997173350728749057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3379631992462268609997485 1267361997173350728749057)
                    ·
                      rfl

theorem cell22_3702268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_3702268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702268 prefixEnd_3702268 := by exact prefixLift 3702268
  have htrace : WordTrace (prefixWord ++ tailWord_3702268) baseStart_3702268 baseEnd_3702268 := by
    simpa [prefixWord, tailWord_3702268, baseEnd_3702268] using wordTrace_append hprefix tailTrace_3702268
  have hstable : (prefixWord ++ tailWord_3702268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702268).length < 2 ^ (prefixWord ++ tailWord_3702268).sum := by decide
  have hdescent : baseEnd_3702268 < baseStart_3702268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702341 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_3702341 : Nat := 118140960795 + 3702341 * 2 ^ 59
def prefixEnd_3702341 : Nat := 4983230072969 + 3 ^ 40 * 3702341 * 2
def baseEnd_3702341 : Nat := 1267386986565202871673833

theorem tailTrace_3702341 : CollatzResearch.WordTrace tailWord_3702341 prefixEnd_3702341 1267386986565202871673833 := by
  unfold tailWord_3702341
  simp only [CollatzResearch.WordTrace]
  refine ⟨135035469880058341347178877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90023646586705560898119251 135035469880058341347178877)
  ·
    refine ⟨50638301205021878005192079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135035469880058341347178877 50638301205021878005192079)
    ·
      refine ⟨75957451807532817007788119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50638301205021878005192079 75957451807532817007788119)
      ·
        refine ⟨113936177711299225511682179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75957451807532817007788119 113936177711299225511682179)
        ·
          refine ⟨170904266566948838267523269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113936177711299225511682179 170904266566948838267523269)
          ·
            refine ⟨32044549981302907175160613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170904266566948838267523269 32044549981302907175160613)
            ·
              refine ⟨6008353121494295095342615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32044549981302907175160613 6008353121494295095342615)
              ·
                refine ⟨9012529682241442643013923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6008353121494295095342615 9012529682241442643013923)
                ·
                  refine ⟨13518794523362163964520885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9012529682241442643013923 13518794523362163964520885)
                  ·
                    refine ⟨1267386986565202871673833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13518794523362163964520885 1267386986565202871673833)
                    ·
                      rfl

theorem cell22_3702341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_3702341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702341 prefixEnd_3702341 := by exact prefixLift 3702341
  have htrace : WordTrace (prefixWord ++ tailWord_3702341) baseStart_3702341 baseEnd_3702341 := by
    simpa [prefixWord, tailWord_3702341, baseEnd_3702341] using wordTrace_append hprefix tailTrace_3702341
  have hstable : (prefixWord ++ tailWord_3702341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702341).length < 2 ^ (prefixWord ++ tailWord_3702341).sum := by decide
  have hdescent : baseEnd_3702341 < baseStart_3702341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702356 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3702356 : Nat := 118140960795 + 3702356 * 2 ^ 59
def prefixEnd_3702356 : Nat := 4983230072969 + 3 ^ 40 * 3702356 * 2
def baseEnd_3702356 : Nat := 1267392121371747832548787

theorem tailTrace_3702356 : CollatzResearch.WordTrace tailWord_3702356 prefixEnd_3702356 1267392121371747832548787 := by
  unfold tailWord_3702356
  simp only [CollatzResearch.WordTrace]
  refine ⟨67518008487501999454487461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90024011316669332605983281 67518008487501999454487461)
  ·
    refine ⟨12659626591406624897716399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67518008487501999454487461 12659626591406624897716399)
    ·
      refine ⟨18989439887109937346574599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659626591406624897716399 18989439887109937346574599)
      ·
        refine ⟨28484159830664906019861899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18989439887109937346574599 28484159830664906019861899)
        ·
          refine ⟨42726239745997359029792849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28484159830664906019861899 42726239745997359029792849)
          ·
            refine ⟨32044679809498019272344637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42726239745997359029792849 32044679809498019272344637)
            ·
              refine ⟨12016754928561757227129239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32044679809498019272344637 12016754928561757227129239)
              ·
                refine ⟨18025132392842635840693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016754928561757227129239 18025132392842635840693859)
                ·
                  refine ⟨27037698589263953761040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18025132392842635840693859 27037698589263953761040789)
                  ·
                    refine ⟨1267392121371747832548787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27037698589263953761040789 1267392121371747832548787)
                    ·
                      rfl

theorem cell22_3702356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3702356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702356 prefixEnd_3702356 := by exact prefixLift 3702356
  have htrace : WordTrace (prefixWord ++ tailWord_3702356) baseStart_3702356 baseEnd_3702356 := by
    simpa [prefixWord, tailWord_3702356, baseEnd_3702356] using wordTrace_append hprefix tailTrace_3702356
  have hstable : (prefixWord ++ tailWord_3702356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702356).length < 2 ^ (prefixWord ++ tailWord_3702356).sum := by decide
  have hdescent : baseEnd_3702356 < baseStart_3702356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702461 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 8]
def baseStart_3702461 : Nat := 118140960795 + 3702461 * 2 ^ 59
def prefixEnd_3702461 : Nat := 4983230072969 + 3 ^ 40 * 3702461 * 2
def baseEnd_3702461 : Nat := 422476021672520852891155

theorem tailTrace_3702461 : CollatzResearch.WordTrace tailWord_3702461 prefixEnd_3702461 422476021672520852891155 := by
  unfold tailWord_3702461
  simp only [CollatzResearch.WordTrace]
  refine ⟨135039846639623601841547237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90026564426415734561031491 135039846639623601841547237)
  ·
    refine ⟨25319971244929425345290107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135039846639623601841547237 25319971244929425345290107)
    ·
      refine ⟨37979956867394138017935161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25319971244929425345290107 37979956867394138017935161)
      ·
        refine ⟨28484967650545603513451371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37979956867394138017935161 28484967650545603513451371)
        ·
          refine ⟨42727451475818405270177057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28484967650545603513451371 42727451475818405270177057)
          ·
            refine ⟨32045588606863803952632793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42727451475818405270177057 32045588606863803952632793)
            ·
              refine ⟨24034191455147852964474595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32045588606863803952632793 24034191455147852964474595)
              ·
                refine ⟨36051287182721779446711893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24034191455147852964474595 36051287182721779446711893)
                ·
                  refine ⟨422476021672520852891155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36051287182721779446711893 422476021672520852891155)
                  ·
                    rfl

theorem cell22_3702461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_3702461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702461 prefixEnd_3702461 := by exact prefixLift 3702461
  have htrace : WordTrace (prefixWord ++ tailWord_3702461) baseStart_3702461 baseEnd_3702461 := by
    simpa [prefixWord, tailWord_3702461, baseEnd_3702461] using wordTrace_append hprefix tailTrace_3702461
  have hstable : (prefixWord ++ tailWord_3702461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702461).length < 2 ^ (prefixWord ++ tailWord_3702461).sum := by decide
  have hdescent : baseEnd_3702461 < baseStart_3702461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702510 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3702510 : Nat := 118140960795 + 3702510 * 2 ^ 59
def prefixEnd_3702510 : Nat := 4983230072969 + 3 ^ 40 * 3702510 * 2
def baseEnd_3702510 : Nat := 1267444838718942764198315

theorem tailTrace_3702510 : CollatzResearch.WordTrace tailWord_3702510 prefixEnd_3702510 1267444838718942764198315 := by
  unfold tailWord_3702510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880204227055760401260123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90027755877630722140053989 16880204227055760401260123)
  ·
    refine ⟨25320306340583640601890185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16880204227055760401260123 25320306340583640601890185)
    ·
      refine ⟨18990229755437730451417639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25320306340583640601890185 18990229755437730451417639)
      ·
        refine ⟨28485344633156595677126459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18990229755437730451417639 28485344633156595677126459)
        ·
          refine ⟨42728016949734893515689689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28485344633156595677126459 42728016949734893515689689)
          ·
            refine ⟨32046012712301170136767267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42728016949734893515689689 32046012712301170136767267)
            ·
              refine ⟨48069019068451755205150901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32046012712301170136767267 48069019068451755205150901)
              ·
                refine ⟨4506470537667352050482897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48069019068451755205150901 4506470537667352050482897)
                ·
                  refine ⟨3379852903250514037862173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4506470537667352050482897 3379852903250514037862173)
                  ·
                    refine ⟨1267444838718942764198315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3379852903250514037862173 1267444838718942764198315)
                    ·
                      rfl

theorem cell22_3702510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3702510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702510 prefixEnd_3702510 := by exact prefixLift 3702510
  have htrace : WordTrace (prefixWord ++ tailWord_3702510) baseStart_3702510 baseEnd_3702510 := by
    simpa [prefixWord, tailWord_3702510, baseEnd_3702510] using wordTrace_append hprefix tailTrace_3702510
  have hstable : (prefixWord ++ tailWord_3702510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702510).length < 2 ^ (prefixWord ++ tailWord_3702510).sum := by decide
  have hdescent : baseEnd_3702510 < baseStart_3702510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702574 : List Nat := [4, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3702574 : Nat := 118140960795 + 3702574 * 2 ^ 59
def prefixEnd_3702574 : Nat := 4983230072969 + 3 ^ 40 * 3702574 * 2
def baseEnd_3702574 : Nat := 140829638580763103399791

theorem tailTrace_3702574 : CollatzResearch.WordTrace tailWord_3702574 prefixEnd_3702574 140829638580763103399791 := by
  unfold tailWord_3702574
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880496011026777767551347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90029312058809481426940517 16880496011026777767551347)
  ·
    refine ⟨25320744016540166651327021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16880496011026777767551347 25320744016540166651327021)
    ·
      refine ⟨9495279006202562494247633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25320744016540166651327021 9495279006202562494247633)
      ·
        refine ⟨7121459254651921870685725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9495279006202562494247633 7121459254651921870685725)
        ·
          refine ⟨2670547220494470701507147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7121459254651921870685725 2670547220494470701507147)
          ·
            refine ⟨4005820830741706052260721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670547220494470701507147 4005820830741706052260721)
            ·
              refine ⟨3004365623056279539195541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005820830741706052260721 3004365623056279539195541)
              ·
                refine ⟨140829638580763103399791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3004365623056279539195541 140829638580763103399791)
                ·
                  rfl

theorem cell22_3702574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3702574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702574 prefixEnd_3702574 := by exact prefixLift 3702574
  have htrace : WordTrace (prefixWord ++ tailWord_3702574) baseStart_3702574 baseEnd_3702574 := by
    simpa [prefixWord, tailWord_3702574, baseEnd_3702574] using wordTrace_append hprefix tailTrace_3702574
  have hstable : (prefixWord ++ tailWord_3702574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702574).length < 2 ^ (prefixWord ++ tailWord_3702574).sum := by decide
  have hdescent : baseEnd_3702574 < baseStart_3702574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702589 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_3702589 : Nat := 118140960795 + 3702589 * 2 ^ 59
def prefixEnd_3702589 : Nat := 4983230072969 + 3 ^ 40 * 3702589 * 2
def baseEnd_3702589 : Nat := 1267471882033412891473073

theorem tailTrace_3702589 : CollatzResearch.WordTrace tailWord_3702589 prefixEnd_3702589 1267471882033412891473073 := by
  unfold tailWord_3702589
  simp only [CollatzResearch.WordTrace]
  refine ⟨135044515183159879702206821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90029676788773253134804547 135044515183159879702206821)
  ·
    refine ⟨25320846596842477444163779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135044515183159879702206821 25320846596842477444163779)
    ·
      refine ⟨37981269895263716166245669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25320846596842477444163779 37981269895263716166245669)
      ·
        refine ⟨7121488105361946781171063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37981269895263716166245669 7121488105361946781171063)
        ·
          refine ⟨10682232158042920171756595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121488105361946781171063 10682232158042920171756595)
          ·
            refine ⟨16023348237064380257634893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682232158042920171756595 16023348237064380257634893)
            ·
              refine ⟨6008755588899142596613085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16023348237064380257634893 6008755588899142596613085)
              ·
                refine ⟨2253283345837178473729907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6008755588899142596613085 2253283345837178473729907)
                ·
                  refine ⟨3379925018755767710594861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253283345837178473729907 3379925018755767710594861)
                  ·
                    refine ⟨1267471882033412891473073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3379925018755767710594861 1267471882033412891473073)
                    ·
                      rfl

theorem cell22_3702589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_3702589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702589 prefixEnd_3702589 := by exact prefixLift 3702589
  have htrace : WordTrace (prefixWord ++ tailWord_3702589) baseStart_3702589 baseEnd_3702589 := by
    simpa [prefixWord, tailWord_3702589, baseEnd_3702589] using wordTrace_append hprefix tailTrace_3702589
  have hstable : (prefixWord ++ tailWord_3702589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702589).length < 2 ^ (prefixWord ++ tailWord_3702589).sum := by decide
  have hdescent : baseEnd_3702589 < baseStart_3702589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702645 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3702645 : Nat := 118140960795 + 3702645 * 2 ^ 59
def prefixEnd_3702645 : Nat := 4983230072969 + 3 ^ 40 * 3702645 * 2
def baseEnd_3702645 : Nat := 1267491051977847412072901

theorem tailTrace_3702645 : CollatzResearch.WordTrace tailWord_3702645 prefixEnd_3702645 1267491051977847412072901 := by
  unfold tailWord_3702645
  simp only [CollatzResearch.WordTrace]
  refine ⟨135046557670957001266245389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90031038447304667510830259 135046557670957001266245389)
  ·
    refine ⟨50642459126608875474842021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135046557670957001266245389 50642459126608875474842021)
    ·
      refine ⟨9495461086239164151532879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50642459126608875474842021 9495461086239164151532879)
      ·
        refine ⟨14243191629358746227299319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9495461086239164151532879 14243191629358746227299319)
        ·
          refine ⟨21364787444038119340948979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14243191629358746227299319 21364787444038119340948979)
          ·
            refine ⟨32047181166057179011423469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21364787444038119340948979 32047181166057179011423469)
            ·
              refine ⟨12017692937271442129283801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32047181166057179011423469 12017692937271442129283801)
              ·
                refine ⟨9013269702953581596962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12017692937271442129283801 9013269702953581596962851)
                ·
                  refine ⟨13519904554430372395444277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013269702953581596962851 13519904554430372395444277)
                  ·
                    refine ⟨1267491051977847412072901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13519904554430372395444277 1267491051977847412072901)
                    ·
                      rfl

theorem cell22_3702645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3702645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702645 prefixEnd_3702645 := by exact prefixLift 3702645
  have htrace : WordTrace (prefixWord ++ tailWord_3702645) baseStart_3702645 baseEnd_3702645 := by
    simpa [prefixWord, tailWord_3702645, baseEnd_3702645] using wordTrace_append hprefix tailTrace_3702645
  have hstable : (prefixWord ++ tailWord_3702645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702645).length < 2 ^ (prefixWord ++ tailWord_3702645).sum := by decide
  have hdescent : baseEnd_3702645 < baseStart_3702645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702660 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3702660 : Nat := 118140960795 + 3702660 * 2 ^ 59
def prefixEnd_3702660 : Nat := 4983230072969 + 3 ^ 40 * 3702660 * 2
def baseEnd_3702660 : Nat := 1267496186784392372947855

theorem tailTrace_3702660 : CollatzResearch.WordTrace tailWord_3702660 prefixEnd_3702660 1267496186784392372947855 := by
  unfold tailWord_3702660
  simp only [CollatzResearch.WordTrace]
  refine ⟨67523552382951329414020717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90031403177268439218694289 67523552382951329414020717)
  ·
    refine ⟨25321332143606748530257769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67523552382951329414020717 25321332143606748530257769)
    ·
      refine ⟨18990999107705061397693327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25321332143606748530257769 18990999107705061397693327)
      ·
        refine ⟨28486498661557592096539991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18990999107705061397693327 28486498661557592096539991)
        ·
          refine ⟨42729747992336388144809987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28486498661557592096539991 42729747992336388144809987)
          ·
            refine ⟨64094621988504582217214981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42729747992336388144809987 64094621988504582217214981)
            ·
              refine ⟨12017741622844609165727809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64094621988504582217214981 12017741622844609165727809)
              ·
                refine ⟨9013306217133456874295857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12017741622844609165727809 9013306217133456874295857)
                ·
                  refine ⟨6759979662850092655721893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9013306217133456874295857 6759979662850092655721893)
                  ·
                    refine ⟨1267496186784392372947855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6759979662850092655721893 1267496186784392372947855)
                    ·
                      rfl

theorem cell22_3702660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3702660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702660 prefixEnd_3702660 := by exact prefixLift 3702660
  have htrace : WordTrace (prefixWord ++ tailWord_3702660) baseStart_3702660 baseEnd_3702660 := by
    simpa [prefixWord, tailWord_3702660, baseEnd_3702660] using wordTrace_append hprefix tailTrace_3702660
  have hstable : (prefixWord ++ tailWord_3702660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702660).length < 2 ^ (prefixWord ++ tailWord_3702660).sum := by decide
  have hdescent : baseEnd_3702660 < baseStart_3702660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702688 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_3702688 : Nat := 118140960795 + 3702688 * 2 ^ 59
def prefixEnd_3702688 : Nat := 4983230072969 + 3 ^ 40 * 3702688 * 2
def baseEnd_3702688 : Nat := 1267505771756609633247769

theorem tailTrace_3702688 : CollatzResearch.WordTrace tailWord_3702688 prefixEnd_3702688 1267505771756609633247769 := by
  unfold tailWord_3702688
  simp only [CollatzResearch.WordTrace]
  refine ⟨67524063004900609805030359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90032084006534146406707145 67524063004900609805030359)
  ·
    refine ⟨101286094507350914707545539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67524063004900609805030359 101286094507350914707545539)
    ·
      refine ⟨151929141761026372061318309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101286094507350914707545539 151929141761026372061318309)
      ·
        refine ⟨28486714080192444761497183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151929141761026372061318309 28486714080192444761497183)
        ·
          refine ⟨42730071120288667142245775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28486714080192444761497183 42730071120288667142245775)
          ·
            refine ⟨64095106680433000713368663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42730071120288667142245775 64095106680433000713368663)
            ·
              refine ⟨96142660020649501070052995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64095106680433000713368663 96142660020649501070052995)
              ·
                refine ⟨144213990030974251605079493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96142660020649501070052995 144213990030974251605079493)
                ·
                  refine ⟨27040123130807672175952405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144213990030974251605079493 27040123130807672175952405)
                  ·
                    refine ⟨1267505771756609633247769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27040123130807672175952405 1267505771756609633247769)
                    ·
                      rfl

theorem cell22_3702688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_3702688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702688 prefixEnd_3702688 := by exact prefixLift 3702688
  have htrace : WordTrace (prefixWord ++ tailWord_3702688) baseStart_3702688 baseEnd_3702688 := by
    simpa [prefixWord, tailWord_3702688, baseEnd_3702688] using wordTrace_append hprefix tailTrace_3702688
  have hstable : (prefixWord ++ tailWord_3702688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702688).length < 2 ^ (prefixWord ++ tailWord_3702688).sum := by decide
  have hdescent : baseEnd_3702688 < baseStart_3702688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702703 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 7]
def baseStart_3702703 : Nat := 118140960795 + 3702703 * 2 ^ 59
def prefixEnd_3702703 : Nat := 4983230072969 + 3 ^ 40 * 3702703 * 2
def baseEnd_3702703 : Nat := 422503635521051531374241

theorem tailTrace_3702703 : CollatzResearch.WordTrace tailWord_3702703 prefixEnd_3702703 422503635521051531374241 := by
  unfold tailWord_3702703
  simp only [CollatzResearch.WordTrace]
  refine ⟨135048673104746877171856763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90032448736497918114571175 135048673104746877171856763)
  ·
    refine ⟨202573009657120315757785145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135048673104746877171856763 202573009657120315757785145)
    ·
      refine ⟨151929757242840236818338859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202573009657120315757785145 151929757242840236818338859)
      ·
        refine ⟨227894635864260355227508289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151929757242840236818338859 227894635864260355227508289)
        ·
          refine ⟨170920976898195266420631217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227894635864260355227508289 170920976898195266420631217)
          ·
            refine ⟨128190732673646449815473413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170920976898195266420631217 128190732673646449815473413)
            ·
              refine ⟨24035762376308709340401265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128190732673646449815473413 24035762376308709340401265)
              ·
                refine ⟨18026821782231532005300949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24035762376308709340401265 18026821782231532005300949)
                ·
                  refine ⟨422503635521051531374241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18026821782231532005300949 422503635521051531374241)
                  ·
                    rfl

theorem cell22_3702703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_3702703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702703 prefixEnd_3702703 := by exact prefixLift 3702703
  have htrace : WordTrace (prefixWord ++ tailWord_3702703) baseStart_3702703 baseEnd_3702703 := by
    simpa [prefixWord, tailWord_3702703, baseEnd_3702703] using wordTrace_append hprefix tailTrace_3702703
  have hstable : (prefixWord ++ tailWord_3702703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702703).length < 2 ^ (prefixWord ++ tailWord_3702703).sum := by decide
  have hdescent : baseEnd_3702703 < baseStart_3702703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702788 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 5]
def baseStart_3702788 : Nat := 118140960795 + 3702788 * 2 ^ 59
def prefixEnd_3702788 : Nat := 4983230072969 + 3 ^ 40 * 3702788 * 2
def baseEnd_3702788 : Nat := 422513334600080901915821

theorem tailTrace_3702788 : CollatzResearch.WordTrace tailWord_3702788 prefixEnd_3702788 422513334600080901915821 := by
  unfold tailWord_3702788
  simp only [CollatzResearch.WordTrace]
  refine ⟨67525886654719468344350509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90034515539625957792467345 67525886654719468344350509)
  ·
    refine ⟨25322207495519800629131441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67525886654719468344350509 25322207495519800629131441)
    ·
      refine ⟨18991655621639850471848581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25322207495519800629131441 18991655621639850471848581)
      ·
        refine ⟨3560935429057471963471609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18991655621639850471848581 3560935429057471963471609)
        ·
          refine ⟨2670701571793103972603707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3560935429057471963471609 2670701571793103972603707)
          ·
            refine ⟨4006052357689655958905561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670701571793103972603707 4006052357689655958905561)
            ·
              refine ⟨3004539268267241969179171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006052357689655958905561 3004539268267241969179171)
              ·
                refine ⟨4506808902400862953768757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004539268267241969179171 4506808902400862953768757)
                ·
                  refine ⟨422513334600080901915821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4506808902400862953768757 422513334600080901915821)
                  ·
                    rfl

theorem cell22_3702788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_3702788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702788 prefixEnd_3702788 := by exact prefixLift 3702788
  have htrace : WordTrace (prefixWord ++ tailWord_3702788) baseStart_3702788 baseEnd_3702788 := by
    simpa [prefixWord, tailWord_3702788, baseEnd_3702788] using wordTrace_append hprefix tailTrace_3702788
  have hstable : (prefixWord ++ tailWord_3702788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702788).length < 2 ^ (prefixWord ++ tailWord_3702788).sum := by decide
  have hdescent : baseEnd_3702788 < baseStart_3702788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702795 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 4, 4]
def baseStart_3702795 : Nat := 118140960795 + 3702795 * 2 ^ 59
def prefixEnd_3702795 : Nat := 4983230072969 + 3 ^ 40 * 3702795 * 2
def baseEnd_3702795 : Nat := 1267542400043297020822441

theorem tailTrace_3702795 : CollatzResearch.WordTrace tailWord_3702795 prefixEnd_3702795 1267542400043297020822441 := by
  unfold tailWord_3702795
  simp only [CollatzResearch.WordTrace]
  refine ⟨135052028620413576884205839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90034685746942384589470559 135052028620413576884205839)
  ·
    refine ⟨202578042930620365326308759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135052028620413576884205839 202578042930620365326308759)
    ·
      refine ⟨303867064395930547989463139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202578042930620365326308759 303867064395930547989463139)
      ·
        refine ⟨455800596593895821984194709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303867064395930547989463139 455800596593895821984194709)
        ·
          refine ⟨21365652965338866655509127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 455800596593895821984194709 21365652965338866655509127)
          ·
            refine ⟨32048479448008299983263691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21365652965338866655509127 32048479448008299983263691)
            ·
              refine ⟨48072719172012449974895537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32048479448008299983263691 48072719172012449974895537)
              ·
                refine ⟨36054539379009337481171653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48072719172012449974895537 36054539379009337481171653)
                ·
                  refine ⟨6760226133564250777719685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36054539379009337481171653 6760226133564250777719685)
                  ·
                    refine ⟨1267542400043297020822441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6760226133564250777719685 1267542400043297020822441)
                    ·
                      rfl

theorem cell22_3702795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_3702795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702795 prefixEnd_3702795 := by exact prefixLift 3702795
  have htrace : WordTrace (prefixWord ++ tailWord_3702795) baseStart_3702795 baseEnd_3702795 := by
    simpa [prefixWord, tailWord_3702795, baseEnd_3702795] using wordTrace_append hprefix tailTrace_3702795
  have hstable : (prefixWord ++ tailWord_3702795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702795).length < 2 ^ (prefixWord ++ tailWord_3702795).sum := by decide
  have hdescent : baseEnd_3702795 < baseStart_3702795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702810 : List Nat := [3, 1, 1, 3, 1, 3, 2, 8]
def baseStart_3702810 : Nat := 118140960795 + 3702810 * 2 ^ 59
def prefixEnd_3702810 : Nat := 4983230072969 + 3 ^ 40 * 3702810 * 2
def baseEnd_3702810 : Nat := 140838614983315775744155

theorem tailTrace_3702810 : CollatzResearch.WordTrace tailWord_3702810 prefixEnd_3702810 140838614983315775744155 := by
  unfold tailWord_3702810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33763143928839808611500471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90035050476906156297334589 33763143928839808611500471)
  ·
    refine ⟨50644715893259712917250707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33763143928839808611500471 50644715893259712917250707)
    ·
      refine ⟨75967073839889569375876061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50644715893259712917250707 75967073839889569375876061)
      ·
        refine ⟨28487652689958588515953523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75967073839889569375876061 28487652689958588515953523)
        ·
          refine ⟨42731479034937882773930285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28487652689958588515953523 42731479034937882773930285)
          ·
            refine ⟨16024304638101706040223857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42731479034937882773930285 16024304638101706040223857)
            ·
              refine ⟨12018228478576279530167893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16024304638101706040223857 12018228478576279530167893)
              ·
                refine ⟨140838614983315775744155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12018228478576279530167893 140838614983315775744155)
                ·
                  rfl

theorem cell22_3702810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_3702810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702810 prefixEnd_3702810 := by exact prefixLift 3702810
  have htrace : WordTrace (prefixWord ++ tailWord_3702810) baseStart_3702810 baseEnd_3702810 := by
    simpa [prefixWord, tailWord_3702810, baseEnd_3702810] using wordTrace_append hprefix tailTrace_3702810
  have hstable : (prefixWord ++ tailWord_3702810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702810).length < 2 ^ (prefixWord ++ tailWord_3702810).sum := by decide
  have hdescent : baseEnd_3702810 < baseStart_3702810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702812 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3702812 : Nat := 118140960795 + 3702812 * 2 ^ 59
def prefixEnd_3702812 : Nat := 4983230072969 + 3 ^ 40 * 3702812 * 2
def baseEnd_3702812 : Nat := 1267548219490714643147389

theorem tailTrace_3702812 : CollatzResearch.WordTrace tailWord_3702812 prefixEnd_3702812 1267548219490714643147389 := by
  unfold tailWord_3702812
  simp only [CollatzResearch.WordTrace]
  refine ⟨67526324330675994393787345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90035099107567992525049793 67526324330675994393787345)
  ·
    refine ⟨50644743248006995795340509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67526324330675994393787345 50644743248006995795340509)
    ·
      refine ⟨18991778718002623423252691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50644743248006995795340509 18991778718002623423252691)
      ·
        refine ⟨28487668077003935134879037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18991778718002623423252691 28487668077003935134879037)
        ·
          refine ⟨10682875528876475675579639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28487668077003935134879037 10682875528876475675579639)
          ·
            refine ⟨16024313293314713513369459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682875528876475675579639 16024313293314713513369459)
            ·
              refine ⟨24036469939972070270054189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16024313293314713513369459 24036469939972070270054189)
              ·
                refine ⟨9013676227489526351270321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24036469939972070270054189 9013676227489526351270321)
                ·
                  refine ⟨6760257170617144763452741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9013676227489526351270321 6760257170617144763452741)
                  ·
                    refine ⟨1267548219490714643147389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6760257170617144763452741 1267548219490714643147389)
                    ·
                      rfl

theorem cell22_3702812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3702812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702812 prefixEnd_3702812 := by exact prefixLift 3702812
  have htrace : WordTrace (prefixWord ++ tailWord_3702812) baseStart_3702812 baseEnd_3702812 := by
    simpa [prefixWord, tailWord_3702812, baseEnd_3702812] using wordTrace_append hprefix tailTrace_3702812
  have hstable : (prefixWord ++ tailWord_3702812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702812).length < 2 ^ (prefixWord ++ tailWord_3702812).sum := by decide
  have hdescent : baseEnd_3702812 < baseStart_3702812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702842 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_3702842 : Nat := 118140960795 + 3702842 * 2 ^ 59
def prefixEnd_3702842 : Nat := 4983230072969 + 3 ^ 40 * 3702842 * 2
def baseEnd_3702842 : Nat := 1267558489103804564897297

theorem tailTrace_3702842 : CollatzResearch.WordTrace tailWord_3702842 prefixEnd_3702842 1267558489103804564897297 := by
  unfold tailWord_3702842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33763435712810825977791695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90035828567495535940777853 33763435712810825977791695)
  ·
    refine ⟨50645153569216238966687543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33763435712810825977791695 50645153569216238966687543)
    ·
      refine ⟨75967730353824358450031315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50645153569216238966687543 75967730353824358450031315)
      ·
        refine ⟨113951595530736537675046973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75967730353824358450031315 113951595530736537675046973)
        ·
          refine ⟨42731848324026201628142615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113951595530736537675046973 42731848324026201628142615)
          ·
            refine ⟨64097772486039302442213923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42731848324026201628142615 64097772486039302442213923)
            ·
              refine ⟨96146658729058953663320885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64097772486039302442213923 96146658729058953663320885)
              ·
                refine ⟨9013749255849276905936333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96146658729058953663320885 9013749255849276905936333)
                ·
                  refine ⟨3380155970943478839726125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9013749255849276905936333 3380155970943478839726125)
                  ·
                    refine ⟨1267558489103804564897297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380155970943478839726125 1267558489103804564897297)
                    ·
                      rfl

theorem cell22_3702842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_3702842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702842 prefixEnd_3702842 := by exact prefixLift 3702842
  have htrace : WordTrace (prefixWord ++ tailWord_3702842) baseStart_3702842 baseEnd_3702842 := by
    simpa [prefixWord, tailWord_3702842, baseEnd_3702842] using wordTrace_append hprefix tailTrace_3702842
  have hstable : (prefixWord ++ tailWord_3702842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702842).length < 2 ^ (prefixWord ++ tailWord_3702842).sum := by decide
  have hdescent : baseEnd_3702842 < baseStart_3702842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702876 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3702876 : Nat := 118140960795 + 3702876 * 2 ^ 59
def prefixEnd_3702876 : Nat := 4983230072969 + 3 ^ 40 * 3702876 * 2
def baseEnd_3702876 : Nat := 1267570127998639809547193

theorem tailTrace_3702876 : CollatzResearch.WordTrace tailWord_3702876 prefixEnd_3702876 1267570127998639809547193 := by
  unfold tailWord_3702876
  simp only [CollatzResearch.WordTrace]
  refine ⟨67527491466560063858952241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90036655288746751811936321 67527491466560063858952241)
  ·
    refine ⟨50645618599920047894214181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67527491466560063858952241 50645618599920047894214181)
    ·
      refine ⟨9496053487485008980165159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50645618599920047894214181 9496053487485008980165159)
      ·
        refine ⟨14244080231227513470247739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496053487485008980165159 14244080231227513470247739)
        ·
          refine ⟨21366120346841270205371609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14244080231227513470247739 21366120346841270205371609)
          ·
            refine ⟨16024590260130952654028707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21366120346841270205371609 16024590260130952654028707)
            ·
              refine ⟨24036885390196428981043061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16024590260130952654028707 24036885390196428981043061)
              ·
                refine ⟨2253458005330915216972787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24036885390196428981043061 2253458005330915216972787)
                ·
                  refine ⟨3380187007996372825459181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253458005330915216972787 3380187007996372825459181)
                  ·
                    refine ⟨1267570127998639809547193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380187007996372825459181 1267570127998639809547193)
                    ·
                      rfl

theorem cell22_3702876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3702876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702876 prefixEnd_3702876 := by exact prefixLift 3702876
  have htrace : WordTrace (prefixWord ++ tailWord_3702876) baseStart_3702876 baseEnd_3702876 := by
    simpa [prefixWord, tailWord_3702876, baseEnd_3702876] using wordTrace_append hprefix tailTrace_3702876
  have hstable : (prefixWord ++ tailWord_3702876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702876).length < 2 ^ (prefixWord ++ tailWord_3702876).sum := by decide
  have hdescent : baseEnd_3702876 < baseStart_3702876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702917 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 6]
def baseStart_3702917 : Nat := 118140960795 + 3702917 * 2 ^ 59
def prefixEnd_3702917 : Nat := 4983230072969 + 3 ^ 40 * 3702917 * 2
def baseEnd_3702917 : Nat := 422528054378843123090689

theorem tailTrace_3702917 : CollatzResearch.WordTrace tailWord_3702917 prefixEnd_3702917 422528054378843123090689 := by
  unfold tailWord_3702917
  simp only [CollatzResearch.WordTrace]
  refine ⟨135056478325971591720147005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90037652217314394480098003 135056478325971591720147005)
  ·
    refine ⟨50646179372239346895055127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135056478325971591720147005 50646179372239346895055127)
    ·
      refine ⟨75969269058359020342582691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50646179372239346895055127 75969269058359020342582691)
      ·
        refine ⟨113953903587538530513874037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75969269058359020342582691 113953903587538530513874037)
        ·
          refine ⟨10683178461331737235675691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113953903587538530513874037 10683178461331737235675691)
          ·
            refine ⟨16024767691997605853513537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683178461331737235675691 16024767691997605853513537)
            ·
              refine ⟨12018575768998204390135153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16024767691997605853513537 12018575768998204390135153)
              ·
                refine ⟨9013931826748653292601365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12018575768998204390135153 9013931826748653292601365)
                ·
                  refine ⟨422528054378843123090689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9013931826748653292601365 422528054378843123090689)
                  ·
                    rfl

theorem cell22_3702917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_3702917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702917 prefixEnd_3702917 := by exact prefixLift 3702917
  have htrace : WordTrace (prefixWord ++ tailWord_3702917) baseStart_3702917 baseEnd_3702917 := by
    simpa [prefixWord, tailWord_3702917, baseEnd_3702917] using wordTrace_append hprefix tailTrace_3702917
  have hstable : (prefixWord ++ tailWord_3702917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702917).length < 2 ^ (prefixWord ++ tailWord_3702917).sum := by decide
  have hdescent : baseEnd_3702917 < baseStart_3702917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702949 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_3702949 : Nat := 118140960795 + 3702949 * 2 ^ 59
def prefixEnd_3702949 : Nat := 4983230072969 + 3 ^ 40 * 3702949 * 2
def baseEnd_3702949 : Nat := 1267595117390491952471969

theorem tailTrace_3702949 : CollatzResearch.WordTrace tailWord_3702949 prefixEnd_3702949 1267595117390491952471969 := by
  unfold tailWord_3702949
  simp only [CollatzResearch.WordTrace]
  refine ⟨135057645461855661185311901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90038430307903774123541267 135057645461855661185311901)
  ·
    refine ⟨50646617048195872944491963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135057645461855661185311901 50646617048195872944491963)
    ·
      refine ⟨75969925572293809416737945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50646617048195872944491963 75969925572293809416737945)
      ·
        refine ⟨56977444179220357062553459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75969925572293809416737945 56977444179220357062553459)
        ·
          refine ⟨85466166268830535593830189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56977444179220357062553459 85466166268830535593830189)
          ·
            refine ⟨32049812350811450847686321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85466166268830535593830189 32049812350811450847686321)
            ·
              refine ⟨24037359263108588135764741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32049812350811450847686321 24037359263108588135764741)
              ·
                refine ⟨4507004861832860275455889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24037359263108588135764741 4507004861832860275455889)
                ·
                  refine ⟨3380253646374645206591917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507004861832860275455889 3380253646374645206591917)
                  ·
                    refine ⟨1267595117390491952471969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380253646374645206591917 1267595117390491952471969)
                    ·
                      rfl

theorem cell22_3702949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_3702949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702949 prefixEnd_3702949 := by exact prefixLift 3702949
  have htrace : WordTrace (prefixWord ++ tailWord_3702949) baseStart_3702949 baseEnd_3702949 := by
    simpa [prefixWord, tailWord_3702949, baseEnd_3702949] using wordTrace_append hprefix tailTrace_3702949
  have hstable : (prefixWord ++ tailWord_3702949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702949).length < 2 ^ (prefixWord ++ tailWord_3702949).sum := by decide
  have hdescent : baseEnd_3702949 < baseStart_3702949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702951 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 6]
def baseStart_3702951 : Nat := 118140960795 + 3702951 * 2 ^ 59
def prefixEnd_3702951 : Nat := 4983230072969 + 3 ^ 40 * 3702951 * 2
def baseEnd_3702951 : Nat := 422531934010454871307321

theorem tailTrace_3702951 : CollatzResearch.WordTrace tailWord_3702951 prefixEnd_3702951 422531934010454871307321 := by
  unfold tailWord_3702951
  simp only [CollatzResearch.WordTrace]
  refine ⟨135057718407848415526884707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90038478938565610351256471 135057718407848415526884707)
  ·
    refine ⟨202586577611772623290327061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135057718407848415526884707 202586577611772623290327061)
    ·
      refine ⟨9496245825551841716734081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202586577611772623290327061 9496245825551841716734081)
      ·
        refine ⟨7122184369163881287550561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9496245825551841716734081 7122184369163881287550561)
        ·
          refine ⟨5341638276872910965662921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7122184369163881287550561 5341638276872910965662921)
          ·
            refine ⟨4006228707654683224247191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5341638276872910965662921 4006228707654683224247191)
            ·
              refine ⟨6009343061482024836370787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006228707654683224247191 6009343061482024836370787)
              ·
                refine ⟨9014014592223037254556181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009343061482024836370787 9014014592223037254556181)
                ·
                  refine ⟨422531934010454871307321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9014014592223037254556181 422531934010454871307321)
                  ·
                    rfl

theorem cell22_3702951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 6].length) (baseStart_3702951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702951 prefixEnd_3702951 := by exact prefixLift 3702951
  have htrace : WordTrace (prefixWord ++ tailWord_3702951) baseStart_3702951 baseEnd_3702951 := by
    simpa [prefixWord, tailWord_3702951, baseEnd_3702951] using wordTrace_append hprefix tailTrace_3702951
  have hstable : (prefixWord ++ tailWord_3702951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702951).length < 2 ^ (prefixWord ++ tailWord_3702951).sum := by decide
  have hdescent : baseEnd_3702951 < baseStart_3702951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3702962 : List Nat := [3, 2, 1, 1, 1, 3, 4, 7]
def baseStart_3702962 : Nat := 118140960795 + 3702962 * 2 ^ 59
def prefixEnd_3702962 : Nat := 4983230072969 + 3 ^ 40 * 3702962 * 2
def baseEnd_3702962 : Nat := 140844396395129361321881

theorem tailTrace_3702962 : CollatzResearch.WordTrace tailWord_3702962 prefixEnd_3702962 140844396395129361321881 := by
  unfold tailWord_3702962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33764529902702141101383785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90038746407205709603690093 33764529902702141101383785)
  ·
    refine ⟨25323397427026605826037839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33764529902702141101383785 25323397427026605826037839)
    ·
      refine ⟨37985096140539908739056759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25323397427026605826037839 37985096140539908739056759)
      ·
        refine ⟨56977644210809863108585139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37985096140539908739056759 56977644210809863108585139)
        ·
          refine ⟨85466466316214794662877709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56977644210809863108585139 85466466316214794662877709)
          ·
            refine ⟨32049924868580547998579141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85466466316214794662877709 32049924868580547998579141)
            ·
              refine ⟨6009360912858852749733589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32049924868580547998579141 6009360912858852749733589)
              ·
                refine ⟨140844396395129361321881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6009360912858852749733589 140844396395129361321881)
                ·
                  rfl

theorem cell22_3702962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_3702962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3702962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3702962 prefixEnd_3702962 := by exact prefixLift 3702962
  have htrace : WordTrace (prefixWord ++ tailWord_3702962) baseStart_3702962 baseEnd_3702962 := by
    simpa [prefixWord, tailWord_3702962, baseEnd_3702962] using wordTrace_append hprefix tailTrace_3702962
  have hstable : (prefixWord ++ tailWord_3702962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3702962).length < 2 ^ (prefixWord ++ tailWord_3702962).sum := by decide
  have hdescent : baseEnd_3702962 < baseStart_3702962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3702962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703052 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_3703052 : Nat := 118140960795 + 3703052 * 2 ^ 59
def prefixEnd_3703052 : Nat := 4983230072969 + 3 ^ 40 * 3703052 * 2
def baseEnd_3703052 : Nat := 422543458798478005715551

theorem tailTrace_3703052 : CollatzResearch.WordTrace tailWord_3703052 prefixEnd_3703052 422543458798478005715551 := by
  unfold tailWord_3703052
  simp only [CollatzResearch.WordTrace]
  refine ⟨67530701090241254888155705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90040934786988339850874273 67530701090241254888155705)
  ·
    refine ⟨50648025817680941166116779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67530701090241254888155705 50648025817680941166116779)
    ·
      refine ⟨75972038726521411749175169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50648025817680941166116779 75972038726521411749175169)
      ·
        refine ⟨56979029044891058811881377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75972038726521411749175169 56979029044891058811881377)
        ·
          refine ⟨42734271783668294108911033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56979029044891058811881377 42734271783668294108911033)
          ·
            refine ⟨32050703837751220581683275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42734271783668294108911033 32050703837751220581683275)
            ·
              refine ⟨48076055756626830872524913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32050703837751220581683275 48076055756626830872524913)
              ·
                refine ⟨36057041817470123154393685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48076055756626830872524913 36057041817470123154393685)
                ·
                  refine ⟨422543458798478005715551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36057041817470123154393685 422543458798478005715551)
                  ·
                    rfl

theorem cell22_3703052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_3703052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703052 prefixEnd_3703052 := by exact prefixLift 3703052
  have htrace : WordTrace (prefixWord ++ tailWord_3703052) baseStart_3703052 baseEnd_3703052 := by
    simpa [prefixWord, tailWord_3703052, baseEnd_3703052] using wordTrace_append hprefix tailTrace_3703052
  have hstable : (prefixWord ++ tailWord_3703052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703052).length < 2 ^ (prefixWord ++ tailWord_3703052).sum := by decide
  have hdescent : baseEnd_3703052 < baseStart_3703052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703067 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_3703067 : Nat := 118140960795 + 3703067 * 2 ^ 59
def prefixEnd_3703067 : Nat := 4983230072969 + 3 ^ 40 * 3703067 * 2
def baseEnd_3703067 : Nat := 1267635511201978978021607

theorem tailTrace_3703067 : CollatzResearch.WordTrace tailWord_3703067 prefixEnd_3703067 1267635511201978978021607 := by
  unfold tailWord_3703067
  simp only [CollatzResearch.WordTrace]
  refine ⟨135061949275428167338107455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90041299516952111558738303 135061949275428167338107455)
  ·
    refine ⟨202592923913142251007161183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135061949275428167338107455 202592923913142251007161183)
    ·
      refine ⟨303889385869713376510741775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202592923913142251007161183 303889385869713376510741775)
      ·
        refine ⟨455834078804570064766112663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303889385869713376510741775 455834078804570064766112663)
        ·
          refine ⟨683751118206855097149168995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455834078804570064766112663 683751118206855097149168995)
          ·
            refine ⟨1025626677310282645723753493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683751118206855097149168995 1025626677310282645723753493)
            ·
              refine ⟨48076250498919499018300945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1025626677310282645723753493 48076250498919499018300945)
              ·
                refine ⟨36057187874189624263725709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48076250498919499018300945 36057187874189624263725709)
                ·
                  refine ⟨13521445452821109098897141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36057187874189624263725709 13521445452821109098897141)
                  ·
                    refine ⟨1267635511201978978021607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13521445452821109098897141 1267635511201978978021607)
                    ·
                      rfl

theorem cell22_3703067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_3703067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703067 prefixEnd_3703067 := by exact prefixLift 3703067
  have htrace : WordTrace (prefixWord ++ tailWord_3703067) baseStart_3703067 baseEnd_3703067 := by
    simpa [prefixWord, tailWord_3703067, baseEnd_3703067] using wordTrace_append hprefix tailTrace_3703067
  have hstable : (prefixWord ++ tailWord_3703067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703067).length < 2 ^ (prefixWord ++ tailWord_3703067).sum := by decide
  have hdescent : baseEnd_3703067 < baseStart_3703067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703084 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_3703084 : Nat := 118140960795 + 3703084 * 2 ^ 59
def prefixEnd_3703084 : Nat := 4983230072969 + 3 ^ 40 * 3703084 * 2
def baseEnd_3703084 : Nat := 1267641330649396600346555

theorem tailTrace_3703084 : CollatzResearch.WordTrace tailWord_3703084 prefixEnd_3703084 1267641330649396600346555 := by
  unfold tailWord_3703084
  simp only [CollatzResearch.WordTrace]
  refine ⟨67531284658183289620738153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90041712877577719494317537 67531284658183289620738153)
  ·
    refine ⟨50648463493637467215553615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67531284658183289620738153 50648463493637467215553615)
    ·
      refine ⟨75972695240456200823330423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50648463493637467215553615 75972695240456200823330423)
      ·
        refine ⟨113959042860684301234995635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75972695240456200823330423 113959042860684301234995635)
        ·
          refine ⟨170938564291026451852493453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113959042860684301234995635 170938564291026451852493453)
          ·
            refine ⟨64101961609134919444685045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170938564291026451852493453 64101961609134919444685045)
            ·
              refine ⟨6009558900856398697939223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64101961609134919444685045 6009558900856398697939223)
              ·
                refine ⟨9014338351284598046908835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009558900856398697939223 9014338351284598046908835)
                ·
                  refine ⟨13521507526926897070363253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9014338351284598046908835 13521507526926897070363253)
                  ·
                    refine ⟨1267641330649396600346555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13521507526926897070363253 1267641330649396600346555)
                    ·
                      rfl

theorem cell22_3703084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_3703084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703084 prefixEnd_3703084 := by exact prefixLift 3703084
  have htrace : WordTrace (prefixWord ++ tailWord_3703084) baseStart_3703084 baseEnd_3703084 := by
    simpa [prefixWord, tailWord_3703084, baseEnd_3703084] using wordTrace_append hprefix tailTrace_3703084
  have hstable : (prefixWord ++ tailWord_3703084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703084).length < 2 ^ (prefixWord ++ tailWord_3703084).sum := by decide
  have hdescent : baseEnd_3703084 < baseStart_3703084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703176 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_3703176 : Nat := 118140960795 + 3703176 * 2 ^ 59
def prefixEnd_3703176 : Nat := 4983230072969 + 3 ^ 40 * 3703176 * 2
def baseEnd_3703176 : Nat := 422557608043179675682091

theorem tailTrace_3703176 : CollatzResearch.WordTrace tailWord_3703176 prefixEnd_3703176 422557608043179675682091 := by
  unfold tailWord_3703176
  simp only [CollatzResearch.WordTrace]
  refine ⟨67532962416016639476912691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90043949888022185969216921 67532962416016639476912691)
  ·
    refine ⟨101299443624024959215369037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67532962416016639476912691 101299443624024959215369037)
    ·
      refine ⟨37987291359009359705763389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101299443624024959215369037 37987291359009359705763389)
      ·
        refine ⟨14245234259628509889661271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37987291359009359705763389 14245234259628509889661271)
        ·
          refine ⟨21367851389442764834491907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245234259628509889661271 21367851389442764834491907)
          ·
            refine ⟨32051777084164147251737861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21367851389442764834491907 32051777084164147251737861)
            ·
              refine ⟨6009708203280777609700849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32051777084164147251737861 6009708203280777609700849)
              ·
                refine ⟨4507281152460583207275637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6009708203280777609700849 4507281152460583207275637)
                ·
                  refine ⟨422557608043179675682091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4507281152460583207275637 422557608043179675682091)
                  ·
                    rfl

theorem cell22_3703176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_3703176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703176 prefixEnd_3703176 := by exact prefixLift 3703176
  have htrace : WordTrace (prefixWord ++ tailWord_3703176) baseStart_3703176 baseEnd_3703176 := by
    simpa [prefixWord, tailWord_3703176, baseEnd_3703176] using wordTrace_append hprefix tailTrace_3703176
  have hstable : (prefixWord ++ tailWord_3703176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703176).length < 2 ^ (prefixWord ++ tailWord_3703176).sum := by decide
  have hdescent : baseEnd_3703176 < baseStart_3703176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703180 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_3703180 : Nat := 118140960795 + 3703180 * 2 ^ 59
def prefixEnd_3703180 : Nat := 4983230072969 + 3 ^ 40 * 3703180 * 2
def baseEnd_3703180 : Nat := 1267674193411284349946261

theorem tailTrace_3703180 : CollatzResearch.WordTrace tailWord_3703180 prefixEnd_3703180 1267674193411284349946261 := by
  unfold tailWord_3703180
  simp only [CollatzResearch.WordTrace]
  refine ⟨67533035362009393818485497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90044047149345858424647329 67533035362009393818485497)
  ·
    refine ⟨50649776521507045363864123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67533035362009393818485497 50649776521507045363864123)
    ·
      refine ⟨75974664782260568045796185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50649776521507045363864123 75974664782260568045796185)
      ·
        refine ⟨56980998586695426034347139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75974664782260568045796185 56980998586695426034347139)
        ·
          refine ⟨85471497880043139051520709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56980998586695426034347139 85471497880043139051520709)
          ·
            refine ⟨16025905852508088572160133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85471497880043139051520709 16025905852508088572160133)
            ·
              refine ⟨3004857347345266607280025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16025905852508088572160133 3004857347345266607280025)
              ·
                refine ⟨2253643010508949955460019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004857347345266607280025 2253643010508949955460019)
                ·
                  refine ⟨3380464515763424933190029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253643010508949955460019 3380464515763424933190029)
                  ·
                    refine ⟨1267674193411284349946261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380464515763424933190029 1267674193411284349946261)
                    ·
                      rfl

theorem cell22_3703180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_3703180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703180 prefixEnd_3703180 := by exact prefixLift 3703180
  have htrace : WordTrace (prefixWord ++ tailWord_3703180) baseStart_3703180 baseEnd_3703180 := by
    simpa [prefixWord, tailWord_3703180, baseEnd_3703180] using wordTrace_append hprefix tailTrace_3703180
  have hstable : (prefixWord ++ tailWord_3703180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703180).length < 2 ^ (prefixWord ++ tailWord_3703180).sum := by decide
  have hdescent : baseEnd_3703180 < baseStart_3703180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703204 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_3703204 : Nat := 118140960795 + 3703204 * 2 ^ 59
def prefixEnd_3703204 : Nat := 4983230072969 + 3 ^ 40 * 3703204 * 2
def baseEnd_3703204 : Nat := 422560803033918762448729

theorem tailTrace_3703204 : CollatzResearch.WordTrace tailWord_3703204 prefixEnd_3703204 422560803033918762448729 := by
  unfold tailWord_3703204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67533473037965919867922333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90044630717287893157229777 67533473037965919867922333)
  ·
    refine ⟨25325052389237219950470875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67533473037965919867922333 25325052389237219950470875)
    ·
      refine ⟨37987578583855829925706313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25325052389237219950470875 37987578583855829925706313)
      ·
        refine ⟨28490683937891872444279735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37987578583855829925706313 28490683937891872444279735)
        ·
          refine ⟨42736025906837808666419603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28490683937891872444279735 42736025906837808666419603)
          ·
            refine ⟨64104038860256712999629405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42736025906837808666419603 64104038860256712999629405)
            ·
              refine ⟨24039014572596267374861027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64104038860256712999629405 24039014572596267374861027)
              ·
                refine ⟨36058521858894401062291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24039014572596267374861027 36058521858894401062291541)
                ·
                  refine ⟨422560803033918762448729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36058521858894401062291541 422560803033918762448729)
                  ·
                    rfl

theorem cell22_3703204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_3703204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703204 prefixEnd_3703204 := by exact prefixLift 3703204
  have htrace : WordTrace (prefixWord ++ tailWord_3703204) baseStart_3703204 baseEnd_3703204 := by
    simpa [prefixWord, tailWord_3703204, baseEnd_3703204] using wordTrace_append hprefix tailTrace_3703204
  have hstable : (prefixWord ++ tailWord_3703204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703204).length < 2 ^ (prefixWord ++ tailWord_3703204).sum := by decide
  have hdescent : baseEnd_3703204 < baseStart_3703204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703223 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 1, 4]
def baseStart_3703223 : Nat := 118140960795 + 3703223 * 2 ^ 59
def prefixEnd_3703223 : Nat := 4983230072969 + 3 ^ 40 * 3703223 * 2
def baseEnd_3703223 : Nat := 1267688913190046571121129

theorem tailTrace_3703223 : CollatzResearch.WordTrace tailWord_3703223 prefixEnd_3703223 1267688913190046571121129 := by
  unfold tailWord_3703223
  simp only [CollatzResearch.WordTrace]
  refine ⟨135067639062863005980786323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90045092708575337320524215 135067639062863005980786323)
  ·
    refine ⟨202601458594294508971179485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135067639062863005980786323 202601458594294508971179485)
    ·
      refine ⟨75975546972860440864192307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202601458594294508971179485 75975546972860440864192307)
      ·
        refine ⟨113963320459290661296288461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75975546972860440864192307 113963320459290661296288461)
        ·
          refine ⟨42736245172233997986108173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113963320459290661296288461 42736245172233997986108173)
          ·
            refine ⟨16026091939587749244790565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42736245172233997986108173 16026091939587749244790565)
            ·
              refine ⟨3004892238672702983398231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16026091939587749244790565 3004892238672702983398231)
              ·
                refine ⟨4507338358009054475097347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004892238672702983398231 4507338358009054475097347)
                ·
                  refine ⟨6761007537013581712646021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507338358009054475097347 6761007537013581712646021)
                  ·
                    refine ⟨1267688913190046571121129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761007537013581712646021 1267688913190046571121129)
                    ·
                      rfl

theorem cell22_3703223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_3703223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703223 prefixEnd_3703223 := by exact prefixLift 3703223
  have htrace : WordTrace (prefixWord ++ tailWord_3703223) baseStart_3703223 baseEnd_3703223 := by
    simpa [prefixWord, tailWord_3703223, baseEnd_3703223] using wordTrace_append hprefix tailTrace_3703223
  have hstable : (prefixWord ++ tailWord_3703223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703223).length < 2 ^ (prefixWord ++ tailWord_3703223).sum := by decide
  have hdescent : baseEnd_3703223 < baseStart_3703223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703253 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_3703253 : Nat := 118140960795 + 3703253 * 2 ^ 59
def prefixEnd_3703253 : Nat := 4983230072969 + 3 ^ 40 * 3703253 * 2
def baseEnd_3703253 : Nat := 1267699182803136492871037

theorem tailTrace_3703253 : CollatzResearch.WordTrace tailWord_3703253 prefixEnd_3703253 1267699182803136492871037 := by
  unfold tailWord_3703253
  simp only [CollatzResearch.WordTrace]
  refine ⟨135068733252754321104378413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90045822168502880736252275 135068733252754321104378413)
  ·
    refine ⟨50650774969782870414141905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135068733252754321104378413 50650774969782870414141905)
    ·
      refine ⟨37988081227337152810606429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50650774969782870414141905 37988081227337152810606429)
      ·
        refine ⟨14245530460251432303977411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37988081227337152810606429 14245530460251432303977411)
        ·
          refine ⟨21368295690377148455966117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245530460251432303977411 21368295690377148455966117)
          ·
            refine ⟨4006555441945715335493647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21368295690377148455966117 4006555441945715335493647)
            ·
              refine ⟨6009833162918573003240471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006555441945715335493647 6009833162918573003240471)
              ·
                refine ⟨9014749744377859504860707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009833162918573003240471 9014749744377859504860707)
                ·
                  refine ⟨13522124616566789257291061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9014749744377859504860707 13522124616566789257291061)
                  ·
                    refine ⟨1267699182803136492871037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13522124616566789257291061 1267699182803136492871037)
                    ·
                      rfl

theorem cell22_3703253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_3703253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703253 prefixEnd_3703253 := by exact prefixLift 3703253
  have htrace : WordTrace (prefixWord ++ tailWord_3703253) baseStart_3703253 baseEnd_3703253 := by
    simpa [prefixWord, tailWord_3703253, baseEnd_3703253] using wordTrace_append hprefix tailTrace_3703253
  have hstable : (prefixWord ++ tailWord_3703253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703253).length < 2 ^ (prefixWord ++ tailWord_3703253).sum := by decide
  have hdescent : baseEnd_3703253 < baseStart_3703253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703264 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_3703264 : Nat := 118140960795 + 3703264 * 2 ^ 59
def prefixEnd_3703264 : Nat := 4983230072969 + 3 ^ 40 * 3703264 * 2
def baseEnd_3703264 : Nat := 1267702948327936130846003

theorem tailTrace_3703264 : CollatzResearch.WordTrace tailWord_3703264 prefixEnd_3703264 1267702948327936130846003 := by
  unfold tailWord_3703264
  simp only [CollatzResearch.WordTrace]
  refine ⟨67534567227857234991514423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90046089637142979988685897 67534567227857234991514423)
  ·
    refine ⟨101301850841785852487271635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67534567227857234991514423 101301850841785852487271635)
    ·
      refine ⟨151952776262678778730907453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101301850841785852487271635 151952776262678778730907453)
      ·
        refine ⟨56982291098504542024090295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151952776262678778730907453 56982291098504542024090295)
        ·
          refine ⟨85473436647756813036135443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56982291098504542024090295 85473436647756813036135443)
          ·
            refine ⟨128210154971635219554203165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85473436647756813036135443 128210154971635219554203165)
            ·
              refine ⟨48078808114363207332826187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128210154971635219554203165 48078808114363207332826187)
              ·
                refine ⟨72118212171544810999239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48078808114363207332826187 72118212171544810999239281)
                ·
                  refine ⟨54088659128658608249429461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72118212171544810999239281 54088659128658608249429461)
                  ·
                    refine ⟨1267702948327936130846003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54088659128658608249429461 1267702948327936130846003)
                    ·
                      rfl

theorem cell22_3703264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_3703264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703264 prefixEnd_3703264 := by exact prefixLift 3703264
  have htrace : WordTrace (prefixWord ++ tailWord_3703264) baseStart_3703264 baseEnd_3703264 := by
    simpa [prefixWord, tailWord_3703264, baseEnd_3703264] using wordTrace_append hprefix tailTrace_3703264
  have hstable : (prefixWord ++ tailWord_3703264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703264).length < 2 ^ (prefixWord ++ tailWord_3703264).sum := by decide
  have hdescent : baseEnd_3703264 < baseStart_3703264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703279 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_3703279 : Nat := 118140960795 + 3703279 * 2 ^ 59
def prefixEnd_3703279 : Nat := 4983230072969 + 3 ^ 40 * 3703279 * 2
def baseEnd_3703279 : Nat := 1267708083134481091720957

theorem tailTrace_3703279 : CollatzResearch.WordTrace tailWord_3703279 prefixEnd_3703279 1267708083134481091720957 := by
  unfold tailWord_3703279
  simp only [CollatzResearch.WordTrace]
  refine ⟨135069681550660127544824891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90046454367106751696549927 135069681550660127544824891)
  ·
    refine ⟨202604522325990191317237337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135069681550660127544824891 202604522325990191317237337)
    ·
      refine ⟨151953391744492643487928003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202604522325990191317237337 151953391744492643487928003)
      ·
        refine ⟨227930087616738965231892005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151953391744492643487928003 227930087616738965231892005)
        ·
          refine ⟨42736891428138555980979751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227930087616738965231892005 42736891428138555980979751)
          ·
            refine ⟨64105337142207833971469627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42736891428138555980979751 64105337142207833971469627)
            ·
              refine ⟨96158005713311750957204441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64105337142207833971469627 96158005713311750957204441)
              ·
                refine ⟨72118504284983813217903331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96158005713311750957204441 72118504284983813217903331)
                ·
                  refine ⟨108177756427475719826854997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72118504284983813217903331 108177756427475719826854997)
                  ·
                    refine ⟨1267708083134481091720957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108177756427475719826854997 1267708083134481091720957)
                    ·
                      rfl

theorem cell22_3703279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_3703279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703279 prefixEnd_3703279 := by exact prefixLift 3703279
  have htrace : WordTrace (prefixWord ++ tailWord_3703279) baseStart_3703279 baseEnd_3703279 := by
    simpa [prefixWord, tailWord_3703279, baseEnd_3703279] using wordTrace_append hprefix tailTrace_3703279
  have hstable : (prefixWord ++ tailWord_3703279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703279).length < 2 ^ (prefixWord ++ tailWord_3703279).sum := by decide
  have hdescent : baseEnd_3703279 < baseStart_3703279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703285 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3703285 : Nat := 118140960795 + 3703285 * 2 ^ 59
def prefixEnd_3703285 : Nat := 4983230072969 + 3 ^ 40 * 3703285 * 2
def baseEnd_3703285 : Nat := 1267710137057099076070939

theorem tailTrace_3703285 : CollatzResearch.WordTrace tailWord_3703285 prefixEnd_3703285 1267710137057099076070939 := by
  unfold tailWord_3703285
  simp only [CollatzResearch.WordTrace]
  refine ⟨135069900388638390569543309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90046600259092260379695539 135069900388638390569543309)
  ·
    refine ⟨50651212645739396463578741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135069900388638390569543309 50651212645739396463578741)
    ·
      refine ⟨4748551185538068418460507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50651212645739396463578741 4748551185538068418460507)
      ·
        refine ⟨7122826778307102627690761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4748551185538068418460507 7122826778307102627690761)
        ·
          refine ⟨5342120083730326970768071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7122826778307102627690761 5342120083730326970768071)
          ·
            refine ⟨8013180125595490456152107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342120083730326970768071 8013180125595490456152107)
            ·
              refine ⟨12019770188393235684228161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013180125595490456152107 12019770188393235684228161)
              ·
                refine ⟨9014827641294926763171121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12019770188393235684228161 9014827641294926763171121)
                ·
                  refine ⟨6761120730971195072378341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014827641294926763171121 6761120730971195072378341)
                  ·
                    refine ⟨1267710137057099076070939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761120730971195072378341 1267710137057099076070939)
                    ·
                      rfl

theorem cell22_3703285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3703285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703285 prefixEnd_3703285 := by exact prefixLift 3703285
  have htrace : WordTrace (prefixWord ++ tailWord_3703285) baseStart_3703285 baseEnd_3703285 := by
    simpa [prefixWord, tailWord_3703285, baseEnd_3703285] using wordTrace_append hprefix tailTrace_3703285
  have hstable : (prefixWord ++ tailWord_3703285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703285).length < 2 ^ (prefixWord ++ tailWord_3703285).sum := by decide
  have hdescent : baseEnd_3703285 < baseStart_3703285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703371 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 1, 5]
def baseStart_3703371 : Nat := 118140960795 + 3703371 * 2 ^ 59
def prefixEnd_3703371 : Nat := 4983230072969 + 3 ^ 40 * 3703371 * 2
def baseEnd_3703371 : Nat := 1267739576614623518420675

theorem tailTrace_3703371 : CollatzResearch.WordTrace tailWord_3703371 prefixEnd_3703371 1267739576614623518420675 := by
  unfold tailWord_3703371
  simp only [CollatzResearch.WordTrace]
  refine ⟨135073037066326827257173967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90048691377551218171449311 135073037066326827257173967)
  ·
    refine ⟨202609555599490240885760951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135073037066326827257173967 202609555599490240885760951)
    ·
      refine ⟨303914333399235361328641427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202609555599490240885760951 303914333399235361328641427)
      ·
        refine ⟨455871500098853041992962141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303914333399235361328641427 455871500098853041992962141)
        ·
          refine ⟨170951812537069890747360803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455871500098853041992962141 170951812537069890747360803)
          ·
            refine ⟨256427718805604836121041205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170951812537069890747360803 256427718805604836121041205)
            ·
              refine ⟨24040098638025453386347613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256427718805604836121041205 24040098638025453386347613)
              ·
                refine ⟨9015036989259545019880355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24040098638025453386347613 9015036989259545019880355)
                ·
                  refine ⟨13522555483889317529820533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015036989259545019880355 13522555483889317529820533)
                  ·
                    refine ⟨1267739576614623518420675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13522555483889317529820533 1267739576614623518420675)
                    ·
                      rfl

theorem cell22_3703371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_3703371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703371 prefixEnd_3703371 := by exact prefixLift 3703371
  have htrace : WordTrace (prefixWord ++ tailWord_3703371) baseStart_3703371 baseEnd_3703371 := by
    simpa [prefixWord, tailWord_3703371, baseEnd_3703371] using wordTrace_append hprefix tailTrace_3703371
  have hstable : (prefixWord ++ tailWord_3703371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703371).length < 2 ^ (prefixWord ++ tailWord_3703371).sum := by decide
  have hdescent : baseEnd_3703371 < baseStart_3703371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703373 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3703373 : Nat := 118140960795 + 3703373 * 2 ^ 59
def prefixEnd_3703373 : Nat := 4983230072969 + 3 ^ 40 * 3703373 * 2
def baseEnd_3703373 : Nat := 422580087085165393290223

theorem tailTrace_3703373 : CollatzResearch.WordTrace tailWord_3703373 prefixEnd_3703373 422580087085165393290223 := by
  unfold tailWord_3703373
  simp only [CollatzResearch.WordTrace]
  refine ⟨135073110012319581598746773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90048740008213054399164515 135073110012319581598746773)
  ·
    refine ⟨6331552031827480387441255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135073110012319581598746773 6331552031827480387441255)
    ·
      refine ⟨9497328047741220581161883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6331552031827480387441255 9497328047741220581161883)
      ·
        refine ⟨14245992071611830871742825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9497328047741220581161883 14245992071611830871742825)
        ·
          refine ⟨10684494053708873153807119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14245992071611830871742825 10684494053708873153807119)
          ·
            refine ⟨16026741080563309730710679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684494053708873153807119 16026741080563309730710679)
            ·
              refine ⟨24040111620844964596066019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16026741080563309730710679 24040111620844964596066019)
              ·
                refine ⟨36060167431267446894099029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24040111620844964596066019 36060167431267446894099029)
                ·
                  refine ⟨422580087085165393290223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36060167431267446894099029 422580087085165393290223)
                  ·
                    rfl

theorem cell22_3703373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3703373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703373 prefixEnd_3703373 := by exact prefixLift 3703373
  have htrace : WordTrace (prefixWord ++ tailWord_3703373) baseStart_3703373 baseEnd_3703373 := by
    simpa [prefixWord, tailWord_3703373, baseEnd_3703373] using wordTrace_append hprefix tailTrace_3703373
  have hstable : (prefixWord ++ tailWord_3703373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703373).length < 2 ^ (prefixWord ++ tailWord_3703373).sum := by decide
  have hdescent : baseEnd_3703373 < baseStart_3703373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703405 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3703405 : Nat := 118140960795 + 3703405 * 2 ^ 59
def prefixEnd_3703405 : Nat := 4983230072969 + 3 ^ 40 * 3703405 * 2
def baseEnd_3703405 : Nat := 1267751215509458763070571

theorem tailTrace_3703405 : CollatzResearch.WordTrace tailWord_3703405 prefixEnd_3703405 1267751215509458763070571 := by
  unfold tailWord_3703405
  simp only [CollatzResearch.WordTrace]
  refine ⟨135074277148203651063911669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90049518098802434042607779 135074277148203651063911669)
  ·
    refine ⟨12663213482644092287241719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135074277148203651063911669 12663213482644092287241719)
    ·
      refine ⟨18994820223966138430862579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12663213482644092287241719 18994820223966138430862579)
      ·
        refine ⟨28492230335949207646293869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18994820223966138430862579 28492230335949207646293869)
        ·
          refine ⟨10684586375980952867360201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28492230335949207646293869 10684586375980952867360201)
          ·
            refine ⟨8013439781985714650520151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10684586375980952867360201 8013439781985714650520151)
            ·
              refine ⟨12020159672978571975780227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013439781985714650520151 12020159672978571975780227)
              ·
                refine ⟨18030239509467857963670341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12020159672978571975780227 18030239509467857963670341)
                ·
                  refine ⟨3380669908025223368188189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18030239509467857963670341 3380669908025223368188189)
                  ·
                    refine ⟨1267751215509458763070571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380669908025223368188189 1267751215509458763070571)
                    ·
                      rfl

theorem cell22_3703405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3703405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703405 prefixEnd_3703405 := by exact prefixLift 3703405
  have htrace : WordTrace (prefixWord ++ tailWord_3703405) baseStart_3703405 baseEnd_3703405 := by
    simpa [prefixWord, tailWord_3703405, baseEnd_3703405] using wordTrace_append hprefix tailTrace_3703405
  have hstable : (prefixWord ++ tailWord_3703405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703405).length < 2 ^ (prefixWord ++ tailWord_3703405).sum := by decide
  have hdescent : baseEnd_3703405 < baseStart_3703405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703426 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3703426 : Nat := 118140960795 + 3703426 * 2 ^ 59
def prefixEnd_3703426 : Nat := 4983230072969 + 3 ^ 40 * 3703426 * 2
def baseEnd_3703426 : Nat := 1267758404238621708295507

theorem tailTrace_3703426 : CollatzResearch.WordTrace tailWord_3703426 prefixEnd_3703426 1267758404238621708295507 := by
  unfold tailWord_3703426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33768760770281892912606533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90050028720751714433617421 33768760770281892912606533)
  ·
    refine ⟨6331642644427854921113725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33768760770281892912606533 6331642644427854921113725)
    ·
      refine ⟨2374365991660445595417647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6331642644427854921113725 2374365991660445595417647)
      ·
        refine ⟨3561548987490668393126471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374365991660445595417647 3561548987490668393126471)
        ·
          refine ⟨5342323481236002589689707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561548987490668393126471 5342323481236002589689707)
          ·
            refine ⟨8013485221854003884534561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342323481236002589689707 8013485221854003884534561)
            ·
              refine ⟨6010113916390502913400921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8013485221854003884534561 6010113916390502913400921)
              ·
                refine ⟨4507585437292877185050691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010113916390502913400921 4507585437292877185050691)
                ·
                  refine ⟨6761378155939315777576037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507585437292877185050691 6761378155939315777576037)
                  ·
                    refine ⟨1267758404238621708295507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761378155939315777576037 1267758404238621708295507)
                    ·
                      rfl

theorem cell22_3703426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3703426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703426 prefixEnd_3703426 := by exact prefixLift 3703426
  have htrace : WordTrace (prefixWord ++ tailWord_3703426) baseStart_3703426 baseEnd_3703426 := by
    simpa [prefixWord, tailWord_3703426, baseEnd_3703426] using wordTrace_append hprefix tailTrace_3703426
  have hstable : (prefixWord ++ tailWord_3703426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703426).length < 2 ^ (prefixWord ++ tailWord_3703426).sum := by decide
  have hdescent : baseEnd_3703426 < baseStart_3703426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703604 : List Nat := [2, 5, 1, 1, 3, 2, 2, 6]
def baseStart_3703604 : Nat := 118140960795 + 3703604 * 2 ^ 59
def prefixEnd_3703604 : Nat := 4983230072969 + 3 ^ 40 * 3703604 * 2
def baseEnd_3703604 : Nat := 140868815252920953038329

theorem tailTrace_3703604 : CollatzResearch.WordTrace tailWord_3703604 prefixEnd_3703604 140868815252920953038329 := by
  unfold tailWord_3703604
  simp only [CollatzResearch.WordTrace]
  refine ⟨67540767637241354025202933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90054356849655138700270577 67540767637241354025202933)
  ·
    refine ⟨6331946965991376939862775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67540767637241354025202933 6331946965991376939862775)
    ·
      refine ⟨9497920448987065409794163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6331946965991376939862775 9497920448987065409794163)
      ·
        refine ⟨14246880673480598114691245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9497920448987065409794163 14246880673480598114691245)
        ·
          refine ⟨5342580252555224293009217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14246880673480598114691245 5342580252555224293009217)
          ·
            refine ⟨4006935189416418219756913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342580252555224293009217 4006935189416418219756913)
            ·
              refine ⟨3005201392062313664817685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006935189416418219756913 3005201392062313664817685)
              ·
                refine ⟨140868815252920953038329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3005201392062313664817685 140868815252920953038329)
                ·
                  rfl

theorem cell22_3703604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 6].length) (baseStart_3703604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703604 prefixEnd_3703604 := by exact prefixLift 3703604
  have htrace : WordTrace (prefixWord ++ tailWord_3703604) baseStart_3703604 baseEnd_3703604 := by
    simpa [prefixWord, tailWord_3703604, baseEnd_3703604] using wordTrace_append hprefix tailTrace_3703604
  have hstable : (prefixWord ++ tailWord_3703604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703604).length < 2 ^ (prefixWord ++ tailWord_3703604).sum := by decide
  have hdescent : baseEnd_3703604 < baseStart_3703604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703636 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_3703636 : Nat := 118140960795 + 3703636 * 2 ^ 59
def prefixEnd_3703636 : Nat := 4983230072969 + 3 ^ 40 * 3703636 * 2
def baseEnd_3703636 : Nat := 1267830291530251160544863

theorem tailTrace_3703636 : CollatzResearch.WordTrace tailWord_3703636 prefixEnd_3703636 1267830291530251160544863 := by
  unfold tailWord_3703636
  simp only [CollatzResearch.WordTrace]
  refine ⟨67541351205183388757785381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90055134940244518343713841 67541351205183388757785381)
  ·
    refine ⟨12664003350971885392084759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67541351205183388757785381 12664003350971885392084759)
    ·
      refine ⟨18996005026457828088127139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12664003350971885392084759 18996005026457828088127139)
      ·
        refine ⟨28494007539686742132190709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18996005026457828088127139 28494007539686742132190709)
        ·
          refine ⟨2671313206845632074892879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28494007539686742132190709 2671313206845632074892879)
          ·
            refine ⟨4006969810268448112339319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671313206845632074892879 4006969810268448112339319)
            ·
              refine ⟨6010454715402672168508979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006969810268448112339319 6010454715402672168508979)
              ·
                refine ⟨9015682073104008252763469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010454715402672168508979 9015682073104008252763469)
                ·
                  refine ⟨3380880777414003094786301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9015682073104008252763469 3380880777414003094786301)
                  ·
                    refine ⟨1267830291530251160544863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380880777414003094786301 1267830291530251160544863)
                    ·
                      rfl

theorem cell22_3703636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_3703636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703636 prefixEnd_3703636 := by exact prefixLift 3703636
  have htrace : WordTrace (prefixWord ++ tailWord_3703636) baseStart_3703636 baseEnd_3703636 := by
    simpa [prefixWord, tailWord_3703636, baseEnd_3703636] using wordTrace_append hprefix tailTrace_3703636
  have hstable : (prefixWord ++ tailWord_3703636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703636).length < 2 ^ (prefixWord ++ tailWord_3703636).sum := by decide
  have hdescent : baseEnd_3703636 < baseStart_3703636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703675 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 6, 3]
def baseStart_3703675 : Nat := 118140960795 + 3703675 * 2 ^ 59
def prefixEnd_3703675 : Nat := 4983230072969 + 3 ^ 40 * 3703675 * 2
def baseEnd_3703675 : Nat := 1267843642027268058819743

theorem tailTrace_3703675 : CollatzResearch.WordTrace tailWord_3703675 prefixEnd_3703675 1267843642027268058819743 := by
  unfold tailWord_3703675
  simp only [CollatzResearch.WordTrace]
  refine ⟨135084124857225487176240479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90056083238150324784160319 135084124857225487176240479)
  ·
    refine ⟨202626187285838230764360719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135084124857225487176240479 202626187285838230764360719)
    ·
      refine ⟨303939280928757346146541079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202626187285838230764360719 303939280928757346146541079)
      ·
        refine ⟨455908921393136019219811619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303939280928757346146541079 455908921393136019219811619)
        ·
          refine ⟨683863382089704028829717429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455908921393136019219811619 683863382089704028829717429)
          ·
            refine ⟨64112192070909752702786009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 683863382089704028829717429 64112192070909752702786009)
            ·
              refine ⟨48084144053182314527089507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64112192070909752702786009 48084144053182314527089507)
              ·
                refine ⟨72126216079773471790634261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48084144053182314527089507 72126216079773471790634261)
                ·
                  refine ⟨3380916378739381490185981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72126216079773471790634261 3380916378739381490185981)
                  ·
                    refine ⟨1267843642027268058819743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380916378739381490185981 1267843642027268058819743)
                    ·
                      rfl

theorem cell22_3703675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 3].length) (baseStart_3703675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703675 prefixEnd_3703675 := by exact prefixLift 3703675
  have htrace : WordTrace (prefixWord ++ tailWord_3703675) baseStart_3703675 baseEnd_3703675 := by
    simpa [prefixWord, tailWord_3703675, baseEnd_3703675] using wordTrace_append hprefix tailTrace_3703675
  have hstable : (prefixWord ++ tailWord_3703675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703675).length < 2 ^ (prefixWord ++ tailWord_3703675).sum := by decide
  have hdescent : baseEnd_3703675 < baseStart_3703675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703692 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_3703692 : Nat := 118140960795 + 3703692 * 2 ^ 59
def prefixEnd_3703692 : Nat := 4983230072969 + 3 ^ 40 * 3703692 * 2
def baseEnd_3703692 : Nat := 1267849461474685681144691

theorem tailTrace_3703692 : CollatzResearch.WordTrace tailWord_3703692 prefixEnd_3703692 1267849461474685681144691 := by
  unfold tailWord_3703692
  simp only [CollatzResearch.WordTrace]
  refine ⟨67542372449081949539804665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90056496598775932719739553 67542372449081949539804665)
  ·
    refine ⟨50656779336811462154853499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67542372449081949539804665 50656779336811462154853499)
    ·
      refine ⟨75985169005217193232280249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50656779336811462154853499 75985169005217193232280249)
      ·
        refine ⟨56988876753912894924210187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75985169005217193232280249 56988876753912894924210187)
        ·
          refine ⟨85483315130869342386315281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56988876753912894924210187 85483315130869342386315281)
          ·
            refine ⟨64112486348152006789736461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85483315130869342386315281 64112486348152006789736461)
            ·
              refine ⟨24042182380557002546151173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64112486348152006789736461 24042182380557002546151173)
              ·
                refine ⟨4507909196354437977403345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24042182380557002546151173 4507909196354437977403345)
                ·
                  refine ⟨3380931897265828483052509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4507909196354437977403345 3380931897265828483052509)
                  ·
                    refine ⟨1267849461474685681144691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380931897265828483052509 1267849461474685681144691)
                    ·
                      rfl

theorem cell22_3703692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_3703692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703692 prefixEnd_3703692 := by exact prefixLift 3703692
  have htrace : WordTrace (prefixWord ++ tailWord_3703692) baseStart_3703692 baseEnd_3703692 := by
    simpa [prefixWord, tailWord_3703692, baseEnd_3703692] using wordTrace_append hprefix tailTrace_3703692
  have hstable : (prefixWord ++ tailWord_3703692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703692).length < 2 ^ (prefixWord ++ tailWord_3703692).sum := by decide
  have hdescent : baseEnd_3703692 < baseStart_3703692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703825 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3703825 : Nat := 118140960795 + 3703825 * 2 ^ 59
def prefixEnd_3703825 : Nat := 4983230072969 + 3 ^ 40 * 3703825 * 2
def baseEnd_3703825 : Nat := 1267894990092717667569283

theorem tailTrace_3703825 : CollatzResearch.WordTrace tailWord_3703825 prefixEnd_3703825 1267894990092717667569283 := by
  unfold tailWord_3703825
  simp only [CollatzResearch.WordTrace]
  refine ⟨135089595806682062794200929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90059730537788041862800619 135089595806682062794200929)
  ·
    refine ⟨101317196855011547095650697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135089595806682062794200929 101317196855011547095650697)
    ·
      refine ⟨75987897641258660321738023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101317196855011547095650697 75987897641258660321738023)
      ·
        refine ⟨113981846461887990482607035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75987897641258660321738023 113981846461887990482607035)
        ·
          refine ⟨170972769692831985723910553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113981846461887990482607035 170972769692831985723910553)
          ·
            refine ⟨128229577269623989292932915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170972769692831985723910553 128229577269623989292932915)
            ·
              refine ⟨192344365904435983939399373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128229577269623989292932915 192344365904435983939399373)
              ·
                refine ⟨72129137214163493977274765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192344365904435983939399373 72129137214163493977274765)
                ·
                  refine ⟨27048426455311310241478037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72129137214163493977274765 27048426455311310241478037)
                  ·
                    refine ⟨1267894990092717667569283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27048426455311310241478037 1267894990092717667569283)
                    ·
                      rfl

theorem cell22_3703825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3703825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703825 prefixEnd_3703825 := by exact prefixLift 3703825
  have htrace : WordTrace (prefixWord ++ tailWord_3703825) baseStart_3703825 baseEnd_3703825 := by
    simpa [prefixWord, tailWord_3703825, baseEnd_3703825] using wordTrace_append hprefix tailTrace_3703825
  have hstable : (prefixWord ++ tailWord_3703825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703825).length < 2 ^ (prefixWord ++ tailWord_3703825).sum := by decide
  have hdescent : baseEnd_3703825 < baseStart_3703825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703831 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 1, 4]
def baseStart_3703831 : Nat := 118140960795 + 3703831 * 2 ^ 59
def prefixEnd_3703831 : Nat := 4983230072969 + 3 ^ 40 * 3703831 * 2
def baseEnd_3703831 : Nat := 1267897044015335651919265

theorem tailTrace_3703831 : CollatzResearch.WordTrace tailWord_3703831 prefixEnd_3703831 1267897044015335651919265 := by
  unfold tailWord_3703831
  simp only [CollatzResearch.WordTrace]
  refine ⟨135089814644660325818919347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90059876429773550545946231 135089814644660325818919347)
  ·
    refine ⟨202634721966990488728379021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135089814644660325818919347 202634721966990488728379021)
    ·
      refine ⟨75988020737621433273142133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202634721966990488728379021 75988020737621433273142133)
      ·
        refine ⟨7123876944152009369357075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75988020737621433273142133 7123876944152009369357075)
        ·
          refine ⟨10685815416228014054035613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123876944152009369357075 10685815416228014054035613)
          ·
            refine ⟨4007180781085505270263355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10685815416228014054035613 4007180781085505270263355)
            ·
              refine ⟨6010771171628257905395033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007180781085505270263355 6010771171628257905395033)
              ·
                refine ⟨4508078378721193429046275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010771171628257905395033 4508078378721193429046275)
                ·
                  refine ⟨6762117568081790143569413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508078378721193429046275 6762117568081790143569413)
                  ·
                    refine ⟨1267897044015335651919265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762117568081790143569413 1267897044015335651919265)
                    ·
                      rfl

theorem cell22_3703831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_3703831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703831 prefixEnd_3703831 := by exact prefixLift 3703831
  have htrace : WordTrace (prefixWord ++ tailWord_3703831) baseStart_3703831 baseEnd_3703831 := by
    simpa [prefixWord, tailWord_3703831, baseEnd_3703831] using wordTrace_append hprefix tailTrace_3703831
  have hstable : (prefixWord ++ tailWord_3703831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703831).length < 2 ^ (prefixWord ++ tailWord_3703831).sum := by decide
  have hdescent : baseEnd_3703831 < baseStart_3703831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703844 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3703844 : Nat := 118140960795 + 3703844 * 2 ^ 59
def prefixEnd_3703844 : Nat := 4983230072969 + 3 ^ 40 * 3703844 * 2
def baseEnd_3703844 : Nat := 1267901494181007951344225

theorem tailTrace_3703844 : CollatzResearch.WordTrace tailWord_3703844 prefixEnd_3703844 1267901494181007951344225 := by
  unfold tailWord_3703844
  simp only [CollatzResearch.WordTrace]
  refine ⟨67545144396806614519571293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90060192529075486026095057 67545144396806614519571293)
  ·
    refine ⟨25329429148802480444839235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67545144396806614519571293 25329429148802480444839235)
    ·
      refine ⟨37994143723203720667258853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25329429148802480444839235 37994143723203720667258853)
      ·
        refine ⟨7123901948100697625111035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37994143723203720667258853 7123901948100697625111035)
        ·
          refine ⟨10685852922151046437666553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123901948100697625111035 10685852922151046437666553)
          ·
            refine ⟨8014389691613284828249915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10685852922151046437666553 8014389691613284828249915)
            ·
              refine ⟨12021584537419927242374873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8014389691613284828249915 12021584537419927242374873)
              ·
                refine ⟨9016188403064945431781155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021584537419927242374873 9016188403064945431781155)
                ·
                  refine ⟨13524282604597418147671733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016188403064945431781155 13524282604597418147671733)
                  ·
                    refine ⟨1267901494181007951344225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13524282604597418147671733 1267901494181007951344225)
                    ·
                      rfl

theorem cell22_3703844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3703844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703844 prefixEnd_3703844 := by exact prefixLift 3703844
  have htrace : WordTrace (prefixWord ++ tailWord_3703844) baseStart_3703844 baseEnd_3703844 := by
    simpa [prefixWord, tailWord_3703844, baseEnd_3703844] using wordTrace_append hprefix tailTrace_3703844
  have hstable : (prefixWord ++ tailWord_3703844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703844).length < 2 ^ (prefixWord ++ tailWord_3703844).sum := by decide
  have hdescent : baseEnd_3703844 < baseStart_3703844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703855 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_3703855 : Nat := 118140960795 + 3703855 * 2 ^ 59
def prefixEnd_3703855 : Nat := 4983230072969 + 3 ^ 40 * 3703855 * 2
def baseEnd_3703855 : Nat := 1267905259705807589319191

theorem tailTrace_3703855 : CollatzResearch.WordTrace tailWord_3703855 prefixEnd_3703855 1267905259705807589319191 := by
  unfold tailWord_3703855
  simp only [CollatzResearch.WordTrace]
  refine ⟨135090689996573377917793019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90060459997715585278528679 135090689996573377917793019)
  ·
    refine ⟨202636034994860066876689529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135090689996573377917793019 202636034994860066876689529)
    ·
      refine ⟨151977026246145050157517147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202636034994860066876689529 151977026246145050157517147)
      ·
        refine ⟨227965539369217575236275721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151977026246145050157517147 227965539369217575236275721)
        ·
          refine ⟨170974154526913181427206791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227965539369217575236275721 170974154526913181427206791)
          ·
            refine ⟨256461231790369772140810187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170974154526913181427206791 256461231790369772140810187)
            ·
              refine ⟨384691847685554658211215281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256461231790369772140810187 384691847685554658211215281)
              ·
                refine ⟨288518885764165993658411461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384691847685554658211215281 288518885764165993658411461)
                ·
                  refine ⟨54097291080781123810952149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288518885764165993658411461 54097291080781123810952149)
                  ·
                    refine ⟨1267905259705807589319191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54097291080781123810952149 1267905259705807589319191)
                    ·
                      rfl

theorem cell22_3703855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_3703855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703855 prefixEnd_3703855 := by exact prefixLift 3703855
  have htrace : WordTrace (prefixWord ++ tailWord_3703855) baseStart_3703855 baseEnd_3703855 := by
    simpa [prefixWord, tailWord_3703855, baseEnd_3703855] using wordTrace_append hprefix tailTrace_3703855
  have hstable : (prefixWord ++ tailWord_3703855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703855).length < 2 ^ (prefixWord ++ tailWord_3703855).sum := by decide
  have hdescent : baseEnd_3703855 < baseStart_3703855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3703878 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3703878 : Nat := 118140960795 + 3703878 * 2 ^ 59
def prefixEnd_3703878 : Nat := 4983230072969 + 3 ^ 40 * 3703878 * 2
def baseEnd_3703878 : Nat := 1267913133075843195994121

theorem tailTrace_3703878 : CollatzResearch.WordTrace tailWord_3703878 prefixEnd_3703878 1267913133075843195994121 := by
  unfold tailWord_3703878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221610277359064151433759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90061019250326701897253525 4221610277359064151433759)
  ·
    refine ⟨6332415416038596227150639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4221610277359064151433759 6332415416038596227150639)
    ·
      refine ⟨9498623124057894340725959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332415416038596227150639 9498623124057894340725959)
      ·
        refine ⟨14247934686086841511088939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9498623124057894340725959 14247934686086841511088939)
        ·
          refine ⟨21371902029130262266633409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14247934686086841511088939 21371902029130262266633409)
          ·
            refine ⟨16028926521847696699975057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21371902029130262266633409 16028926521847696699975057)
            ·
              refine ⟨12021694891385772524981293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16028926521847696699975057 12021694891385772524981293)
              ·
                refine ⟨4508135584269664696867985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12021694891385772524981293 4508135584269664696867985)
                ·
                  refine ⟨3381101688202248522650989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508135584269664696867985 3381101688202248522650989)
                  ·
                    refine ⟨1267913133075843195994121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381101688202248522650989 1267913133075843195994121)
                    ·
                      rfl

theorem cell22_3703878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3703878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3703878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3703878 prefixEnd_3703878 := by exact prefixLift 3703878
  have htrace : WordTrace (prefixWord ++ tailWord_3703878) baseStart_3703878 baseEnd_3703878 := by
    simpa [prefixWord, tailWord_3703878, baseEnd_3703878] using wordTrace_append hprefix tailTrace_3703878
  have hstable : (prefixWord ++ tailWord_3703878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3703878).length < 2 ^ (prefixWord ++ tailWord_3703878).sum := by decide
  have hdescent : baseEnd_3703878 < baseStart_3703878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3703878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704007 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3704007 : Nat := 118140960795 + 3704007 * 2 ^ 59
def prefixEnd_3704007 : Nat := 4983230072969 + 3 ^ 40 * 3704007 * 2
def baseEnd_3704007 : Nat := 1267957292412129859518725

theorem tailTrace_3704007 : CollatzResearch.WordTrace tailWord_3704007 prefixEnd_3704007 1267957292412129859518725 := by
  unfold tailWord_3704007
  simp only [CollatzResearch.WordTrace]
  refine ⟨135096233892022707877326275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90064155928015138584884183 135096233892022707877326275)
  ·
    refine ⟨202644350838034061815989413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135096233892022707877326275 202644350838034061815989413)
    ·
      refine ⟨37995815782131386590498015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202644350838034061815989413 37995815782131386590498015)
      ·
        refine ⟨56993723673197079885747023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37995815782131386590498015 56993723673197079885747023)
        ·
          refine ⟨85490585509795619828620535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56993723673197079885747023 85490585509795619828620535)
          ·
            refine ⟨128235878264693429742930803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85490585509795619828620535 128235878264693429742930803)
            ·
              refine ⟨192353817397040144614396205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128235878264693429742930803 192353817397040144614396205)
              ·
                refine ⟨72132681523890054230398577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192353817397040144614396205 72132681523890054230398577)
                ·
                  refine ⟨54099511142917540672798933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72132681523890054230398577 54099511142917540672798933)
                  ·
                    refine ⟨1267957292412129859518725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54099511142917540672798933 1267957292412129859518725)
                    ·
                      rfl

theorem cell22_3704007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3704007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704007 prefixEnd_3704007 := by exact prefixLift 3704007
  have htrace : WordTrace (prefixWord ++ tailWord_3704007) baseStart_3704007 baseEnd_3704007 := by
    simpa [prefixWord, tailWord_3704007, baseEnd_3704007] using wordTrace_append hprefix tailTrace_3704007
  have hstable : (prefixWord ++ tailWord_3704007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704007).length < 2 ^ (prefixWord ++ tailWord_3704007).sum := by decide
  have hdescent : baseEnd_3704007 < baseStart_3704007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704054 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_3704054 : Nat := 118140960795 + 3704054 * 2 ^ 59
def prefixEnd_3704054 : Nat := 4983230072969 + 3 ^ 40 * 3704054 * 2
def baseEnd_3704054 : Nat := 422657793824212467864527

theorem tailTrace_3704054 : CollatzResearch.WordTrace tailWord_3704054 prefixEnd_3704054 422657793824212467864527 := by
  unfold tailWord_3704054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443621757678277181517951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90065298748568289936191477 8443621757678277181517951)
  ·
    refine ⟨12665432636517415772276927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443621757678277181517951 12665432636517415772276927)
    ·
      refine ⟨18998148954776123658415391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12665432636517415772276927 18998148954776123658415391)
      ·
        refine ⟨28497223432164185487623087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18998148954776123658415391 28497223432164185487623087)
        ·
          refine ⟨42745835148246278231434631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28497223432164185487623087 42745835148246278231434631)
          ·
            refine ⟨64118752722369417347151947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42745835148246278231434631 64118752722369417347151947)
            ·
              refine ⟨96178129083554126020727921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64118752722369417347151947 96178129083554126020727921)
              ·
                refine ⟨72133596812665594515545941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96178129083554126020727921 72133596812665594515545941)
                ·
                  refine ⟨422657793824212467864527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72133596812665594515545941 422657793824212467864527)
                  ·
                    rfl

theorem cell22_3704054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_3704054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704054 prefixEnd_3704054 := by exact prefixLift 3704054
  have htrace : WordTrace (prefixWord ++ tailWord_3704054) baseStart_3704054 baseEnd_3704054 := by
    simpa [prefixWord, tailWord_3704054, baseEnd_3704054] using wordTrace_append hprefix tailTrace_3704054
  have hstable : (prefixWord ++ tailWord_3704054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704054).length < 2 ^ (prefixWord ++ tailWord_3704054).sum := by decide
  have hdescent : baseEnd_3704054 < baseStart_3704054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704099 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 6]
def baseStart_3704099 : Nat := 118140960795 + 3704099 * 2 ^ 59
def prefixEnd_3704099 : Nat := 4983230072969 + 3 ^ 40 * 3704099 * 2
def baseEnd_3704099 : Nat := 422662928630757428739481

theorem tailTrace_3704099 : CollatzResearch.WordTrace tailWord_3704099 prefixEnd_3704099 422662928630757428739481 := by
  unfold tailWord_3704099
  simp only [CollatzResearch.WordTrace]
  refine ⟨135099589407689407589675351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90066392938459605059783567 135099589407689407589675351)
  ·
    refine ⟨202649384111534111384513027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135099589407689407589675351 202649384111534111384513027)
    ·
      refine ⟨303974076167301167076769541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202649384111534111384513027 303974076167301167076769541)
      ·
        refine ⟨56995139281368968826894289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303974076167301167076769541 56995139281368968826894289)
        ·
          refine ⟨42746354461026726620170717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56995139281368968826894289 42746354461026726620170717)
          ·
            refine ⟨16029882922885022482564019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42746354461026726620170717 16029882922885022482564019)
            ·
              refine ⟨24044824384327533723846029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16029882922885022482564019 24044824384327533723846029)
              ·
                refine ⟨9016809144122825146442261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24044824384327533723846029 9016809144122825146442261)
                ·
                  refine ⟨422662928630757428739481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9016809144122825146442261 422662928630757428739481)
                  ·
                    rfl

theorem cell22_3704099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_3704099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704099 prefixEnd_3704099 := by exact prefixLift 3704099
  have htrace : WordTrace (prefixWord ++ tailWord_3704099) baseStart_3704099 baseEnd_3704099 := by
    simpa [prefixWord, tailWord_3704099, baseEnd_3704099] using wordTrace_append hprefix tailTrace_3704099
  have hstable : (prefixWord ++ tailWord_3704099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704099).length < 2 ^ (prefixWord ++ tailWord_3704099).sum := by decide
  have hdescent : baseEnd_3704099 < baseStart_3704099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704116 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3704116 : Nat := 118140960795 + 3704116 * 2 ^ 59
def prefixEnd_3704116 : Nat := 4983230072969 + 3 ^ 40 * 3704116 * 2
def baseEnd_3704116 : Nat := 422664868446563302847797

theorem tailTrace_3704116 : CollatzResearch.WordTrace tailWord_3704116 prefixEnd_3704116 422664868446563302847797 := by
  unfold tailWord_3704116
  simp only [CollatzResearch.WordTrace]
  refine ⟨67550104724313909746522101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90066806299085212995362801 67550104724313909746522101)
  ·
    refine ⟨6332822317904429038736447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67550104724313909746522101 6332822317904429038736447)
    ·
      refine ⟨9499233476856643558104671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332822317904429038736447 9499233476856643558104671)
      ·
        refine ⟨14248850215284965337157007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9499233476856643558104671 14248850215284965337157007)
        ·
          refine ⟨21373275322927448005735511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14248850215284965337157007 21373275322927448005735511)
          ·
            refine ⟨32059912984391172008603267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21373275322927448005735511 32059912984391172008603267)
            ·
              refine ⟨48089869476586758012904901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32059912984391172008603267 48089869476586758012904901)
              ·
                refine ⟨9016850526860017127419669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48089869476586758012904901 9016850526860017127419669)
                ·
                  refine ⟨422664868446563302847797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9016850526860017127419669 422664868446563302847797)
                  ·
                    rfl

theorem cell22_3704116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3704116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704116 prefixEnd_3704116 := by exact prefixLift 3704116
  have htrace : WordTrace (prefixWord ++ tailWord_3704116) baseStart_3704116 baseEnd_3704116 := by
    simpa [prefixWord, tailWord_3704116, baseEnd_3704116] using wordTrace_append hprefix tailTrace_3704116
  have hstable : (prefixWord ++ tailWord_3704116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704116).length < 2 ^ (prefixWord ++ tailWord_3704116).sum := by decide
  have hdescent : baseEnd_3704116 < baseStart_3704116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704148 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3704148 : Nat := 118140960795 + 3704148 * 2 ^ 59
def prefixEnd_3704148 : Nat := 4983230072969 + 3 ^ 40 * 3704148 * 2
def baseEnd_3704148 : Nat := 1268005559593652491743293

theorem tailTrace_3704148 : CollatzResearch.WordTrace tailWord_3704148 prefixEnd_3704148 1268005559593652491743293 := by
  unfold tailWord_3704148
  simp only [CollatzResearch.WordTrace]
  refine ⟨67550688292255944479104549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90067584389674592638806065 67550688292255944479104549)
  ·
    refine ⟨12665754054797989589832103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67550688292255944479104549 12665754054797989589832103)
    ·
      refine ⟨18998631082196984384748155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12665754054797989589832103 18998631082196984384748155)
      ·
        refine ⟨28497946623295476577122233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18998631082196984384748155 28497946623295476577122233)
        ·
          refine ⟨21373459967471607432841675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28497946623295476577122233 21373459967471607432841675)
          ·
            refine ⟨32060189951207411149262513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21373459967471607432841675 32060189951207411149262513)
            ·
              refine ⟨24045142463405558361946885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32060189951207411149262513 24045142463405558361946885)
              ·
                refine ⟨4508464211888542192865041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24045142463405558361946885 4508464211888542192865041)
                ·
                  refine ⟨3381348158916406644648781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508464211888542192865041 3381348158916406644648781)
                  ·
                    refine ⟨1268005559593652491743293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381348158916406644648781 1268005559593652491743293)
                    ·
                      rfl

theorem cell22_3704148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3704148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704148 prefixEnd_3704148 := by exact prefixLift 3704148
  have htrace : WordTrace (prefixWord ++ tailWord_3704148) baseStart_3704148 baseEnd_3704148 := by
    simpa [prefixWord, tailWord_3704148, baseEnd_3704148] using wordTrace_append hprefix tailTrace_3704148
  have hstable : (prefixWord ++ tailWord_3704148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704148).length < 2 ^ (prefixWord ++ tailWord_3704148).sum := by decide
  have hdescent : baseEnd_3704148 < baseStart_3704148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704176 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_3704176 : Nat := 118140960795 + 3704176 * 2 ^ 59
def prefixEnd_3704176 : Nat := 4983230072969 + 3 ^ 40 * 3704176 * 2
def baseEnd_3704176 : Nat := 1268015144565869752043207

theorem tailTrace_3704176 : CollatzResearch.WordTrace tailWord_3704176 prefixEnd_3704176 1268015144565869752043207 := by
  unfold tailWord_3704176
  simp only [CollatzResearch.WordTrace]
  refine ⟨67551198914205224870114191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90068265218940299826818921 67551198914205224870114191)
  ·
    refine ⟨101326798371307837305171287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67551198914205224870114191 101326798371307837305171287)
    ·
      refine ⟨151990197556961755957756931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101326798371307837305171287 151990197556961755957756931)
      ·
        refine ⟨227985296335442633936635397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151990197556961755957756931 227985296335442633936635397)
        ·
          refine ⟨42747243062895493863119137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227985296335442633936635397 42747243062895493863119137)
          ·
            refine ⟨32060432297171620397339353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42747243062895493863119137 32060432297171620397339353)
            ·
              refine ⟨24045324222878715298004515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32060432297171620397339353 24045324222878715298004515)
              ·
                refine ⟨36067986334318072947006773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045324222878715298004515 36067986334318072947006773)
                ·
                  refine ⟨3381373718842319338781885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36067986334318072947006773 3381373718842319338781885)
                  ·
                    refine ⟨1268015144565869752043207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381373718842319338781885 1268015144565869752043207)
                    ·
                      rfl

theorem cell22_3704176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_3704176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704176 prefixEnd_3704176 := by exact prefixLift 3704176
  have htrace : WordTrace (prefixWord ++ tailWord_3704176) baseStart_3704176 baseEnd_3704176 := by
    simpa [prefixWord, tailWord_3704176, baseEnd_3704176] using wordTrace_append hprefix tailTrace_3704176
  have hstable : (prefixWord ++ tailWord_3704176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704176).length < 2 ^ (prefixWord ++ tailWord_3704176).sum := by decide
  have hdescent : baseEnd_3704176 < baseStart_3704176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704221 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3704221 : Nat := 118140960795 + 3704221 * 2 ^ 59
def prefixEnd_3704221 : Nat := 4983230072969 + 3 ^ 40 * 3704221 * 2
def baseEnd_3704221 : Nat := 1268030548985504634668069

theorem tailTrace_3704221 : CollatzResearch.WordTrace tailWord_3704221 prefixEnd_3704221 1268030548985504634668069 := by
  unfold tailWord_3704221
  simp only [CollatzResearch.WordTrace]
  refine ⟨135104039113247422425616517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90069359408831614950411011 135104039113247422425616517)
  ·
    refine ⟨25332007333733891704803097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135104039113247422425616517 25332007333733891704803097)
    ·
      refine ⟨18999005500300418778602323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25332007333733891704803097 18999005500300418778602323)
      ·
        refine ⟨28498508250450628167903485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18999005500300418778602323 28498508250450628167903485)
        ·
          refine ⟨10686940593918985562963807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28498508250450628167903485 10686940593918985562963807)
          ·
            refine ⟨16030410890878478344445711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10686940593918985562963807 16030410890878478344445711)
            ·
              refine ⟨24045616336317717516668567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030410890878478344445711 24045616336317717516668567)
              ·
                refine ⟨36068424504476576275002851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045616336317717516668567 36068424504476576275002851)
                ·
                  refine ⟨54102636756714864412504277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36068424504476576275002851 54102636756714864412504277)
                  ·
                    refine ⟨1268030548985504634668069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54102636756714864412504277 1268030548985504634668069)
                    ·
                      rfl

theorem cell22_3704221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3704221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704221 prefixEnd_3704221 := by exact prefixLift 3704221
  have htrace : WordTrace (prefixWord ++ tailWord_3704221) baseStart_3704221 baseEnd_3704221 := by
    simpa [prefixWord, tailWord_3704221, baseEnd_3704221] using wordTrace_append hprefix tailTrace_3704221
  have hstable : (prefixWord ++ tailWord_3704221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704221).length < 2 ^ (prefixWord ++ tailWord_3704221).sum := by decide
  have hdescent : baseEnd_3704221 < baseStart_3704221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704236 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_3704236 : Nat := 118140960795 + 3704236 * 2 ^ 59
def prefixEnd_3704236 : Nat := 4983230072969 + 3 ^ 40 * 3704236 * 2
def baseEnd_3704236 : Nat := 1268035683792049595543023

theorem tailTrace_3704236 : CollatzResearch.WordTrace tailWord_3704236 prefixEnd_3704236 1268035683792049595543023 := by
  unfold tailWord_3704236
  simp only [CollatzResearch.WordTrace]
  refine ⟨67552293104096539993706281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90069724138795386658275041 67552293104096539993706281)
  ·
    refine ⟨50664219828072404995279711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67552293104096539993706281 50664219828072404995279711)
    ·
      refine ⟨75996329742108607492919567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50664219828072404995279711 75996329742108607492919567)
      ·
        refine ⟨113994494613162911239379351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75996329742108607492919567 113994494613162911239379351)
        ·
          refine ⟨170991741919744366859069027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113994494613162911239379351 170991741919744366859069027)
          ·
            refine ⟨256487612879616550288603541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170991741919744366859069027 256487612879616550288603541)
            ·
              refine ⟨12022856853732025794778291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256487612879616550288603541 12022856853732025794778291)
              ·
                refine ⟨18034285280598038692167437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12022856853732025794778291 18034285280598038692167437)
                ·
                  refine ⟨6762856980224264509562789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18034285280598038692167437 6762856980224264509562789)
                  ·
                    refine ⟨1268035683792049595543023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762856980224264509562789 1268035683792049595543023)
                    ·
                      rfl

theorem cell22_3704236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_3704236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704236 prefixEnd_3704236 := by exact prefixLift 3704236
  have htrace : WordTrace (prefixWord ++ tailWord_3704236) baseStart_3704236 baseEnd_3704236 := by
    simpa [prefixWord, tailWord_3704236, baseEnd_3704236] using wordTrace_append hprefix tailTrace_3704236
  have hstable : (prefixWord ++ tailWord_3704236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704236).length < 2 ^ (prefixWord ++ tailWord_3704236).sum := by decide
  have hdescent : baseEnd_3704236 < baseStart_3704236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704253 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3704253 : Nat := 118140960795 + 3704253 * 2 ^ 59
def prefixEnd_3704253 : Nat := 4983230072969 + 3 ^ 40 * 3704253 * 2
def baseEnd_3704253 : Nat := 1268041503239467217867971

theorem tailTrace_3704253 : CollatzResearch.WordTrace tailWord_3704253 prefixEnd_3704253 1268041503239467217867971 := by
  unfold tailWord_3704253
  simp only [CollatzResearch.WordTrace]
  refine ⟨135105206249131491890781413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90070137499420994593854275 135105206249131491890781413)
  ·
    refine ⟨25332226171712154729521515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135105206249131491890781413 25332226171712154729521515)
    ·
      refine ⟨37998339257568232094282273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25332226171712154729521515 37998339257568232094282273)
      ·
        refine ⟨28498754443176174070711705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37998339257568232094282273 28498754443176174070711705)
        ·
          refine ⟨21374065832382130553033779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28498754443176174070711705 21374065832382130553033779)
          ·
            refine ⟨32061098748573195829550669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21374065832382130553033779 32061098748573195829550669)
            ·
              refine ⟨12022912030714948436081501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32061098748573195829550669 12022912030714948436081501)
              ·
                refine ⟨4508592011518105663530563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12022912030714948436081501 4508592011518105663530563)
                ·
                  refine ⟨6762888017277158495295845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508592011518105663530563 6762888017277158495295845)
                  ·
                    refine ⟨1268041503239467217867971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762888017277158495295845 1268041503239467217867971)
                    ·
                      rfl

theorem cell22_3704253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3704253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704253 prefixEnd_3704253 := by exact prefixLift 3704253
  have htrace : WordTrace (prefixWord ++ tailWord_3704253) baseStart_3704253 baseEnd_3704253 := by
    simpa [prefixWord, tailWord_3704253, baseEnd_3704253] using wordTrace_append hprefix tailTrace_3704253
  have hstable : (prefixWord ++ tailWord_3704253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704253).length < 2 ^ (prefixWord ++ tailWord_3704253).sum := by decide
  have hdescent : baseEnd_3704253 < baseStart_3704253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704268 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_3704268 : Nat := 118140960795 + 3704268 * 2 ^ 59
def prefixEnd_3704268 : Nat := 4983230072969 + 3 ^ 40 * 3704268 * 2
def baseEnd_3704268 : Nat := 422682212682004059580975

theorem tailTrace_3704268 : CollatzResearch.WordTrace tailWord_3704268 prefixEnd_3704268 422682212682004059580975 := by
  unfold tailWord_3704268
  simp only [CollatzResearch.WordTrace]
  refine ⟨67552876672038574726288729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90070502229384766301718305 67552876672038574726288729)
  ·
    refine ⟨50664657504028931044716547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67552876672038574726288729 50664657504028931044716547)
    ·
      refine ⟨75996986256043396567074821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50664657504028931044716547 75996986256043396567074821)
      ·
        refine ⟨14249434923008136856326529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75996986256043396567074821 14249434923008136856326529)
        ·
          refine ⟨10687076192256102642244897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14249434923008136856326529 10687076192256102642244897)
          ·
            refine ⟨8015307144192076981683673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10687076192256102642244897 8015307144192076981683673)
            ·
              refine ⟨6011480358144057736262755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8015307144192076981683673 6011480358144057736262755)
              ·
                refine ⟨9017220537216086604394133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011480358144057736262755 9017220537216086604394133)
                ·
                  refine ⟨422682212682004059580975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9017220537216086604394133 422682212682004059580975)
                  ·
                    rfl

theorem cell22_3704268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_3704268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704268 prefixEnd_3704268 := by exact prefixLift 3704268
  have htrace : WordTrace (prefixWord ++ tailWord_3704268) baseStart_3704268 baseEnd_3704268 := by
    simpa [prefixWord, tailWord_3704268, baseEnd_3704268] using wordTrace_append hprefix tailTrace_3704268
  have hstable : (prefixWord ++ tailWord_3704268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704268).length < 2 ^ (prefixWord ++ tailWord_3704268).sum := by decide
  have hdescent : baseEnd_3704268 < baseStart_3704268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704281 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_3704281 : Nat := 118140960795 + 3704281 * 2 ^ 59
def prefixEnd_3704281 : Nat := 4983230072969 + 3 ^ 40 * 3704281 * 2
def baseEnd_3704281 : Nat := 1268051088211684478167885

theorem tailTrace_3704281 : CollatzResearch.WordTrace tailWord_3704281 prefixEnd_3704281 1268051088211684478167885 := by
  unfold tailWord_3704281
  simp only [CollatzResearch.WordTrace]
  refine ⟨135106227493030052672800697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90070818328686701781867131 135106227493030052672800697)
  ·
    refine ⟨101329670619772539504600523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135106227493030052672800697 101329670619772539504600523)
    ·
      refine ⟨151994505929658809256900785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101329670619772539504600523 151994505929658809256900785)
      ·
        refine ⟨113995879447244106942675589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151994505929658809256900785 113995879447244106942675589)
        ·
          refine ⟨21374227396358270051751673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113995879447244106942675589 21374227396358270051751673)
          ·
            refine ⟨16030670547268702538813755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21374227396358270051751673 16030670547268702538813755)
            ·
              refine ⟨24046005820903053808220633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030670547268702538813755 24046005820903053808220633)
              ·
                refine ⟨18034504365677290356165475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24046005820903053808220633 18034504365677290356165475)
                ·
                  refine ⟨27051756548515935534248213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18034504365677290356165475 27051756548515935534248213)
                  ·
                    refine ⟨1268051088211684478167885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27051756548515935534248213 1268051088211684478167885)
                    ·
                      rfl

theorem cell22_3704281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_3704281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704281 prefixEnd_3704281 := by exact prefixLift 3704281
  have htrace : WordTrace (prefixWord ++ tailWord_3704281) baseStart_3704281 baseEnd_3704281 := by
    simpa [prefixWord, tailWord_3704281, baseEnd_3704281] using wordTrace_append hprefix tailTrace_3704281
  have hstable : (prefixWord ++ tailWord_3704281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704281).length < 2 ^ (prefixWord ++ tailWord_3704281).sum := by decide
  have hdescent : baseEnd_3704281 < baseStart_3704281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704296 : List Nat := [2, 1, 4, 1, 1, 2, 3, 8]
def baseStart_3704296 : Nat := 118140960795 + 3704296 * 2 ^ 59
def prefixEnd_3704296 : Nat := 4983230072969 + 3 ^ 40 * 3704296 * 2
def baseEnd_3704296 : Nat := 140895135890914382115871

theorem tailTrace_3704296 : CollatzResearch.WordTrace tailWord_3704296 prefixEnd_3704296 140895135890914382115871 := by
  unfold tailWord_3704296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67553387293987855117298371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90071183058650473489731161 67553387293987855117298371)
  ·
    refine ⟨101330080940981782675947557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67553387293987855117298371 101330080940981782675947557)
    ·
      refine ⟨18999390176434084251740167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101330080940981782675947557 18999390176434084251740167)
      ·
        refine ⟨28499085264651126377610251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18999390176434084251740167 28499085264651126377610251)
        ·
          refine ⟨42748627896976689566415377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28499085264651126377610251 42748627896976689566415377)
          ·
            refine ⟨32061470922732517174811533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42748627896976689566415377 32061470922732517174811533)
            ·
              refine ⟨12023051596024693940554325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32061470922732517174811533 12023051596024693940554325)
              ·
                refine ⟨140895135890914382115871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12023051596024693940554325 140895135890914382115871)
                ·
                  rfl

theorem cell22_3704296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_3704296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704296 prefixEnd_3704296 := by exact prefixLift 3704296
  have htrace : WordTrace (prefixWord ++ tailWord_3704296) baseStart_3704296 baseEnd_3704296 := by
    simpa [prefixWord, tailWord_3704296, baseEnd_3704296] using wordTrace_append hprefix tailTrace_3704296
  have hstable : (prefixWord ++ tailWord_3704296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704296).length < 2 ^ (prefixWord ++ tailWord_3704296).sum := by decide
  have hdescent : baseEnd_3704296 < baseStart_3704296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704334 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_3704334 : Nat := 118140960795 + 3704334 * 2 ^ 59
def prefixEnd_3704334 : Nat := 4983230072969 + 3 ^ 40 * 3704334 * 2
def baseEnd_3704334 : Nat := 1268069231194810006592723

theorem tailTrace_3704334 : CollatzResearch.WordTrace tailWord_3704334 prefixEnd_3704334 1268069231194810006592723 := by
  unfold tailWord_3704334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888520070229755340560007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90072107041225361816320037 16888520070229755340560007)
  ·
    refine ⟨25332780105344633010840011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16888520070229755340560007 25332780105344633010840011)
    ·
      refine ⟨37999170158016949516260017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25332780105344633010840011 37999170158016949516260017)
      ·
        refine ⟨28499377618512712137195013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37999170158016949516260017 28499377618512712137195013)
        ·
          refine ⟨5343633303471133525724065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28499377618512712137195013 5343633303471133525724065)
          ·
            refine ⟨4007724977603350144293049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5343633303471133525724065 4007724977603350144293049)
            ·
              refine ⟨3005793733202512608219787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4007724977603350144293049 3005793733202512608219787)
              ·
                refine ⟨4508690599803768912329681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005793733202512608219787 4508690599803768912329681)
                ·
                  refine ⟨3381517949852826684247261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508690599803768912329681 3381517949852826684247261)
                  ·
                    refine ⟨1268069231194810006592723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381517949852826684247261 1268069231194810006592723)
                    ·
                      rfl

theorem cell22_3704334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_3704334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704334 prefixEnd_3704334 := by exact prefixLift 3704334
  have htrace : WordTrace (prefixWord ++ tailWord_3704334) baseStart_3704334 baseEnd_3704334 := by
    simpa [prefixWord, tailWord_3704334, baseEnd_3704334] using wordTrace_append hprefix tailTrace_3704334
  have hstable : (prefixWord ++ tailWord_3704334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704334).length < 2 ^ (prefixWord ++ tailWord_3704334).sum := by decide
  have hdescent : baseEnd_3704334 < baseStart_3704334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704362 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3704362 : Nat := 118140960795 + 3704362 * 2 ^ 59
def prefixEnd_3704362 : Nat := 4983230072969 + 3 ^ 40 * 3704362 * 2
def baseEnd_3704362 : Nat := 1268078816167027266892637

theorem tailTrace_3704362 : CollatzResearch.WordTrace tailWord_3704362 prefixEnd_3704362 1268078816167027266892637 := by
  unfold tailWord_3704362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33777295451434150876624835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90072787870491069004332893 33777295451434150876624835)
  ·
    refine ⟨50665943177151226314937253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33777295451434150876624835 50665943177151226314937253)
    ·
      refine ⟨9499864345715854934050735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50665943177151226314937253 9499864345715854934050735)
      ·
        refine ⟨14249796518573782401076103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9499864345715854934050735 14249796518573782401076103)
        ·
          refine ⟨21374694777860673601614155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14249796518573782401076103 21374694777860673601614155)
          ·
            refine ⟨32062042166791010402421233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21374694777860673601614155 32062042166791010402421233)
            ·
              refine ⟨24046531625093257801815925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32062042166791010402421233 24046531625093257801815925)
              ·
                refine ⟨2254362339852492918920243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24046531625093257801815925 2254362339852492918920243)
                ·
                  refine ⟨3381543509778739378380365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254362339852492918920243 3381543509778739378380365)
                  ·
                    refine ⟨1268078816167027266892637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381543509778739378380365 1268078816167027266892637)
                    ·
                      rfl

theorem cell22_3704362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3704362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704362 prefixEnd_3704362 := by exact prefixLift 3704362
  have htrace : WordTrace (prefixWord ++ tailWord_3704362) baseStart_3704362 baseEnd_3704362 := by
    simpa [prefixWord, tailWord_3704362, baseEnd_3704362] using wordTrace_append hprefix tailTrace_3704362
  have hstable : (prefixWord ++ tailWord_3704362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704362).length < 2 ^ (prefixWord ++ tailWord_3704362).sum := by decide
  have hdescent : baseEnd_3704362 < baseStart_3704362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704420 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 4]
def baseStart_3704420 : Nat := 118140960795 + 3704420 * 2 ^ 59
def prefixEnd_3704420 : Nat := 4983230072969 + 3 ^ 40 * 3704420 * 2
def baseEnd_3704420 : Nat := 422699556917444816314153

theorem tailTrace_3704420 : CollatzResearch.WordTrace tailWord_3704420 prefixEnd_3704420 422699556917444816314153 := by
  unfold tailWord_3704420
  simp only [CollatzResearch.WordTrace]
  refine ⟨67555648619763239706055357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90074198159684319608073809 67555648619763239706055357)
  ·
    refine ⟨25333368232411214889770759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67555648619763239706055357 25333368232411214889770759)
    ·
      refine ⟨38000052348616822334656139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25333368232411214889770759 38000052348616822334656139)
      ·
        refine ⟨57000078522925233501984209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38000052348616822334656139 57000078522925233501984209)
        ·
          refine ⟨42750058892193925126488157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57000078522925233501984209 42750058892193925126488157)
          ·
            refine ⟨16031272084572721922433059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42750058892193925126488157 16031272084572721922433059)
            ·
              refine ⟨24046908126859082883649589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16031272084572721922433059 24046908126859082883649589)
              ·
                refine ⟨2254397636893039020342149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24046908126859082883649589 2254397636893039020342149)
                ·
                  refine ⟨422699556917444816314153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254397636893039020342149 422699556917444816314153)
                  ·
                    rfl

theorem cell22_3704420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_3704420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704420 prefixEnd_3704420 := by exact prefixLift 3704420
  have htrace : WordTrace (prefixWord ++ tailWord_3704420) baseStart_3704420 baseEnd_3704420 := by
    simpa [prefixWord, tailWord_3704420, baseEnd_3704420] using wordTrace_append hprefix tailTrace_3704420
  have hstable : (prefixWord ++ tailWord_3704420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704420).length < 2 ^ (prefixWord ++ tailWord_3704420).sum := by decide
  have hdescent : baseEnd_3704420 < baseStart_3704420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704433 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3704433 : Nat := 118140960795 + 3704433 * 2 ^ 59
def prefixEnd_3704433 : Nat := 4983230072969 + 3 ^ 40 * 3704433 * 2
def baseEnd_3704433 : Nat := 1268103120918006748367419

theorem tailTrace_3704433 : CollatzResearch.WordTrace tailWord_3704433 prefixEnd_3704433 1268103120918006748367419 := by
  unfold tailWord_3704433
  simp only [CollatzResearch.WordTrace]
  refine ⟨135111771388479382632333953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90074514258986255088222635 135111771388479382632333953)
  ·
    refine ⟨101333828541359536974250465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135111771388479382632333953 101333828541359536974250465)
    ·
      refine ⟨76000371406019652730687849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101333828541359536974250465 76000371406019652730687849)
      ·
        refine ⟨57000278554514739548015887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76000371406019652730687849 57000278554514739548015887)
        ·
          refine ⟨85500417831772109322023831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57000278554514739548015887 85500417831772109322023831)
          ·
            refine ⟨128250626747658163983035747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85500417831772109322023831 128250626747658163983035747)
            ·
              refine ⟨192375940121487245974553621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128250626747658163983035747 192375940121487245974553621)
              ·
                refine ⟨9017622193194714655057201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192375940121487245974553621 9017622193194714655057201)
                ·
                  refine ⟨6763216644896035991292901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9017622193194714655057201 6763216644896035991292901)
                  ·
                    refine ⟨1268103120918006748367419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6763216644896035991292901 1268103120918006748367419)
                    ·
                      rfl

theorem cell22_3704433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3704433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704433 prefixEnd_3704433 := by exact prefixLift 3704433
  have htrace : WordTrace (prefixWord ++ tailWord_3704433) baseStart_3704433 baseEnd_3704433 := by
    simpa [prefixWord, tailWord_3704433, baseEnd_3704433] using wordTrace_append hprefix tailTrace_3704433
  have hstable : (prefixWord ++ tailWord_3704433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704433).length < 2 ^ (prefixWord ++ tailWord_3704433).sum := by decide
  have hdescent : baseEnd_3704433 < baseStart_3704433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704437 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 4]
def baseStart_3704437 : Nat := 118140960795 + 3704437 * 2 ^ 59
def prefixEnd_3704437 : Nat := 4983230072969 + 3 ^ 40 * 3704437 * 2
def baseEnd_3704437 : Nat := 422701496733250690422469

theorem tailTrace_3704437 : CollatzResearch.WordTrace tailWord_3704437 prefixEnd_3704437 422701496733250690422469 := by
  unfold tailWord_3704437
  simp only [CollatzResearch.WordTrace]
  refine ⟨135111917280464891315479565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90074611520309927543653043 135111917280464891315479565)
  ·
    refine ⟨50666968980174334243304837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135111917280464891315479565 50666968980174334243304837)
    ·
      refine ⟨9500056683782687670619657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50666968980174334243304837 9500056683782687670619657)
      ·
        refine ⟨7125042512837015752964743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9500056683782687670619657 7125042512837015752964743)
        ·
          refine ⟨10687563769255523629447115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7125042512837015752964743 10687563769255523629447115)
          ·
            refine ⟨16031345653883285444170673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10687563769255523629447115 16031345653883285444170673)
            ·
              refine ⟨12023509240412464083128005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16031345653883285444170673 12023509240412464083128005)
              ·
                refine ⟨2254407982577337015586501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12023509240412464083128005 2254407982577337015586501)
                ·
                  refine ⟨422701496733250690422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254407982577337015586501 422701496733250690422469)
                  ·
                    rfl

theorem cell22_3704437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_3704437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704437 prefixEnd_3704437 := by exact prefixLift 3704437
  have htrace : WordTrace (prefixWord ++ tailWord_3704437) baseStart_3704437 baseEnd_3704437 := by
    simpa [prefixWord, tailWord_3704437, baseEnd_3704437] using wordTrace_append hprefix tailTrace_3704437
  have hstable : (prefixWord ++ tailWord_3704437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704437).length < 2 ^ (prefixWord ++ tailWord_3704437).sum := by decide
  have hdescent : baseEnd_3704437 < baseStart_3704437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704452 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3704452 : Nat := 118140960795 + 3704452 * 2 ^ 59
def prefixEnd_3704452 : Nat := 4983230072969 + 3 ^ 40 * 3704452 * 2
def baseEnd_3704452 : Nat := 1268109625006297032142361

theorem tailTrace_3704452 : CollatzResearch.WordTrace tailWord_3704452 prefixEnd_3704452 1268109625006297032142361 := by
  unfold tailWord_3704452
  simp only [CollatzResearch.WordTrace]
  refine ⟨67556232187705274438637805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90074976250273699251517073 67556232187705274438637805)
  ·
    refine ⟨25333587070389477914489177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67556232187705274438637805 25333587070389477914489177)
    ·
      refine ⟨19000190302792108435866883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25333587070389477914489177 19000190302792108435866883)
      ·
        refine ⟨28500285454188162653800325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19000190302792108435866883 28500285454188162653800325)
        ·
          refine ⟨5343803522660280497587561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28500285454188162653800325 5343803522660280497587561)
          ·
            refine ⟨4007852641995210373190671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5343803522660280497587561 4007852641995210373190671)
            ·
              refine ⟨6011778962992815559786007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007852641995210373190671 6011778962992815559786007)
              ·
                refine ⟨9017668444489223339679011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011778962992815559786007 9017668444489223339679011)
                ·
                  refine ⟨13526502666733835009518517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9017668444489223339679011 13526502666733835009518517)
                  ·
                    refine ⟨1268109625006297032142361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13526502666733835009518517 1268109625006297032142361)
                    ·
                      rfl

theorem cell22_3704452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3704452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704452 prefixEnd_3704452 := by exact prefixLift 3704452
  have htrace : WordTrace (prefixWord ++ tailWord_3704452) baseStart_3704452 baseEnd_3704452 := by
    simpa [prefixWord, tailWord_3704452, baseEnd_3704452] using wordTrace_append hprefix tailTrace_3704452
  have hstable : (prefixWord ++ tailWord_3704452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704452).length < 2 ^ (prefixWord ++ tailWord_3704452).sum := by decide
  have hdescent : baseEnd_3704452 < baseStart_3704452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704482 : List Nat := [3, 3, 1, 4, 1, 2, 8]
def baseStart_3704482 : Nat := 118140960795 + 3704482 * 2 ^ 59
def prefixEnd_3704482 : Nat := 4983230072969 + 3 ^ 40 * 3704482 * 2
def baseEnd_3704482 : Nat := 46967403504421739033047

theorem tailTrace_3704482 : CollatzResearch.WordTrace tailWord_3704482 prefixEnd_3704482 46967403504421739033047 := by
  unfold tailWord_3704482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33778389641325466000216925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90075705710201242667245133 33778389641325466000216925)
  ·
    refine ⟨12666896115497049750081347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33778389641325466000216925 12666896115497049750081347)
    ·
      refine ⟨19000344173245574625122021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12666896115497049750081347 19000344173245574625122021)
      ·
        refine ⟨3562564532483545242210379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19000344173245574625122021 3562564532483545242210379)
        ·
          refine ⟨5343846798725317863315569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562564532483545242210379 5343846798725317863315569)
          ·
            refine ⟨4007885099043988397486677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5343846798725317863315569 4007885099043988397486677)
            ·
              refine ⟨46967403504421739033047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4007885099043988397486677 46967403504421739033047)
              ·
                rfl

theorem cell22_3704482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 8].length) (baseStart_3704482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704482 prefixEnd_3704482 := by exact prefixLift 3704482
  have htrace : WordTrace (prefixWord ++ tailWord_3704482) baseStart_3704482 baseEnd_3704482 := by
    simpa [prefixWord, tailWord_3704482, baseEnd_3704482] using wordTrace_append hprefix tailTrace_3704482
  have hstable : (prefixWord ++ tailWord_3704482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704482).length < 2 ^ (prefixWord ++ tailWord_3704482).sum := by decide
  have hdescent : baseEnd_3704482 < baseStart_3704482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704488 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 4]
def baseStart_3704488 : Nat := 118140960795 + 3704488 * 2 ^ 59
def prefixEnd_3704488 : Nat := 4983230072969 + 3 ^ 40 * 3704488 * 2
def baseEnd_3704488 : Nat := 422707316180668312747417

theorem tailTrace_3704488 : CollatzResearch.WordTrace tailWord_3704488 prefixEnd_3704488 422707316180668312747417 := by
  unfold tailWord_3704488
  simp only [CollatzResearch.WordTrace]
  refine ⟨67556888701640063512793059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90075851602186751350390745 67556888701640063512793059)
  ·
    refine ⟨101335333052460095269189589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67556888701640063512793059 101335333052460095269189589)
    ·
      refine ⟨2375046868417033482871631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101335333052460095269189589 2375046868417033482871631)
      ·
        refine ⟨3562570302625550224307447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375046868417033482871631 3562570302625550224307447)
        ·
          refine ⟨5343855453938325336461171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562570302625550224307447 5343855453938325336461171)
          ·
            refine ⟨8015783180907488004691757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343855453938325336461171 8015783180907488004691757)
            ·
              refine ⟨3005918692840308001759409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8015783180907488004691757 3005918692840308001759409)
              ·
                refine ⟨2254439019630231001319557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005918692840308001759409 2254439019630231001319557)
                ·
                  refine ⟨422707316180668312747417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254439019630231001319557 422707316180668312747417)
                  ·
                    rfl

theorem cell22_3704488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_3704488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704488 prefixEnd_3704488 := by exact prefixLift 3704488
  have htrace : WordTrace (prefixWord ++ tailWord_3704488) baseStart_3704488 baseEnd_3704488 := by
    simpa [prefixWord, tailWord_3704488, baseEnd_3704488] using wordTrace_append hprefix tailTrace_3704488
  have hstable : (prefixWord ++ tailWord_3704488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704488).length < 2 ^ (prefixWord ++ tailWord_3704488).sum := by decide
  have hdescent : baseEnd_3704488 < baseStart_3704488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704553 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_3704553 : Nat := 118140960795 + 3704553 * 2 ^ 59
def prefixEnd_3704553 : Nat := 4983230072969 + 3 ^ 40 * 3704553 * 2
def baseEnd_3704553 : Nat := 1268144199370366435367051

theorem tailTrace_3704553 : CollatzResearch.WordTrace tailWord_3704553 prefixEnd_3704553 1268144199370366435367051 := by
  unfold tailWord_3704553
  simp only [CollatzResearch.WordTrace]
  refine ⟨135116148148044643126702313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90077432098696428751134875 135116148148044643126702313)
  ·
    refine ⟨101337111111033482345026735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135116148148044643126702313 101337111111033482345026735)
    ·
      refine ⟨152005666666550223517540103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101337111111033482345026735 152005666666550223517540103)
      ·
        refine ⟨228008499999825335276310155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152005666666550223517540103 228008499999825335276310155)
        ·
          refine ⟨342012749999738002914465233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228008499999825335276310155 342012749999738002914465233)
          ·
            refine ⟨256509562499803502185848925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342012749999738002914465233 256509562499803502185848925)
            ·
              refine ⟨96191085937426313319693347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256509562499803502185848925 96191085937426313319693347)
              ·
                refine ⟨144286628906139469979540021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96191085937426313319693347 144286628906139469979540021)
                ·
                  refine ⟨13526871459950575310581877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144286628906139469979540021 13526871459950575310581877)
                  ·
                    refine ⟨1268144199370366435367051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13526871459950575310581877 1268144199370366435367051)
                    ·
                      rfl

theorem cell22_3704553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_3704553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704553 prefixEnd_3704553 := by exact prefixLift 3704553
  have htrace : WordTrace (prefixWord ++ tailWord_3704553) baseStart_3704553 baseEnd_3704553 := by
    simpa [prefixWord, tailWord_3704553, baseEnd_3704553] using wordTrace_append hprefix tailTrace_3704553
  have hstable : (prefixWord ++ tailWord_3704553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704553).length < 2 ^ (prefixWord ++ tailWord_3704553).sum := by decide
  have hdescent : baseEnd_3704553 < baseStart_3704553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704570 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_3704570 : Nat := 118140960795 + 3704570 * 2 ^ 59
def prefixEnd_3704570 : Nat := 4983230072969 + 3 ^ 40 * 3704570 * 2
def baseEnd_3704570 : Nat := 1268150018817784057691999

theorem tailTrace_3704570 : CollatzResearch.WordTrace tailWord_3704570 prefixEnd_3704570 1268150018817784057691999 := by
  unfold tailWord_3704570
  simp only [CollatzResearch.WordTrace]
  refine ⟨33779192047245763757517791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90077845459322036686714109 33779192047245763757517791)
  ·
    refine ⟨50668788070868645636276687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33779192047245763757517791 50668788070868645636276687)
    ·
      refine ⟨76003182106302968454415031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50668788070868645636276687 76003182106302968454415031)
      ·
        refine ⟨114004773159454452681622547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76003182106302968454415031 114004773159454452681622547)
        ·
          refine ⟨171007159739181679022433821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114004773159454452681622547 171007159739181679022433821)
          ·
            refine ⟨64127684902193129633412683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171007159739181679022433821 64127684902193129633412683)
            ·
              refine ⟨96191527353289694450119025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64127684902193129633412683 96191527353289694450119025)
              ·
                refine ⟨72143645514967270837589269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96191527353289694450119025 72143645514967270837589269)
                ·
                  refine ⟨3381733383514090820511997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72143645514967270837589269 3381733383514090820511997)
                  ·
                    refine ⟨1268150018817784057691999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381733383514090820511997 1268150018817784057691999)
                    ·
                      rfl

theorem cell22_3704570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_3704570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704570 prefixEnd_3704570 := by exact prefixLift 3704570
  have htrace : WordTrace (prefixWord ++ tailWord_3704570) baseStart_3704570 baseEnd_3704570 := by
    simpa [prefixWord, tailWord_3704570, baseEnd_3704570] using wordTrace_append hprefix tailTrace_3704570
  have hstable : (prefixWord ++ tailWord_3704570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704570).length < 2 ^ (prefixWord ++ tailWord_3704570).sum := by decide
  have hdescent : baseEnd_3704570 < baseStart_3704570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704606 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3704606 : Nat := 118140960795 + 3704606 * 2 ^ 59
def prefixEnd_3704606 : Nat := 4983230072969 + 3 ^ 40 * 3704606 * 2
def baseEnd_3704606 : Nat := 422720780784497321263963

theorem tailTrace_3704606 : CollatzResearch.WordTrace tailWord_3704606 prefixEnd_3704606 422720780784497321263963 := by
  unfold tailWord_3704606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889760152106579147297709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90078720811235088785587781 16889760152106579147297709)
  ·
    refine ⟨6333660057039967180236641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16889760152106579147297709 6333660057039967180236641)
    ·
      refine ⟨4750245042779975385177481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6333660057039967180236641 4750245042779975385177481)
      ·
        refine ⟨3562683782084981538883111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4750245042779975385177481 3562683782084981538883111)
        ·
          refine ⟨5344025673127472308324667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562683782084981538883111 5344025673127472308324667)
          ·
            refine ⟨8016038509691208462487001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344025673127472308324667 8016038509691208462487001)
            ·
              refine ⟨6012028882268406346865251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8016038509691208462487001 6012028882268406346865251)
              ·
                refine ⟨9018043323402609520297877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012028882268406346865251 9018043323402609520297877)
                ·
                  refine ⟨422720780784497321263963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9018043323402609520297877 422720780784497321263963)
                  ·
                    rfl

theorem cell22_3704606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3704606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704606 prefixEnd_3704606 := by exact prefixLift 3704606
  have htrace : WordTrace (prefixWord ++ tailWord_3704606) baseStart_3704606 baseEnd_3704606 := by
    simpa [prefixWord, tailWord_3704606, baseEnd_3704606] using wordTrace_append hprefix tailTrace_3704606
  have hstable : (prefixWord ++ tailWord_3704606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704606).length < 2 ^ (prefixWord ++ tailWord_3704606).sum := by decide
  have hdescent : baseEnd_3704606 < baseStart_3704606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704632 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_3704632 : Nat := 118140960795 + 3704632 * 2 ^ 59
def prefixEnd_3704632 : Nat := 4983230072969 + 3 ^ 40 * 3704632 * 2
def baseEnd_3704632 : Nat := 1268171242684836562641809

theorem tailTrace_3704632 : CollatzResearch.WordTrace tailWord_3704632 prefixEnd_3704632 1268171242684836562641809 := by
  unfold tailWord_3704632
  simp only [CollatzResearch.WordTrace]
  refine ⟨67559514757379219809414075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90079353009838959745885433 67559514757379219809414075)
  ·
    refine ⟨101339272136068829714121113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67559514757379219809414075 101339272136068829714121113)
    ·
      refine ⟨76004454102051622285590835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101339272136068829714121113 76004454102051622285590835)
      ·
        refine ⟨114006681153077433428386253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76004454102051622285590835 114006681153077433428386253)
        ·
          refine ⟨42752505432404037535644845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114006681153077433428386253 42752505432404037535644845)
          ·
            refine ⟨16032189537151514075866817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42752505432404037535644845 16032189537151514075866817)
            ·
              refine ⟨12024142152863635556900113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16032189537151514075866817 12024142152863635556900113)
              ·
                refine ⟨9018106614647726667675085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12024142152863635556900113 9018106614647726667675085)
                ·
                  refine ⟨3381789980492897500378157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9018106614647726667675085 3381789980492897500378157)
                  ·
                    refine ⟨1268171242684836562641809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381789980492897500378157 1268171242684836562641809)
                    ·
                      rfl

theorem cell22_3704632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_3704632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704632 prefixEnd_3704632 := by exact prefixLift 3704632
  have htrace : WordTrace (prefixWord ++ tailWord_3704632) baseStart_3704632 baseEnd_3704632 := by
    simpa [prefixWord, tailWord_3704632, baseEnd_3704632] using wordTrace_append hprefix tailTrace_3704632
  have hstable : (prefixWord ++ tailWord_3704632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704632).length < 2 ^ (prefixWord ++ tailWord_3704632).sum := by decide
  have hdescent : baseEnd_3704632 < baseStart_3704632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704666 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_3704666 : Nat := 118140960795 + 3704666 * 2 ^ 59
def prefixEnd_3704666 : Nat := 4983230072969 + 3 ^ 40 * 3704666 * 2
def baseEnd_3704666 : Nat := 1268182881579671807291705

theorem tailTrace_3704666 : CollatzResearch.WordTrace tailWord_3704666 prefixEnd_3704666 1268182881579671807291705 := by
  unfold tailWord_3704666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780067399158815856391463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90080179731090175617043901 33780067399158815856391463)
  ·
    refine ⟨50670101098738223784587195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33780067399158815856391463 50670101098738223784587195)
    ·
      refine ⟨76005151648107335676880793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50670101098738223784587195 76005151648107335676880793)
      ·
        refine ⟨57003863736080501757660595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76005151648107335676880793 57003863736080501757660595)
        ·
          refine ⟨85505795604120752636490893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57003863736080501757660595 85505795604120752636490893)
          ·
            refine ⟨32064673351545282238684085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85505795604120752636490893 32064673351545282238684085)
            ·
              refine ⟨3006063126707370209876633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32064673351545282238684085 3006063126707370209876633)
              ·
                refine ⟨2254547345030527657407475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006063126707370209876633 2254547345030527657407475)
                ·
                  refine ⟨3381821017545791486111213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254547345030527657407475 3381821017545791486111213)
                  ·
                    refine ⟨1268182881579671807291705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381821017545791486111213 1268182881579671807291705)
                    ·
                      rfl

theorem cell22_3704666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_3704666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704666 prefixEnd_3704666 := by exact prefixLift 3704666
  have htrace : WordTrace (prefixWord ++ tailWord_3704666) baseStart_3704666 baseEnd_3704666 := by
    simpa [prefixWord, tailWord_3704666, baseEnd_3704666] using wordTrace_append hprefix tailTrace_3704666
  have hstable : (prefixWord ++ tailWord_3704666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704666).length < 2 ^ (prefixWord ++ tailWord_3704666).sum := by decide
  have hdescent : baseEnd_3704666 < baseStart_3704666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704690 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_3704690 : Nat := 118140960795 + 3704690 * 2 ^ 59
def prefixEnd_3704690 : Nat := 4983230072969 + 3 ^ 40 * 3704690 * 2
def baseEnd_3704690 : Nat := 422730365756714581563877

theorem tailTrace_3704690 : CollatzResearch.WordTrace tailWord_3704690 prefixEnd_3704690 422730365756714581563877 := by
  unfold tailWord_3704690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780286237137078881109881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90080763299032210349626349 33780286237137078881109881)
  ·
    refine ⟨25335214677852809160832411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33780286237137078881109881 25335214677852809160832411)
    ·
      refine ⟨38002822016779213741248617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25335214677852809160832411 38002822016779213741248617)
      ·
        refine ⟨28502116512584410305936463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38002822016779213741248617 28502116512584410305936463)
        ·
          refine ⟨42753174768876615458904695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28502116512584410305936463 42753174768876615458904695)
          ·
            refine ⟨64129762153314923188357043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42753174768876615458904695 64129762153314923188357043)
            ·
              refine ⟨96194643229972384782535565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64129762153314923188357043 96194643229972384782535565)
              ·
                refine ⟨36072991211239644293450837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96194643229972384782535565 36072991211239644293450837)
                ·
                  refine ⟨422730365756714581563877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36072991211239644293450837 422730365756714581563877)
                  ·
                    rfl

theorem cell22_3704690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_3704690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704690 prefixEnd_3704690 := by exact prefixLift 3704690
  have htrace : WordTrace (prefixWord ++ tailWord_3704690) baseStart_3704690 baseEnd_3704690 := by
    simpa [prefixWord, tailWord_3704690, baseEnd_3704690] using wordTrace_append hprefix tailTrace_3704690
  have hstable : (prefixWord ++ tailWord_3704690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704690).length < 2 ^ (prefixWord ++ tailWord_3704690).sum := by decide
  have hdescent : baseEnd_3704690 < baseStart_3704690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704709 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_3704709 : Nat := 118140960795 + 3704709 * 2 ^ 59
def prefixEnd_3704709 : Nat := 4983230072969 + 3 ^ 40 * 3704709 * 2
def baseEnd_3704709 : Nat := 1268197601358434028466573

theorem tailTrace_3704709 : CollatzResearch.WordTrace tailWord_3704709 prefixEnd_3704709 1268197601358434028466573 := by
  unfold tailWord_3704709
  simp only [CollatzResearch.WordTrace]
  refine ⟨135121837935479481769381181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90081225290319654512920787 135121837935479481769381181)
  ·
    refine ⟨50670689225804805663517943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135121837935479481769381181 50670689225804805663517943)
    ·
      refine ⟨76006033838707208495276915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50670689225804805663517943 76006033838707208495276915)
      ·
        refine ⟨114009050758060812742915373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76006033838707208495276915 114009050758060812742915373)
        ·
          refine ⟨42753394034272804778593265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114009050758060812742915373 42753394034272804778593265)
          ·
            refine ⟨32065045525704603583944949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42753394034272804778593265 32065045525704603583944949)
            ·
              refine ⟨3006098018034806585994839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32065045525704603583944949 3006098018034806585994839)
              ·
                refine ⟨4509147027052209878992259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006098018034806585994839 4509147027052209878992259)
                ·
                  refine ⟨6763720540578314818488389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509147027052209878992259 6763720540578314818488389)
                  ·
                    refine ⟨1268197601358434028466573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6763720540578314818488389 1268197601358434028466573)
                    ·
                      rfl

theorem cell22_3704709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_3704709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704709 prefixEnd_3704709 := by exact prefixLift 3704709
  have htrace : WordTrace (prefixWord ++ tailWord_3704709) baseStart_3704709 baseEnd_3704709 := by
    simpa [prefixWord, tailWord_3704709, baseEnd_3704709] using wordTrace_append hprefix tailTrace_3704709
  have hstable : (prefixWord ++ tailWord_3704709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704709).length < 2 ^ (prefixWord ++ tailWord_3704709).sum := by decide
  have hdescent : baseEnd_3704709 < baseStart_3704709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704767 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 5, 3]
def baseStart_3704767 : Nat := 118140960795 + 3704767 * 2 ^ 59
def prefixEnd_3704767 : Nat := 4983230072969 + 3 ^ 40 * 3704767 * 2
def baseEnd_3704767 : Nat := 1268217455943741210516395

theorem tailTrace_3704767 : CollatzResearch.WordTrace tailWord_3704767 prefixEnd_3704767 1268217455943741210516395 := by
  unfold tailWord_3704767
  simp only [CollatzResearch.WordTrace]
  refine ⟨135123953369269357674992555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90082635579512905116661703 135123953369269357674992555)
  ·
    refine ⟨202685930053904036512488833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135123953369269357674992555 202685930053904036512488833)
    ·
      refine ⟨152014447540428027384366625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202685930053904036512488833 152014447540428027384366625)
      ·
        refine ⟨114010835655321020538274969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152014447540428027384366625 114010835655321020538274969)
        ·
          refine ⟨85508126741490765403706227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114010835655321020538274969 85508126741490765403706227)
          ·
            refine ⟨128262190112236148105559341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85508126741490765403706227 128262190112236148105559341)
            ·
              refine ⟨48098321292088555539584753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128262190112236148105559341 48098321292088555539584753)
              ·
                refine ⟨36073740969066416654688565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48098321292088555539584753 36073740969066416654688565)
                ·
                  refine ⟨3381913215849976561377053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36073740969066416654688565 3381913215849976561377053)
                  ·
                    refine ⟨1268217455943741210516395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381913215849976561377053 1268217455943741210516395)
                    ·
                      rfl

theorem cell22_3704767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_3704767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704767 prefixEnd_3704767 := by exact prefixLift 3704767
  have htrace : WordTrace (prefixWord ++ tailWord_3704767) baseStart_3704767 baseEnd_3704767 := by
    simpa [prefixWord, tailWord_3704767, baseEnd_3704767] using wordTrace_append hprefix tailTrace_3704767
  have hstable : (prefixWord ++ tailWord_3704767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704767).length < 2 ^ (prefixWord ++ tailWord_3704767).sum := by decide
  have hdescent : baseEnd_3704767 < baseStart_3704767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704790 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3704790 : Nat := 118140960795 + 3704790 * 2 ^ 59
def prefixEnd_3704790 : Nat := 4983230072969 + 3 ^ 40 * 3704790 * 2
def baseEnd_3704790 : Nat := 1268225329313776817191325

theorem tailTrace_3704790 : CollatzResearch.WordTrace tailWord_3704790 prefixEnd_3704790 1268225329313776817191325 := by
  unfold tailWord_3704790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445299515511627037692489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90083194832124021735386549 8445299515511627037692489)
  ·
    refine ⟨6333974636633720278269367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8445299515511627037692489 6333974636633720278269367)
    ·
      refine ⟨9500961954950580417404051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6333974636633720278269367 9500961954950580417404051)
      ·
        refine ⟨14251442932425870626106077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9500961954950580417404051 14251442932425870626106077)
        ·
          refine ⟨5344291099659701484789779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14251442932425870626106077 5344291099659701484789779)
          ·
            refine ⟨8016436649489552227184669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344291099659701484789779 8016436649489552227184669)
            ·
              refine ⟨3006163743558582085194251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8016436649489552227184669 3006163743558582085194251)
              ·
                refine ⟨4509245615337873127791377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006163743558582085194251 4509245615337873127791377)
                ·
                  refine ⟨3381934211503404845843533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4509245615337873127791377 3381934211503404845843533)
                  ·
                    refine ⟨1268225329313776817191325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381934211503404845843533 1268225329313776817191325)
                    ·
                      rfl

theorem cell22_3704790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3704790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704790 prefixEnd_3704790 := by exact prefixLift 3704790
  have htrace : WordTrace (prefixWord ++ tailWord_3704790) baseStart_3704790 baseEnd_3704790 := by
    simpa [prefixWord, tailWord_3704790, baseEnd_3704790] using wordTrace_append hprefix tailTrace_3704790
  have hstable : (prefixWord ++ tailWord_3704790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704790).length < 2 ^ (prefixWord ++ tailWord_3704790).sum := by decide
  have hdescent : baseEnd_3704790 < baseStart_3704790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704857 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_3704857 : Nat := 118140960795 + 3704857 * 2 ^ 59
def prefixEnd_3704857 : Nat := 4983230072969 + 3 ^ 40 * 3704857 * 2
def baseEnd_3704857 : Nat := 1268248264783010975766119

theorem tailTrace_3704857 : CollatzResearch.WordTrace tailWord_3704857 prefixEnd_3704857 1268248264783010975766119 := by
  unfold tailWord_3704857
  simp only [CollatzResearch.WordTrace]
  refine ⟨135127235938943303045768825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90084823959295535363845883 135127235938943303045768825)
  ·
    refine ⟨101345426954207477284326619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135127235938943303045768825 101345426954207477284326619)
    ·
      refine ⟨152018140431311215926489929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101345426954207477284326619 152018140431311215926489929)
      ·
        refine ⟨114013605323483411944867447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152018140431311215926489929 114013605323483411944867447)
        ·
          refine ⟨171020407985225117917301171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114013605323483411944867447 171020407985225117917301171)
          ·
            refine ⟨256530611977837676875951757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171020407985225117917301171 256530611977837676875951757)
            ·
              refine ⟨96198979491689128828481909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256530611977837676875951757 96198979491689128828481909)
              ·
                refine ⟨9018654327345855827670179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96198979491689128828481909 9018654327345855827670179)
                ·
                  refine ⟨13527981491018783741505269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018654327345855827670179 13527981491018783741505269)
                  ·
                    refine ⟨1268248264783010975766119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13527981491018783741505269 1268248264783010975766119)
                    ·
                      rfl

theorem cell22_3704857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_3704857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704857 prefixEnd_3704857 := by exact prefixLift 3704857
  have htrace : WordTrace (prefixWord ++ tailWord_3704857) baseStart_3704857 baseEnd_3704857 := by
    simpa [prefixWord, tailWord_3704857, baseEnd_3704857] using wordTrace_append hprefix tailTrace_3704857
  have hstable : (prefixWord ++ tailWord_3704857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704857).length < 2 ^ (prefixWord ++ tailWord_3704857).sum := by decide
  have hdescent : baseEnd_3704857 < baseStart_3704857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704861 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3704861 : Nat := 118140960795 + 3704861 * 2 ^ 59
def prefixEnd_3704861 : Nat := 4983230072969 + 3 ^ 40 * 3704861 * 2
def baseEnd_3704861 : Nat := 1268249634064756298666107

theorem tailTrace_3704861 : CollatzResearch.WordTrace tailWord_3704861 prefixEnd_3704861 1268249634064756298666107 := by
  unfold tailWord_3704861
  simp only [CollatzResearch.WordTrace]
  refine ⟨135127381830928811728914437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90084921220619207819276291 135127381830928811728914437)
  ·
    refine ⟨25336384093299152199171457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135127381830928811728914437 25336384093299152199171457)
    ·
      refine ⟨19002288069974364149378593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25336384093299152199171457 19002288069974364149378593)
      ·
        refine ⟨14251716052480773112033945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19002288069974364149378593 14251716052480773112033945)
        ·
          refine ⟨10688787039360579834025459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14251716052480773112033945 10688787039360579834025459)
          ·
            refine ⟨16033180559040869751038189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10688787039360579834025459 16033180559040869751038189)
            ·
              refine ⟨6012442709640326156639321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16033180559040869751038189 6012442709640326156639321)
              ·
                refine ⟨4509332032230244617479491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6012442709640326156639321 4509332032230244617479491)
                ·
                  refine ⟨6763998048345366926219237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509332032230244617479491 6763998048345366926219237)
                  ·
                    refine ⟨1268249634064756298666107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6763998048345366926219237 1268249634064756298666107)
                    ·
                      rfl

theorem cell22_3704861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3704861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704861 prefixEnd_3704861 := by exact prefixLift 3704861
  have htrace : WordTrace (prefixWord ++ tailWord_3704861) baseStart_3704861 baseEnd_3704861 := by
    simpa [prefixWord, tailWord_3704861, baseEnd_3704861] using wordTrace_append hprefix tailTrace_3704861
  have hstable : (prefixWord ++ tailWord_3704861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704861).length < 2 ^ (prefixWord ++ tailWord_3704861).sum := by decide
  have hdescent : baseEnd_3704861 < baseStart_3704861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704874 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3704874 : Nat := 118140960795 + 3704874 * 2 ^ 59
def prefixEnd_3704874 : Nat := 4983230072969 + 3 ^ 40 * 3704874 * 2
def baseEnd_3704874 : Nat := 1268254084230428598091067

theorem tailTrace_3704874 : CollatzResearch.WordTrace tailWord_3704874 prefixEnd_3704874 1268254084230428598091067 := by
  unfold tailWord_3704874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33781963994970428737284419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90085237319921143299425117 33781963994970428737284419)
  ·
    refine ⟨50672945992455643105926629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33781963994970428737284419 50672945992455643105926629)
    ·
      refine ⟨9501177373585433082361243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50672945992455643105926629 9501177373585433082361243)
      ·
        refine ⟨14251766060378149623541865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9501177373585433082361243 14251766060378149623541865)
        ·
          refine ⟨10688824545283612217656399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14251766060378149623541865 10688824545283612217656399)
          ·
            refine ⟨16033236817925418326484599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10688824545283612217656399 16033236817925418326484599)
            ·
              refine ⟨24049855226888127489726899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16033236817925418326484599 24049855226888127489726899)
              ·
                refine ⟨36074782840332191234590349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24049855226888127489726899 36074782840332191234590349)
                ·
                  refine ⟨13528043565124571712971381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36074782840332191234590349 13528043565124571712971381)
                  ·
                    refine ⟨1268254084230428598091067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13528043565124571712971381 1268254084230428598091067)
                    ·
                      rfl

theorem cell22_3704874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3704874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704874 prefixEnd_3704874 := by exact prefixLift 3704874
  have htrace : WordTrace (prefixWord ++ tailWord_3704874) baseStart_3704874 baseEnd_3704874 := by
    simpa [prefixWord, tailWord_3704874, baseEnd_3704874] using wordTrace_append hprefix tailTrace_3704874
  have hstable : (prefixWord ++ tailWord_3704874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704874).length < 2 ^ (prefixWord ++ tailWord_3704874).sum := by decide
  have hdescent : baseEnd_3704874 < baseStart_3704874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704878 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3704878 : Nat := 118140960795 + 3704878 * 2 ^ 59
def prefixEnd_3704878 : Nat := 4983230072969 + 3 ^ 40 * 3704878 * 2
def baseEnd_3704878 : Nat := 1268255453512173920991055

theorem tailTrace_3704878 : CollatzResearch.WordTrace tailWord_3704878 prefixEnd_3704878 1268255453512173920991055 := by
  unfold tailWord_3704878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891000233983402954035411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90085334581244815754855525 16891000233983402954035411)
  ·
    refine ⟨25336500350975104431053117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891000233983402954035411 25336500350975104431053117)
    ·
      refine ⟨9501187631615664161644919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25336500350975104431053117 9501187631615664161644919)
      ·
        refine ⟨14251781447423496242467379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9501187631615664161644919 14251781447423496242467379)
        ·
          refine ⟨21377672171135244363701069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14251781447423496242467379 21377672171135244363701069)
          ·
            refine ⟨8016627064175716636387901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21377672171135244363701069 8016627064175716636387901)
            ·
              refine ⟨3006235149065893738645463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8016627064175716636387901 3006235149065893738645463)
              ·
                refine ⟨4509352723598840607968195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006235149065893738645463 4509352723598840607968195)
                ·
                  refine ⟨6764029085398260911952293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509352723598840607968195 6764029085398260911952293)
                  ·
                    refine ⟨1268255453512173920991055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764029085398260911952293 1268255453512173920991055)
                    ·
                      rfl

theorem cell22_3704878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3704878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704878 prefixEnd_3704878 := by exact prefixLift 3704878
  have htrace : WordTrace (prefixWord ++ tailWord_3704878) baseStart_3704878 baseEnd_3704878 := by
    simpa [prefixWord, tailWord_3704878, baseEnd_3704878] using wordTrace_append hprefix tailTrace_3704878
  have hstable : (prefixWord ++ tailWord_3704878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704878).length < 2 ^ (prefixWord ++ tailWord_3704878).sum := by decide
  have hdescent : baseEnd_3704878 < baseStart_3704878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704919 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 5, 3]
def baseStart_3704919 : Nat := 118140960795 + 3704919 * 2 ^ 59
def prefixEnd_3704919 : Nat := 4983230072969 + 3 ^ 40 * 3704919 * 2
def baseEnd_3704919 : Nat := 1268269488650063480715929

theorem tailTrace_3704919 : CollatzResearch.WordTrace tailWord_3704919 prefixEnd_3704919 1268269488650063480715929 := by
  unfold tailWord_3704919
  simp only [CollatzResearch.WordTrace]
  refine ⟨135129497264718687634525811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90086331509812458423017207 135129497264718687634525811)
  ·
    refine ⟨202694245897078031451788717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135129497264718687634525811 202694245897078031451788717)
    ·
      refine ⟨76010342211404261794420769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202694245897078031451788717 76010342211404261794420769)
      ·
        refine ⟨57007756658553196345815577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76010342211404261794420769 57007756658553196345815577)
        ·
          refine ⟨42755817493914897259361683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57007756658553196345815577 42755817493914897259361683)
          ·
            refine ⟨64133726240872345889042525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42755817493914897259361683 64133726240872345889042525)
            ·
              refine ⟨24050147340327129708390947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64133726240872345889042525 24050147340327129708390947)
              ·
                refine ⟨36075221010490694562586421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24050147340327129708390947 36075221010490694562586421)
                ·
                  refine ⟨3382051969733502615242477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36075221010490694562586421 3382051969733502615242477)
                  ·
                    refine ⟨1268269488650063480715929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382051969733502615242477 1268269488650063480715929)
                    ·
                      rfl

theorem cell22_3704919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_3704919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704919 prefixEnd_3704919 := by exact prefixLift 3704919
  have htrace : WordTrace (prefixWord ++ tailWord_3704919) baseStart_3704919 baseEnd_3704919 := by
    simpa [prefixWord, tailWord_3704919, baseEnd_3704919] using wordTrace_append hprefix tailTrace_3704919
  have hstable : (prefixWord ++ tailWord_3704919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704919).length < 2 ^ (prefixWord ++ tailWord_3704919).sum := by decide
  have hdescent : baseEnd_3704919 < baseStart_3704919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704953 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 1, 3]
def baseStart_3704953 : Nat := 118140960795 + 3704953 * 2 ^ 59
def prefixEnd_3704953 : Nat := 4983230072969 + 3 ^ 40 * 3704953 * 2
def baseEnd_3704953 : Nat := 1268281127544898725365825

theorem tailTrace_3704953 : CollatzResearch.WordTrace tailWord_3704953 prefixEnd_3704953 1268281127544898725365825 := by
  unfold tailWord_3704953
  simp only [CollatzResearch.WordTrace]
  refine ⟨135130737346595511441263513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90087158231063674294175675 135130737346595511441263513)
  ·
    refine ⟨101348053009946633580947635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135130737346595511441263513 101348053009946633580947635)
    ·
      refine ⟨152022079514919950371421453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101348053009946633580947635 152022079514919950371421453)
      ·
        refine ⟨57008279818094981389283045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152022079514919950371421453 57008279818094981389283045)
        ·
          refine ⟨10689052465892809010490571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57008279818094981389283045 10689052465892809010490571)
          ·
            refine ⟨16033578698839213515735857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10689052465892809010490571 16033578698839213515735857)
            ·
              refine ⟨12025184024129410136801893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16033578698839213515735857 12025184024129410136801893)
              ·
                refine ⟨2254722004524264400650355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12025184024129410136801893 2254722004524264400650355)
                ·
                  refine ⟨3382083006786396600975533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254722004524264400650355 3382083006786396600975533)
                  ·
                    refine ⟨1268281127544898725365825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382083006786396600975533 1268281127544898725365825)
                    ·
                      rfl

theorem cell22_3704953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_3704953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704953 prefixEnd_3704953 := by exact prefixLift 3704953
  have htrace : WordTrace (prefixWord ++ tailWord_3704953) baseStart_3704953 baseEnd_3704953 := by
    simpa [prefixWord, tailWord_3704953, baseEnd_3704953] using wordTrace_append hprefix tailTrace_3704953
  have hstable : (prefixWord ++ tailWord_3704953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704953).length < 2 ^ (prefixWord ++ tailWord_3704953).sum := by decide
  have hdescent : baseEnd_3704953 < baseStart_3704953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3704964 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3704964 : Nat := 118140960795 + 3704964 * 2 ^ 59
def prefixEnd_3704964 : Nat := 4983230072969 + 3 ^ 40 * 3704964 * 2
def baseEnd_3704964 : Nat := 1268284893069698363340791

theorem tailTrace_3704964 : CollatzResearch.WordTrace tailWord_3704964 prefixEnd_3704964 1268284893069698363340791 := by
  unfold tailWord_3704964
  simp only [CollatzResearch.WordTrace]
  refine ⟨67565569274777830159956973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90087425699703773546609297 67565569274777830159956973)
  ·
    refine ⟨25337088478041686309983865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67565569274777830159956973 25337088478041686309983865)
    ·
      refine ⟨19002816358531264732487899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25337088478041686309983865 19002816358531264732487899)
      ·
        refine ⟨28504224537796897098731849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19002816358531264732487899 28504224537796897098731849)
        ·
          refine ⟨21378168403347672824048887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28504224537796897098731849 21378168403347672824048887)
          ·
            refine ⟨32067252605021509236073331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21378168403347672824048887 32067252605021509236073331)
            ·
              refine ⟨48100878907532263854109997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32067252605021509236073331 48100878907532263854109997)
              ·
                refine ⟨18037829590324598945291249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48100878907532263854109997 18037829590324598945291249)
                ·
                  refine ⟨13528372192743449208968437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18037829590324598945291249 13528372192743449208968437)
                  ·
                    refine ⟨1268284893069698363340791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13528372192743449208968437 1268284893069698363340791)
                    ·
                      rfl

theorem cell22_3704964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3704964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3704964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3704964 prefixEnd_3704964 := by exact prefixLift 3704964
  have htrace : WordTrace (prefixWord ++ tailWord_3704964) baseStart_3704964 baseEnd_3704964 := by
    simpa [prefixWord, tailWord_3704964, baseEnd_3704964] using wordTrace_append hprefix tailTrace_3704964
  have hstable : (prefixWord ++ tailWord_3704964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3704964).length < 2 ^ (prefixWord ++ tailWord_3704964).sum := by decide
  have hdescent : baseEnd_3704964 < baseStart_3704964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3704964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705086 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3705086 : Nat := 118140960795 + 3705086 * 2 ^ 59
def prefixEnd_3705086 : Nat := 4983230072969 + 3 ^ 40 * 3705086 * 2
def baseEnd_3705086 : Nat := 1268326656162930711790417

theorem tailTrace_3705086 : CollatzResearch.WordTrace tailWord_3705086 prefixEnd_3705086 1268326656162930711790417 := by
  unfold tailWord_3705086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891948531889209394481889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90090392170075783437236741 16891948531889209394481889)
  ·
    refine ⟨12668961398916907045861417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16891948531889209394481889 12668961398916907045861417)
    ·
      refine ⟨9501721049187680284396063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12668961398916907045861417 9501721049187680284396063)
      ·
        refine ⟨14252581573781520426594095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9501721049187680284396063 14252581573781520426594095)
        ·
          refine ⟨21378872360672280639891143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14252581573781520426594095 21378872360672280639891143)
          ·
            refine ⟨32068308541008420959836715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21378872360672280639891143 32068308541008420959836715)
            ·
              refine ⟨48102462811512631439755073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32068308541008420959836715 48102462811512631439755073)
              ·
                refine ⟨36076847108634473579816305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48102462811512631439755073 36076847108634473579816305)
                ·
                  refine ⟨27057635331475855184862229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36076847108634473579816305 27057635331475855184862229)
                  ·
                    refine ⟨1268326656162930711790417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27057635331475855184862229 1268326656162930711790417)
                    ·
                      rfl

theorem cell22_3705086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3705086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705086 prefixEnd_3705086 := by exact prefixLift 3705086
  have htrace : WordTrace (prefixWord ++ tailWord_3705086) baseStart_3705086 baseEnd_3705086 := by
    simpa [prefixWord, tailWord_3705086, baseEnd_3705086] using wordTrace_append hprefix tailTrace_3705086
  have hstable : (prefixWord ++ tailWord_3705086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705086).length < 2 ^ (prefixWord ++ tailWord_3705086).sum := by decide
  have hdescent : baseEnd_3705086 < baseStart_3705086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705099 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_3705099 : Nat := 118140960795 + 3705099 * 2 ^ 59
def prefixEnd_3705099 : Nat := 4983230072969 + 3 ^ 40 * 3705099 * 2
def baseEnd_3705099 : Nat := 1268331106328603011215377

theorem tailTrace_3705099 : CollatzResearch.WordTrace tailWord_3705099 prefixEnd_3705099 1268331106328603011215377 := by
  unfold tailWord_3705099
  simp only [CollatzResearch.WordTrace]
  refine ⟨135136062404066578376078351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90090708269377718917385567 135136062404066578376078351)
  ·
    refine ⟨202704093606099867564117527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135136062404066578376078351 202704093606099867564117527)
    ·
      refine ⟨304056140409149801346176291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202704093606099867564117527 304056140409149801346176291)
      ·
        refine ⟨456084210613724702019264437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304056140409149801346176291 456084210613724702019264437)
        ·
          refine ⟨42757894745036690814306041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 456084210613724702019264437 42757894745036690814306041)
          ·
            refine ⟨32068421058777518110729531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42757894745036690814306041 32068421058777518110729531)
            ·
              refine ⟨48102631588166277166094297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32068421058777518110729531 48102631588166277166094297)
              ·
                refine ⟨36076973691124707874570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48102631588166277166094297 36076973691124707874570723)
                ·
                  refine ⟨54115460536687061811856085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36076973691124707874570723 54115460536687061811856085)
                  ·
                    refine ⟨1268331106328603011215377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54115460536687061811856085 1268331106328603011215377)
                    ·
                      rfl

theorem cell22_3705099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_3705099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705099 prefixEnd_3705099 := by exact prefixLift 3705099
  have htrace : WordTrace (prefixWord ++ tailWord_3705099) baseStart_3705099 baseEnd_3705099 := by
    simpa [prefixWord, tailWord_3705099, baseEnd_3705099] using wordTrace_append hprefix tailTrace_3705099
  have hstable : (prefixWord ++ tailWord_3705099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705099).length < 2 ^ (prefixWord ++ tailWord_3705099).sum := by decide
  have hdescent : baseEnd_3705099 < baseStart_3705099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705105 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 1, 3]
def baseStart_3705105 : Nat := 118140960795 + 3705105 * 2 ^ 59
def prefixEnd_3705105 : Nat := 4983230072969 + 3 ^ 40 * 3705105 * 2
def baseEnd_3705105 : Nat := 1268333160251220995565359

theorem tailTrace_3705105 : CollatzResearch.WordTrace tailWord_3705105 prefixEnd_3705105 1268333160251220995565359 := by
  unfold tailWord_3705105
  simp only [CollatzResearch.WordTrace]
  refine ⟨135136281242044841400796769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90090854161363227600531179 135136281242044841400796769)
  ·
    refine ⟨101352210931533631050597577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135136281242044841400796769 101352210931533631050597577)
    ·
      refine ⟨76014158198650223287948183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101352210931533631050597577 76014158198650223287948183)
      ·
        refine ⟨114021237297975334931922275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76014158198650223287948183 114021237297975334931922275)
        ·
          refine ⟨171031855946963002397883413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114021237297975334931922275 171031855946963002397883413)
          ·
            refine ⟨8017118247513890737400785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171031855946963002397883413 8017118247513890737400785)
            ·
              refine ⟨6012838685635418053050589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8017118247513890737400785 6012838685635418053050589)
              ·
                refine ⟨2254814507113281769893971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6012838685635418053050589 2254814507113281769893971)
                ·
                  refine ⟨3382221760669922654840957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254814507113281769893971 3382221760669922654840957)
                  ·
                    refine ⟨1268333160251220995565359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382221760669922654840957 1268333160251220995565359)
                    ·
                      rfl

theorem cell22_3705105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_3705105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705105 prefixEnd_3705105 := by exact prefixLift 3705105
  have htrace : WordTrace (prefixWord ++ tailWord_3705105) baseStart_3705105 baseEnd_3705105 := by
    simpa [prefixWord, tailWord_3705105, baseEnd_3705105] using wordTrace_append hprefix tailTrace_3705105
  have hstable : (prefixWord ++ tailWord_3705105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705105).length < 2 ^ (prefixWord ++ tailWord_3705105).sum := by decide
  have hdescent : baseEnd_3705105 < baseStart_3705105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705146 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_3705146 : Nat := 118140960795 + 3705146 * 2 ^ 59
def prefixEnd_3705146 : Nat := 4983230072969 + 3 ^ 40 * 3705146 * 2
def baseEnd_3705146 : Nat := 422782398463036851763411

theorem tailTrace_3705146 : CollatzResearch.WordTrace tailWord_3705146 prefixEnd_3705146 422782398463036851763411 := by
  unfold tailWord_3705146
  simp only [CollatzResearch.WordTrace]
  refine ⟨33784444158724076350759823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90091851089930870268692861 33784444158724076350759823)
  ·
    refine ⟨50676666238086114526139735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33784444158724076350759823 50676666238086114526139735)
    ·
      refine ⟨76014999357129171789209603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50676666238086114526139735 76014999357129171789209603)
      ·
        refine ⟨114022499035693757683814405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76014999357129171789209603 114022499035693757683814405)
        ·
          refine ⟨21379218569192579565715201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114022499035693757683814405 21379218569192579565715201)
          ·
            refine ⟨16034413926894434674286401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21379218569192579565715201 16034413926894434674286401)
            ·
              refine ⟨12025810445170826005714801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16034413926894434674286401 12025810445170826005714801)
              ·
                refine ⟨9019357833878119504286101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12025810445170826005714801 9019357833878119504286101)
                ·
                  refine ⟨422782398463036851763411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9019357833878119504286101 422782398463036851763411)
                  ·
                    rfl

theorem cell22_3705146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_3705146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705146 prefixEnd_3705146 := by exact prefixLift 3705146
  have htrace : WordTrace (prefixWord ++ tailWord_3705146) baseStart_3705146 baseEnd_3705146 := by
    simpa [prefixWord, tailWord_3705146, baseEnd_3705146] using wordTrace_append hprefix tailTrace_3705146
  have hstable : (prefixWord ++ tailWord_3705146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705146).length < 2 ^ (prefixWord ++ tailWord_3705146).sum := by decide
  have hdescent : baseEnd_3705146 < baseStart_3705146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705148 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_3705148 : Nat := 118140960795 + 3705148 * 2 ^ 59
def prefixEnd_3705148 : Nat := 4983230072969 + 3 ^ 40 * 3705148 * 2
def baseEnd_3705148 : Nat := 1268347880029983216740227

theorem tailTrace_3705148 : CollatzResearch.WordTrace tailWord_3705148 prefixEnd_3705148 1268347880029983216740227 := by
  unfold tailWord_3705148
  simp only [CollatzResearch.WordTrace]
  refine ⟨67568924790444529872306049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90091899720592706496408065 67568924790444529872306049)
  ·
    refine ⟨50676693592833397404229537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67568924790444529872306049 50676693592833397404229537)
    ·
      refine ⟨38007520194625048053172153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50676693592833397404229537 38007520194625048053172153)
      ·
        refine ⟨28505640145968786039879115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38007520194625048053172153 28505640145968786039879115)
        ·
          refine ⟨42758460218953179059818673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28505640145968786039879115 42758460218953179059818673)
          ·
            refine ⟨32068845164214884294864005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42758460218953179059818673 32068845164214884294864005)
            ·
              refine ⟨6012908468290290805287001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32068845164214884294864005 6012908468290290805287001)
              ·
                refine ⟨4509681351217718103965251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6012908468290290805287001 4509681351217718103965251)
                ·
                  refine ⟨6764522026826577155947877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509681351217718103965251 6764522026826577155947877)
                  ·
                    refine ⟨1268347880029983216740227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764522026826577155947877 1268347880029983216740227)
                    ·
                      rfl

theorem cell22_3705148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_3705148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705148 prefixEnd_3705148 := by exact prefixLift 3705148
  have htrace : WordTrace (prefixWord ++ tailWord_3705148) baseStart_3705148 baseEnd_3705148 := by
    simpa [prefixWord, tailWord_3705148, baseEnd_3705148] using wordTrace_append hprefix tailTrace_3705148
  have hstable : (prefixWord ++ tailWord_3705148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705148).length < 2 ^ (prefixWord ++ tailWord_3705148).sum := by decide
  have hdescent : baseEnd_3705148 < baseStart_3705148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705156 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3705156 : Nat := 118140960795 + 3705156 * 2 ^ 59
def prefixEnd_3705156 : Nat := 4983230072969 + 3 ^ 40 * 3705156 * 2
def baseEnd_3705156 : Nat := 1268350618593473862540203

theorem tailTrace_3705156 : CollatzResearch.WordTrace tailWord_3705156 prefixEnd_3705156 1268350618593473862540203 := by
  unfold tailWord_3705156
  simp only [CollatzResearch.WordTrace]
  refine ⟨67569070682430038555451661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90092094243240051407268881 67569070682430038555451661)
  ·
    refine ⟨25338401505911264458294373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67569070682430038555451661 25338401505911264458294373)
    ·
      refine ⟨4750950282358362085930195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25338401505911264458294373 4750950282358362085930195)
      ·
        refine ⟨7126425423537543128895293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750950282358362085930195 7126425423537543128895293)
        ·
          refine ⟨2672409533826578673335735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7126425423537543128895293 2672409533826578673335735)
          ·
            refine ⟨4008614300739868010003603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672409533826578673335735 4008614300739868010003603)
            ·
              refine ⟨6012921451109802015005405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008614300739868010003603 6012921451109802015005405)
              ·
                refine ⟨2254845544166175755627027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6012921451109802015005405 2254845544166175755627027)
                ·
                  refine ⟨3382268316249263633440541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254845544166175755627027 3382268316249263633440541)
                  ·
                    refine ⟨1268350618593473862540203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382268316249263633440541 1268350618593473862540203)
                    ·
                      rfl

theorem cell22_3705156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3705156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705156 prefixEnd_3705156 := by exact prefixLift 3705156
  have htrace : WordTrace (prefixWord ++ tailWord_3705156) baseStart_3705156 baseEnd_3705156 := by
    simpa [prefixWord, tailWord_3705156, baseEnd_3705156] using wordTrace_append hprefix tailTrace_3705156
  have hstable : (prefixWord ++ tailWord_3705156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705156).length < 2 ^ (prefixWord ++ tailWord_3705156).sum := by decide
  have hdescent : baseEnd_3705156 < baseStart_3705156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705178 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_3705178 : Nat := 118140960795 + 3705178 * 2 ^ 59
def prefixEnd_3705178 : Nat := 4983230072969 + 3 ^ 40 * 3705178 * 2
def baseEnd_3705178 : Nat := 1268358149643073138490135

theorem tailTrace_3705178 : CollatzResearch.WordTrace tailWord_3705178 prefixEnd_3705178 1268358149643073138490135 := by
  unfold tailWord_3705178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33784735942695093717051047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90092629180520249912136125 33784735942695093717051047)
  ·
    refine ⟨50677103914042640575576571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33784735942695093717051047 50677103914042640575576571)
    ·
      refine ⟨76015655871063960863364857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50677103914042640575576571 76015655871063960863364857)
      ·
        refine ⟨57011741903297970647523643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76015655871063960863364857 57011741903297970647523643)
        ·
          refine ⟨85517612854946955971285465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57011741903297970647523643 85517612854946955971285465)
          ·
            refine ⟨64138209641210216978464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85517612854946955971285465 64138209641210216978464099)
            ·
              refine ⟨96207314461815325467696149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64138209641210216978464099 96207314461815325467696149)
              ·
                refine ⟨4509717865397593381298257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96207314461815325467696149 4509717865397593381298257)
                ·
                  refine ⟨3382288399048195035973693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4509717865397593381298257 3382288399048195035973693)
                  ·
                    refine ⟨1268358149643073138490135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382288399048195035973693 1268358149643073138490135)
                    ·
                      rfl

theorem cell22_3705178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_3705178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705178 prefixEnd_3705178 := by exact prefixLift 3705178
  have htrace : WordTrace (prefixWord ++ tailWord_3705178) baseStart_3705178 baseEnd_3705178 := by
    simpa [prefixWord, tailWord_3705178, baseEnd_3705178] using wordTrace_append hprefix tailTrace_3705178
  have hstable : (prefixWord ++ tailWord_3705178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705178).length < 2 ^ (prefixWord ++ tailWord_3705178).sum := by decide
  have hdescent : baseEnd_3705178 < baseStart_3705178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705191 : List Nat := [1, 1, 5, 1, 3, 1, 1, 9]
def baseStart_3705191 : Nat := 118140960795 + 3705191 * 2 ^ 59
def prefixEnd_3705191 : Nat := 4983230072969 + 3 ^ 40 * 3705191 * 2
def baseEnd_3705191 : Nat := 140929177756527270879455

theorem tailTrace_3705191 : CollatzResearch.WordTrace tailWord_3705191 prefixEnd_3705191 140929177756527270879455 := by
  unfold tailWord_3705191
  simp only [CollatzResearch.WordTrace]
  refine ⟨135139417919733278088427427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90092945279822185392284951 135139417919733278088427427)
  ·
    refine ⟨202709126879599917132641141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135139417919733278088427427 202709126879599917132641141)
    ·
      refine ⟨19003980644962492231185107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202709126879599917132641141 19003980644962492231185107)
      ·
        refine ⟨28505970967443738346777661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19003980644962492231185107 28505970967443738346777661)
        ·
          refine ⟨10689739112791401880041623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28505970967443738346777661 10689739112791401880041623)
          ·
            refine ⟨16034608669187102820062435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10689739112791401880041623 16034608669187102820062435)
            ·
              refine ⟨24051913003780654230093653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16034608669187102820062435 24051913003780654230093653)
              ·
                refine ⟨140929177756527270879455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24051913003780654230093653 140929177756527270879455)
                ·
                  rfl

theorem cell22_3705191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 9].length) (baseStart_3705191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705191 prefixEnd_3705191 := by exact prefixLift 3705191
  have htrace : WordTrace (prefixWord ++ tailWord_3705191) baseStart_3705191 baseEnd_3705191 := by
    simpa [prefixWord, tailWord_3705191, baseEnd_3705191] using wordTrace_append hprefix tailTrace_3705191
  have hstable : (prefixWord ++ tailWord_3705191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705191).length < 2 ^ (prefixWord ++ tailWord_3705191).sum := by decide
  have hdescent : baseEnd_3705191 < baseStart_3705191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705251 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_3705251 : Nat := 118140960795 + 3705251 * 2 ^ 59
def prefixEnd_3705251 : Nat := 4983230072969 + 3 ^ 40 * 3705251 * 2
def baseEnd_3705251 : Nat := 1268383139034925281414911

theorem tailTrace_3705251 : CollatzResearch.WordTrace tailWord_3705251 prefixEnd_3705251 1268383139034925281414911 := by
  unfold tailWord_3705251
  simp only [CollatzResearch.WordTrace]
  refine ⟨135141606299515908335611607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90094404199677272223741071 135141606299515908335611607)
  ·
    refine ⟨202712409449273862503417411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135141606299515908335611607 202712409449273862503417411)
    ·
      refine ⟨304068614173910793755126117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202712409449273862503417411 304068614173910793755126117)
      ·
        refine ⟨57012865157608273829086147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304068614173910793755126117 57012865157608273829086147)
        ·
          refine ⟨85519297736412410743629221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57012865157608273829086147 85519297736412410743629221)
          ·
            refine ⟨16034868325577327014430479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85519297736412410743629221 16034868325577327014430479)
            ·
              refine ⟨24052302488365990521645719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16034868325577327014430479 24052302488365990521645719)
              ·
                refine ⟨36078453732548985782468579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24052302488365990521645719 36078453732548985782468579)
                ·
                  refine ⟨54117680598823478673702869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36078453732548985782468579 54117680598823478673702869)
                  ·
                    refine ⟨1268383139034925281414911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54117680598823478673702869 1268383139034925281414911)
                    ·
                      rfl

theorem cell22_3705251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_3705251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705251 prefixEnd_3705251 := by exact prefixLift 3705251
  have htrace : WordTrace (prefixWord ++ tailWord_3705251) baseStart_3705251 baseEnd_3705251 := by
    simpa [prefixWord, tailWord_3705251, baseEnd_3705251] using wordTrace_append hprefix tailTrace_3705251
  have hstable : (prefixWord ++ tailWord_3705251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705251).length < 2 ^ (prefixWord ++ tailWord_3705251).sum := by decide
  have hdescent : baseEnd_3705251 < baseStart_3705251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705317 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_3705317 : Nat := 118140960795 + 3705317 * 2 ^ 59
def prefixEnd_3705317 : Nat := 4983230072969 + 3 ^ 40 * 3705317 * 2
def baseEnd_3705317 : Nat := 1268405732183723109264709

theorem tailTrace_3705317 : CollatzResearch.WordTrace tailWord_3705317 prefixEnd_3705317 1268405732183723109264709 := by
  unfold tailWord_3705317
  simp only [CollatzResearch.WordTrace]
  refine ⟨135144013517276801607514205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90096009011517867738342803 135144013517276801607514205)
  ·
    refine ⟨50679005068978800602817827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135144013517276801607514205 50679005068978800602817827)
    ·
      refine ⟨76018507603468200904226741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50679005068978800602817827 76018507603468200904226741)
      ·
        refine ⟨7126735087825143834771257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76018507603468200904226741 7126735087825143834771257)
        ·
          refine ⟨5345051315868857876078443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7126735087825143834771257 5345051315868857876078443)
          ·
            refine ⟨8017576973803286814117665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345051315868857876078443 8017576973803286814117665)
            ·
              refine ⟨6013182730352465110588249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8017576973803286814117665 6013182730352465110588249)
              ·
                refine ⟨4509887047764348832941187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6013182730352465110588249 4509887047764348832941187)
                ·
                  refine ⟨6764830571646523249411781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509887047764348832941187 6764830571646523249411781)
                  ·
                    refine ⟨1268405732183723109264709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764830571646523249411781 1268405732183723109264709)
                    ·
                      rfl

theorem cell22_3705317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_3705317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705317 prefixEnd_3705317 := by exact prefixLift 3705317
  have htrace : WordTrace (prefixWord ++ tailWord_3705317) baseStart_3705317 baseEnd_3705317 := by
    simpa [prefixWord, tailWord_3705317, baseEnd_3705317] using wordTrace_append hprefix tailTrace_3705317
  have hstable : (prefixWord ++ tailWord_3705317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705317).length < 2 ^ (prefixWord ++ tailWord_3705317).sum := by decide
  have hdescent : baseEnd_3705317 < baseStart_3705317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705328 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_3705328 : Nat := 118140960795 + 3705328 * 2 ^ 59
def prefixEnd_3705328 : Nat := 4983230072969 + 3 ^ 40 * 3705328 * 2
def baseEnd_3705328 : Nat := 1268409497708522747239675

theorem tailTrace_3705328 : CollatzResearch.WordTrace tailWord_3705328 prefixEnd_3705328 1268409497708522747239675 := by
  unfold tailWord_3705328
  simp only [CollatzResearch.WordTrace]
  refine ⟨67572207360118475243082319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90096276480157966990776425 67572207360118475243082319)
  ·
    refine ⟨101358311040177712864623479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67572207360118475243082319 101358311040177712864623479)
    ·
      refine ⟨152037466560266569296935219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101358311040177712864623479 152037466560266569296935219)
      ·
        refine ⟨228056199840399853945402829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152037466560266569296935219 228056199840399853945402829)
        ·
          refine ⟨85521074940149945229526061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228056199840399853945402829 85521074940149945229526061)
          ·
            refine ⟨32070403102556229461072273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85521074940149945229526061 32070403102556229461072273)
            ·
              refine ⟨24052802326917172095804205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32070403102556229461072273 24052802326917172095804205)
              ·
                refine ⟨9019800872593939535926577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24052802326917172095804205 9019800872593939535926577)
                ·
                  refine ⟨6764850654445454651944933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9019800872593939535926577 6764850654445454651944933)
                  ·
                    refine ⟨1268409497708522747239675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764850654445454651944933 1268409497708522747239675)
                    ·
                      rfl

theorem cell22_3705328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_3705328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705328 prefixEnd_3705328 := by exact prefixLift 3705328
  have htrace : WordTrace (prefixWord ++ tailWord_3705328) baseStart_3705328 baseEnd_3705328 := by
    simpa [prefixWord, tailWord_3705328, baseEnd_3705328] using wordTrace_append hprefix tailTrace_3705328
  have hstable : (prefixWord ++ tailWord_3705328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705328).length < 2 ^ (prefixWord ++ tailWord_3705328).sum := by decide
  have hdescent : baseEnd_3705328 < baseStart_3705328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705345 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3705345 : Nat := 118140960795 + 3705345 * 2 ^ 59
def prefixEnd_3705345 : Nat := 4983230072969 + 3 ^ 40 * 3705345 * 2
def baseEnd_3705345 : Nat := 1268415317155940369564623

theorem tailTrace_3705345 : CollatzResearch.WordTrace tailWord_3705345 prefixEnd_3705345 1268415317155940369564623 := by
  unfold tailWord_3705345
  simp only [CollatzResearch.WordTrace]
  refine ⟨135145034761175362389533489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90096689840783574926355659 135145034761175362389533489)
  ·
    refine ⟨101358776070881521792150117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135145034761175362389533489 101358776070881521792150117)
    ·
      refine ⟨19004770513290285336028147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101358776070881521792150117 19004770513290285336028147)
      ·
        refine ⟨28507155769935428004042221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19004770513290285336028147 28507155769935428004042221)
        ·
          refine ⟨10690183413725785501515833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28507155769935428004042221 10690183413725785501515833)
          ·
            refine ⟨8017637560294339126136875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10690183413725785501515833 8017637560294339126136875)
            ·
              refine ⟨12026456340441508689205313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017637560294339126136875 12026456340441508689205313)
              ·
                refine ⟨9019842255331131516903985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12026456340441508689205313 9019842255331131516903985)
                ·
                  refine ⟨6764881691498348637677989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9019842255331131516903985 6764881691498348637677989)
                  ·
                    refine ⟨1268415317155940369564623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764881691498348637677989 1268415317155940369564623)
                    ·
                      rfl

theorem cell22_3705345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3705345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705345 prefixEnd_3705345 := by exact prefixLift 3705345
  have htrace : WordTrace (prefixWord ++ tailWord_3705345) baseStart_3705345 baseEnd_3705345 := by
    simpa [prefixWord, tailWord_3705345, baseEnd_3705345] using wordTrace_append hprefix tailTrace_3705345
  have hstable : (prefixWord ++ tailWord_3705345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705345).length < 2 ^ (prefixWord ++ tailWord_3705345).sum := by decide
  have hdescent : baseEnd_3705345 < baseStart_3705345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705364 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3705364 : Nat := 118140960795 + 3705364 * 2 ^ 59
def prefixEnd_3705364 : Nat := 4983230072969 + 3 ^ 40 * 3705364 * 2
def baseEnd_3705364 : Nat := 1268421821244230653339565

theorem tailTrace_3705364 : CollatzResearch.WordTrace tailWord_3705364 prefixEnd_3705364 1268421821244230653339565 := by
  unfold tailWord_3705364
  simp only [CollatzResearch.WordTrace]
  refine ⟨67572863874053264317237573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90097151832071019089650097 67572863874053264317237573)
  ·
    refine ⟨12669911976384987059482045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67572863874053264317237573 12669911976384987059482045)
    ·
      refine ⟨4751216991144370147305767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12669911976384987059482045 4751216991144370147305767)
      ·
        refine ⟨7126825486716555220958651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751216991144370147305767 7126825486716555220958651)
        ·
          refine ⟨10690238230074832831437977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7126825486716555220958651 10690238230074832831437977)
          ·
            refine ⟨8017678672556124623578483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10690238230074832831437977 8017678672556124623578483)
            ·
              refine ⟨12026518008834186935367725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017678672556124623578483 12026518008834186935367725)
              ·
                refine ⟨4509944253312820100762897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12026518008834186935367725 4509944253312820100762897)
                ·
                  refine ⟨3382458189984615075572173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4509944253312820100762897 3382458189984615075572173)
                  ·
                    refine ⟨1268421821244230653339565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382458189984615075572173 1268421821244230653339565)
                    ·
                      rfl

theorem cell22_3705364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3705364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705364 prefixEnd_3705364 := by exact prefixLift 3705364
  have htrace : WordTrace (prefixWord ++ tailWord_3705364) baseStart_3705364 baseEnd_3705364 := by
    simpa [prefixWord, tailWord_3705364, baseEnd_3705364] using wordTrace_append hprefix tailTrace_3705364
  have hstable : (prefixWord ++ tailWord_3705364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705364).length < 2 ^ (prefixWord ++ tailWord_3705364).sum := by decide
  have hdescent : baseEnd_3705364 < baseStart_3705364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705405 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3705405 : Nat := 118140960795 + 3705405 * 2 ^ 59
def prefixEnd_3705405 : Nat := 4983230072969 + 3 ^ 40 * 3705405 * 2
def baseEnd_3705405 : Nat := 422811952127373404354813

theorem tailTrace_3705405 : CollatzResearch.WordTrace tailWord_3705405 prefixEnd_3705405 422811952127373404354813 := by
  unfold tailWord_3705405
  simp only [CollatzResearch.WordTrace]
  refine ⟨135147223140957992636717669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90098148760638661757811779 135147223140957992636717669)
  ·
    refine ⟨25340104338929623619384563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135147223140957992636717669 25340104338929623619384563)
    ·
      refine ⟨38010156508394435429076845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25340104338929623619384563 38010156508394435429076845)
      ·
        refine ⟨14253808690647913285903817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38010156508394435429076845 14253808690647913285903817)
        ·
          refine ⟨10690356517985934964427863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14253808690647913285903817 10690356517985934964427863)
          ·
            refine ⟨16035534776978902446641795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10690356517985934964427863 16035534776978902446641795)
            ·
              refine ⟨24053302165468353669962693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16035534776978902446641795 24053302165468353669962693)
              ·
                refine ⟨4509994156025316313118005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24053302165468353669962693 4509994156025316313118005)
                ·
                  refine ⟨422811952127373404354813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4509994156025316313118005 422811952127373404354813)
                  ·
                    rfl

theorem cell22_3705405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3705405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705405 prefixEnd_3705405 := by exact prefixLift 3705405
  have htrace : WordTrace (prefixWord ++ tailWord_3705405) baseStart_3705405 baseEnd_3705405 := by
    simpa [prefixWord, tailWord_3705405, baseEnd_3705405] using wordTrace_append hprefix tailTrace_3705405
  have hstable : (prefixWord ++ tailWord_3705405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705405).length < 2 ^ (prefixWord ++ tailWord_3705405).sum := by decide
  have hdescent : baseEnd_3705405 < baseStart_3705405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705409 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3705409 : Nat := 118140960795 + 3705409 * 2 ^ 59
def prefixEnd_3705409 : Nat := 4983230072969 + 3 ^ 40 * 3705409 * 2
def baseEnd_3705409 : Nat := 1268437225663865535964427

theorem tailTrace_3705409 : CollatzResearch.WordTrace tailWord_3705409 prefixEnd_3705409 1268437225663865535964427 := by
  unfold tailWord_3705409
  simp only [CollatzResearch.WordTrace]
  refine ⟨135147369032943501319863281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90098246021962334213242187 135147369032943501319863281)
  ·
    refine ⟨101360526774707625989897461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135147369032943501319863281 101360526774707625989897461)
    ·
      refine ⟨9502549385128839936552887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101360526774707625989897461 9502549385128839936552887)
      ·
        refine ⟨14253824077693259904829331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9502549385128839936552887 14253824077693259904829331)
        ·
          refine ⟨21380736116539889857243997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14253824077693259904829331 21380736116539889857243997)
          ·
            refine ⟨8017776043702458696466499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21380736116539889857243997 8017776043702458696466499)
            ·
              refine ⟨12026664065553688044699749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017776043702458696466499 12026664065553688044699749)
              ·
                refine ⟨2254999512291316508381203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12026664065553688044699749 2254999512291316508381203)
                ·
                  refine ⟨3382499268436974762571805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254999512291316508381203 3382499268436974762571805)
                  ·
                    refine ⟨1268437225663865535964427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382499268436974762571805 1268437225663865535964427)
                    ·
                      rfl

theorem cell22_3705409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3705409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705409 prefixEnd_3705409 := by exact prefixLift 3705409
  have htrace : WordTrace (prefixWord ++ tailWord_3705409) baseStart_3705409 baseEnd_3705409 := by
    simpa [prefixWord, tailWord_3705409, baseEnd_3705409] using wordTrace_append hprefix tailTrace_3705409
  have hstable : (prefixWord ++ tailWord_3705409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705409).length < 2 ^ (prefixWord ++ tailWord_3705409).sum := by decide
  have hdescent : baseEnd_3705409 < baseStart_3705409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705452 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_3705452 : Nat := 118140960795 + 3705452 * 2 ^ 59
def prefixEnd_3705452 : Nat := 4983230072969 + 3 ^ 40 * 3705452 * 2
def baseEnd_3705452 : Nat := 1268451945442627757139295

theorem tailTrace_3705452 : CollatzResearch.WordTrace tailWord_3705452 prefixEnd_3705452 1268451945442627757139295 := by
  unfold tailWord_3705452
  simp only [CollatzResearch.WordTrace]
  refine ⟨67574468685893859831839305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90099291581191813109119073 67574468685893859831839305)
  ·
    refine ⟨50680851514420394873879479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67574468685893859831839305 50680851514420394873879479)
    ·
      refine ⟨76021277271630592310819219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50680851514420394873879479 76021277271630592310819219)
      ·
        refine ⟨114031915907445888466228829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76021277271630592310819219 114031915907445888466228829)
        ·
          refine ⟨42761968465292208174835811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114031915907445888466228829 42761968465292208174835811)
          ·
            refine ⟨64142952697938312262253717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42761968465292208174835811 64142952697938312262253717)
            ·
              refine ⟨3006700907715858387293143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64142952697938312262253717 3006700907715858387293143)
              ·
                refine ⟨4510051361573787580939715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006700907715858387293143 4510051361573787580939715)
                ·
                  refine ⟨6765077042360681371409573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510051361573787580939715 6765077042360681371409573)
                  ·
                    refine ⟨1268451945442627757139295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765077042360681371409573 1268451945442627757139295)
                    ·
                      rfl

theorem cell22_3705452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_3705452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705452 prefixEnd_3705452 := by exact prefixLift 3705452
  have htrace : WordTrace (prefixWord ++ tailWord_3705452) baseStart_3705452 baseEnd_3705452 := by
    simpa [prefixWord, tailWord_3705452, baseEnd_3705452] using wordTrace_append hprefix tailTrace_3705452
  have hstable : (prefixWord ++ tailWord_3705452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705452).length < 2 ^ (prefixWord ++ tailWord_3705452).sum := by decide
  have hdescent : baseEnd_3705452 < baseStart_3705452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705585 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 6]
def baseStart_3705585 : Nat := 118140960795 + 3705585 * 2 ^ 59
def prefixEnd_3705585 : Nat := 4983230072969 + 3 ^ 40 * 3705585 * 2
def baseEnd_3705585 : Nat := 422832491353553247854629

theorem tailTrace_3705585 : CollatzResearch.WordTrace tailWord_3705585 prefixEnd_3705585 422832491353553247854629 := by
  unfold tailWord_3705585
  simp only [CollatzResearch.WordTrace]
  refine ⟨135153788280305883378270209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90102525520203922252180139 135153788280305883378270209)
  ·
    refine ⟨101365341210229412533702657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135153788280305883378270209 101365341210229412533702657)
    ·
      refine ⟨76024005907672059400276993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101365341210229412533702657 76024005907672059400276993)
      ·
        refine ⟨57018004430754044550207745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76024005907672059400276993 57018004430754044550207745)
        ·
          refine ⟨42763503323065533412655809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57018004430754044550207745 42763503323065533412655809)
          ·
            refine ⟨32072627492299150059491857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42763503323065533412655809 32072627492299150059491857)
            ·
              refine ⟨24054470619224362544618893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32072627492299150059491857 24054470619224362544618893)
              ·
                refine ⟨9020426482209135954232085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24054470619224362544618893 9020426482209135954232085)
                ·
                  refine ⟨422832491353553247854629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9020426482209135954232085 422832491353553247854629)
                  ·
                    rfl

theorem cell22_3705585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_3705585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705585 prefixEnd_3705585 := by exact prefixLift 3705585
  have htrace : WordTrace (prefixWord ++ tailWord_3705585) baseStart_3705585 baseEnd_3705585 := by
    simpa [prefixWord, tailWord_3705585, baseEnd_3705585] using wordTrace_append hprefix tailTrace_3705585
  have hstable : (prefixWord ++ tailWord_3705585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705585).length < 2 ^ (prefixWord ++ tailWord_3705585).sum := by decide
  have hdescent : baseEnd_3705585 < baseStart_3705585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705602 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3705602 : Nat := 118140960795 + 3705602 * 2 ^ 59
def prefixEnd_3705602 : Nat := 4983230072969 + 3 ^ 40 * 3705602 * 2
def baseEnd_3705602 : Nat := 422834431169359121962945

theorem tailTrace_3705602 : CollatzResearch.WordTrace tailWord_3705602 prefixEnd_3705602 422834431169359121962945 := by
  unfold tailWord_3705602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33788602080311073820409765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90102938880829530187759373 33788602080311073820409765)
  ·
    refine ⟨6335362890058326341326831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33788602080311073820409765 6335362890058326341326831)
    ·
      refine ⟨9503044335087489511990247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6335362890058326341326831 9503044335087489511990247)
      ·
        refine ⟨14254566502631234267985371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9503044335087489511990247 14254566502631234267985371)
        ·
          refine ⟨21381849753946851401978057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14254566502631234267985371 21381849753946851401978057)
          ·
            refine ⟨16036387315460138551483543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21381849753946851401978057 16036387315460138551483543)
            ·
              refine ⟨24054580973190207827225315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16036387315460138551483543 24054580973190207827225315)
              ·
                refine ⟨36081871459785311740837973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24054580973190207827225315 36081871459785311740837973)
                ·
                  refine ⟨422834431169359121962945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36081871459785311740837973 422834431169359121962945)
                  ·
                    rfl

theorem cell22_3705602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3705602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705602 prefixEnd_3705602 := by exact prefixLift 3705602
  have htrace : WordTrace (prefixWord ++ tailWord_3705602) baseStart_3705602 baseEnd_3705602 := by
    simpa [prefixWord, tailWord_3705602, baseEnd_3705602] using wordTrace_append hprefix tailTrace_3705602
  have hstable : (prefixWord ++ tailWord_3705602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705602).length < 2 ^ (prefixWord ++ tailWord_3705602).sum := by decide
  have hdescent : baseEnd_3705602 < baseStart_3705602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705615 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 1, 6]
def baseStart_3705615 : Nat := 118140960795 + 3705615 * 2 ^ 59
def prefixEnd_3705615 : Nat := 4983230072969 + 3 ^ 40 * 3705615 * 2
def baseEnd_3705615 : Nat := 1268507743673749665313795

theorem tailTrace_3705615 : CollatzResearch.WordTrace tailWord_3705615 prefixEnd_3705615 1268507743673749665313795 := by
  unfold tailWord_3705615
  simp only [CollatzResearch.WordTrace]
  refine ⟨135154882470197198501862299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90103254980131465667908199 135154882470197198501862299)
  ·
    refine ⟨202732323705295797752793449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135154882470197198501862299 202732323705295797752793449)
    ·
      refine ⟨152049242778971848314595087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202732323705295797752793449 152049242778971848314595087)
      ·
        refine ⟨228073864168457772471892631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152049242778971848314595087 228073864168457772471892631)
        ·
          refine ⟨342110796252686658707838947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228073864168457772471892631 342110796252686658707838947)
          ·
            refine ⟨513166194379029988061758421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342110796252686658707838947 513166194379029988061758421)
            ·
              refine ⟨12027332680758515345197463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 513166194379029988061758421 12027332680758515345197463)
              ·
                refine ⟨18040999021137773017796195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027332680758515345197463 18040999021137773017796195)
                ·
                  refine ⟨27061498531706659526694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18040999021137773017796195 27061498531706659526694293)
                  ·
                    refine ⟨1268507743673749665313795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27061498531706659526694293 1268507743673749665313795)
                    ·
                      rfl

theorem cell22_3705615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_3705615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705615 prefixEnd_3705615 := by exact prefixLift 3705615
  have htrace : WordTrace (prefixWord ++ tailWord_3705615) baseStart_3705615 baseEnd_3705615 := by
    simpa [prefixWord, tailWord_3705615, baseEnd_3705615] using wordTrace_append hprefix tailTrace_3705615
  have hstable : (prefixWord ++ tailWord_3705615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705615).length < 2 ^ (prefixWord ++ tailWord_3705615).sum := by decide
  have hdescent : baseEnd_3705615 < baseStart_3705615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705634 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3705634 : Nat := 118140960795 + 3705634 * 2 ^ 59
def prefixEnd_3705634 : Nat := 4983230072969 + 3 ^ 40 * 3705634 * 2
def baseEnd_3705634 : Nat := 1268514247762039949088737

theorem tailTrace_3705634 : CollatzResearch.WordTrace tailWord_3705634 prefixEnd_3705634 1268514247762039949088737 := by
  unfold tailWord_3705634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33788893864282091186700989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90103716971418909831202637 33788893864282091186700989)
  ·
    refine ⟨12670835199105784195012871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33788893864282091186700989 12670835199105784195012871)
    ·
      refine ⟨19006252798658676292519307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12670835199105784195012871 19006252798658676292519307)
      ·
        refine ⟨28509379197988014438778961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19006252798658676292519307 28509379197988014438778961)
        ·
          refine ⟨21382034398491010829084221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28509379197988014438778961 21382034398491010829084221)
          ·
            refine ⟨8018262899434129060906583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21382034398491010829084221 8018262899434129060906583)
            ·
              refine ⟨12027394349151193591359875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018262899434129060906583 12027394349151193591359875)
              ·
                refine ⟨18041091523726790387039813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027394349151193591359875 18041091523726790387039813)
                ·
                  refine ⟨3382704660698773197569965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18041091523726790387039813 3382704660698773197569965)
                  ·
                    refine ⟨1268514247762039949088737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382704660698773197569965 1268514247762039949088737)
                    ·
                      rfl

theorem cell22_3705634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3705634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705634 prefixEnd_3705634 := by exact prefixLift 3705634
  have htrace : WordTrace (prefixWord ++ tailWord_3705634) baseStart_3705634 baseEnd_3705634 := by
    simpa [prefixWord, tailWord_3705634, baseEnd_3705634] using wordTrace_append hprefix tailTrace_3705634
  have hstable : (prefixWord ++ tailWord_3705634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705634).length < 2 ^ (prefixWord ++ tailWord_3705634).sum := by decide
  have hdescent : baseEnd_3705634 < baseStart_3705634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705651 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 2, 3]
def baseStart_3705651 : Nat := 118140960795 + 3705651 * 2 ^ 59
def prefixEnd_3705651 : Nat := 4983230072969 + 3 ^ 40 * 3705651 * 2
def baseEnd_3705651 : Nat := 1268520067209457571413685

theorem tailTrace_3705651 : CollatzResearch.WordTrace tailWord_3705651 prefixEnd_3705651 1268520067209457571413685 := by
  unfold tailWord_3705651
  simp only [CollatzResearch.WordTrace]
  refine ⟨135156195498066776650172807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90104130332044517766781871 135156195498066776650172807)
  ·
    refine ⟨202734293247100164975259211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135156195498066776650172807 202734293247100164975259211)
    ·
      refine ⟨304101439870650247462888817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202734293247100164975259211 304101439870650247462888817)
      ·
        refine ⟨228076079902987685597166613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304101439870650247462888817 228076079902987685597166613)
        ·
          refine ⟨10691066245452547762367185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228076079902987685597166613 10691066245452547762367185)
          ·
            refine ⟨8018299684089410821775389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10691066245452547762367185 8018299684089410821775389)
            ·
              refine ⟨3006862381533529058165771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8018299684089410821775389 3006862381533529058165771)
              ·
                refine ⟨4510293572300293587248657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006862381533529058165771 4510293572300293587248657)
                ·
                  refine ⟨3382720179225220190436493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510293572300293587248657 3382720179225220190436493)
                  ·
                    refine ⟨1268520067209457571413685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382720179225220190436493 1268520067209457571413685)
                    ·
                      rfl

theorem cell22_3705651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 3].length) (baseStart_3705651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705651 prefixEnd_3705651 := by exact prefixLift 3705651
  have htrace : WordTrace (prefixWord ++ tailWord_3705651) baseStart_3705651 baseEnd_3705651 := by
    simpa [prefixWord, tailWord_3705651, baseEnd_3705651] using wordTrace_append hprefix tailTrace_3705651
  have hstable : (prefixWord ++ tailWord_3705651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705651).length < 2 ^ (prefixWord ++ tailWord_3705651).sum := by decide
  have hdescent : baseEnd_3705651 < baseStart_3705651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705670 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3705670 : Nat := 118140960795 + 3705670 * 2 ^ 59
def prefixEnd_3705670 : Nat := 4983230072969 + 3 ^ 40 * 3705670 * 2
def baseEnd_3705670 : Nat := 422842190432582618396209

theorem tailTrace_3705670 : CollatzResearch.WordTrace tailWord_3705670 prefixEnd_3705670 422842190432582618396209 := by
  unfold tailWord_3705670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223652765156185715472327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90104592323331961930076309 4223652765156185715472327)
  ·
    refine ⟨6335479147734278573208491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223652765156185715472327 6335479147734278573208491)
    ·
      refine ⟨9503218721601417859812737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6335479147734278573208491 9503218721601417859812737)
      ·
        refine ⟨7127414041201063394859553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9503218721601417859812737 7127414041201063394859553)
        ·
          refine ⟨5345560530900797546144665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7127414041201063394859553 5345560530900797546144665)
          ·
            refine ⟨4009170398175598159608499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5345560530900797546144665 4009170398175598159608499)
            ·
              refine ⟨6013755597263397239412749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009170398175598159608499 6013755597263397239412749)
              ·
                refine ⟨2255158348973773964779781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6013755597263397239412749 2255158348973773964779781)
                ·
                  refine ⟨422842190432582618396209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255158348973773964779781 422842190432582618396209)
                  ·
                    rfl

theorem cell22_3705670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3705670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705670 prefixEnd_3705670 := by exact prefixLift 3705670
  have htrace : WordTrace (prefixWord ++ tailWord_3705670) baseStart_3705670 baseEnd_3705670 := by
    simpa [prefixWord, tailWord_3705670, baseEnd_3705670] using wordTrace_append hprefix tailTrace_3705670
  have hstable : (prefixWord ++ tailWord_3705670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705670).length < 2 ^ (prefixWord ++ tailWord_3705670).sum := by decide
  have hdescent : baseEnd_3705670 < baseStart_3705670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705705 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_3705705 : Nat := 118140960795 + 3705705 * 2 ^ 59
def prefixEnd_3705705 : Nat := 4983230072969 + 3 ^ 40 * 3705705 * 2
def baseEnd_3705705 : Nat := 1268538552513019430563519

theorem tailTrace_3705705 : CollatzResearch.WordTrace tailWord_3705705 prefixEnd_3705705 1268538552513019430563519 := by
  unfold tailWord_3705705
  simp only [CollatzResearch.WordTrace]
  refine ⟨135158165039871143872638569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90105443359914095915092379 135158165039871143872638569)
  ·
    refine ⟨101368623779903357904478927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135158165039871143872638569 101368623779903357904478927)
    ·
      refine ⟨152052935669855036856718391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101368623779903357904478927 152052935669855036856718391)
      ·
        refine ⟨228079403504782555285077587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152052935669855036856718391 228079403504782555285077587)
        ·
          refine ⟨342119105257173832927616381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228079403504782555285077587 342119105257173832927616381)
          ·
            refine ⟨128294664471440187347856143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342119105257173832927616381 128294664471440187347856143)
            ·
              refine ⟨192441996707160281021784215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128294664471440187347856143 192441996707160281021784215)
              ·
                refine ⟨288662995060740421532676323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192441996707160281021784215 288662995060740421532676323)
                ·
                  refine ⟨432994492591110632299014485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288662995060740421532676323 432994492591110632299014485)
                  ·
                    refine ⟨1268538552513019430563519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 432994492591110632299014485 1268538552513019430563519)
                    ·
                      rfl

theorem cell22_3705705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_3705705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705705 prefixEnd_3705705 := by exact prefixLift 3705705
  have htrace : WordTrace (prefixWord ++ tailWord_3705705) baseStart_3705705 baseEnd_3705705 := by
    simpa [prefixWord, tailWord_3705705, baseEnd_3705705] using wordTrace_append hprefix tailTrace_3705705
  have hstable : (prefixWord ++ tailWord_3705705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705705).length < 2 ^ (prefixWord ++ tailWord_3705705).sum := by decide
  have hdescent : baseEnd_3705705 < baseStart_3705705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705769 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_3705769 : Nat := 118140960795 + 3705769 * 2 ^ 59
def prefixEnd_3705769 : Nat := 4983230072969 + 3 ^ 40 * 3705769 * 2
def baseEnd_3705769 : Nat := 1268560461020944596963323

theorem tailTrace_3705769 : CollatzResearch.WordTrace tailWord_3705769 prefixEnd_3705769 1268560461020944596963323 := by
  unfold tailWord_3705769
  simp only [CollatzResearch.WordTrace]
  refine ⟨135160499311639282802968361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90106999541092855201978907 135160499311639282802968361)
  ·
    refine ⟨101370374483729462102226271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135160499311639282802968361 101370374483729462102226271)
    ·
      refine ⟨152055561725594193153339407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101370374483729462102226271 152055561725594193153339407)
      ·
        refine ⟨228083342588391289730009111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152055561725594193153339407 228083342588391289730009111)
        ·
          refine ⟨342125013882586934595013667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228083342588391289730009111 342125013882586934595013667)
          ·
            refine ⟨513187520823880401892520501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342125013882586934595013667 513187520823880401892520501)
            ·
              refine ⟨48111330077238787677423797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 513187520823880401892520501 48111330077238787677423797)
              ·
                refine ⟨4510437194741136344758481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48111330077238787677423797 4510437194741136344758481)
                ·
                  refine ⟨3382827896055852258568861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510437194741136344758481 3382827896055852258568861)
                  ·
                    refine ⟨1268560461020944596963323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382827896055852258568861 1268560461020944596963323)
                    ·
                      rfl

theorem cell22_3705769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_3705769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705769 prefixEnd_3705769 := by exact prefixLift 3705769
  have htrace : WordTrace (prefixWord ++ tailWord_3705769) baseStart_3705769 baseEnd_3705769 := by
    simpa [prefixWord, tailWord_3705769, baseEnd_3705769] using wordTrace_append hprefix tailTrace_3705769
  have hstable : (prefixWord ++ tailWord_3705769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705769).length < 2 ^ (prefixWord ++ tailWord_3705769).sum := by decide
  have hdescent : baseEnd_3705769 < baseStart_3705769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705784 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_3705784 : Nat := 118140960795 + 3705784 * 2 ^ 59
def prefixEnd_3705784 : Nat := 4983230072969 + 3 ^ 40 * 3705784 * 2
def baseEnd_3705784 : Nat := 1268565595827489557838277

theorem tailTrace_3705784 : CollatzResearch.WordTrace tailWord_3705784 prefixEnd_3705784 1268565595827489557838277 := by
  unfold tailWord_3705784
  simp only [CollatzResearch.WordTrace]
  refine ⟨67580523203292470182382203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90107364271056626909842937 67580523203292470182382203)
  ·
    refine ⟨101370784804938705273573305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67580523203292470182382203 101370784804938705273573305)
    ·
      refine ⟨76028088603704028955179979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101370784804938705273573305 76028088603704028955179979)
      ·
        refine ⟨114042132905556043432769969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76028088603704028955179979 114042132905556043432769969)
        ·
          refine ⟨85531599679167032574577477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114042132905556043432769969 85531599679167032574577477)
          ·
            refine ⟨16037174939843818607733277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85531599679167032574577477 16037174939843818607733277)
            ·
              refine ⟨6013940602441431977899979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16037174939843818607733277 6013940602441431977899979)
              ·
                refine ⟨9020910903662147966849969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013940602441431977899979 9020910903662147966849969)
                ·
                  refine ⟨6765683177746610975137477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9020910903662147966849969 6765683177746610975137477)
                  ·
                    refine ⟨1268565595827489557838277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765683177746610975137477 1268565595827489557838277)
                    ·
                      rfl

theorem cell22_3705784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_3705784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705784 prefixEnd_3705784 := by exact prefixLift 3705784
  have htrace : WordTrace (prefixWord ++ tailWord_3705784) baseStart_3705784 baseEnd_3705784 := by
    simpa [prefixWord, tailWord_3705784, baseEnd_3705784] using wordTrace_append hprefix tailTrace_3705784
  have hstable : (prefixWord ++ tailWord_3705784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705784).length < 2 ^ (prefixWord ++ tailWord_3705784).sum := by decide
  have hdescent : baseEnd_3705784 < baseStart_3705784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705805 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3705805 : Nat := 118140960795 + 3705805 * 2 ^ 59
def prefixEnd_3705805 : Nat := 4983230072969 + 3 ^ 40 * 3705805 * 2
def baseEnd_3705805 : Nat := 422857594852217501021071

theorem tailTrace_3705805 : CollatzResearch.WordTrace tailWord_3705805 prefixEnd_3705805 422857594852217501021071 := by
  unfold tailWord_3705805
  simp only [CollatzResearch.WordTrace]
  refine ⟨135161812339508860951278869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90107874893005907300852579 135161812339508860951278869)
  ·
    refine ⟨6335709953414477857091197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135161812339508860951278869 6335709953414477857091197)
    ·
      refine ⟨2375891232530429196409199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6335709953414477857091197 2375891232530429196409199)
      ·
        refine ⟨3563836848795643794613799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375891232530429196409199 3563836848795643794613799)
        ·
          refine ⟨5345755273193465691920699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563836848795643794613799 5345755273193465691920699)
          ·
            refine ⟨8018632909790198537881049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345755273193465691920699 8018632909790198537881049)
            ·
              refine ⟨6013974682342648903410787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8018632909790198537881049 6013974682342648903410787)
              ·
                refine ⟨9020962023513973355116181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013974682342648903410787 9020962023513973355116181)
                ·
                  refine ⟨422857594852217501021071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9020962023513973355116181 422857594852217501021071)
                  ·
                    rfl

theorem cell22_3705805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3705805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705805 prefixEnd_3705805 := by exact prefixLift 3705805
  have htrace : WordTrace (prefixWord ++ tailWord_3705805) baseStart_3705805 baseEnd_3705805 := by
    simpa [prefixWord, tailWord_3705805, baseEnd_3705805] using wordTrace_append hprefix tailTrace_3705805
  have hstable : (prefixWord ++ tailWord_3705805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705805).length < 2 ^ (prefixWord ++ tailWord_3705805).sum := by decide
  have hdescent : baseEnd_3705805 < baseStart_3705805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705831 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3705831 : Nat := 118140960795 + 3705831 * 2 ^ 59
def prefixEnd_3705831 : Nat := 4983230072969 + 3 ^ 40 * 3705831 * 2
def baseEnd_3705831 : Nat := 1268581684887997101913133

theorem tailTrace_3705831 : CollatzResearch.WordTrace tailWord_3705831 prefixEnd_3705831 1268581684887997101913133 := by
  unfold tailWord_3705831
  simp only [CollatzResearch.WordTrace]
  refine ⟨135162760637414667391725347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90108507091609778261150231 135162760637414667391725347)
  ·
    refine ⟨202744140956122001087588021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135162760637414667391725347 202744140956122001087588021)
    ·
      refine ⟨19007263214636437601961377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202744140956122001087588021 19007263214636437601961377)
      ·
        refine ⟨14255447410977328201471033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19007263214636437601961377 14255447410977328201471033)
        ·
          refine ⟨10691585558232996151103275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14255447410977328201471033 10691585558232996151103275)
          ·
            refine ⟨16037378337349494226654913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10691585558232996151103275 16037378337349494226654913)
            ·
              refine ⟨12028033753012120669991185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16037378337349494226654913 12028033753012120669991185)
              ·
                refine ⟨9021025314759090502493389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028033753012120669991185 9021025314759090502493389)
                ·
                  refine ⟨3382884493034658938435021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9021025314759090502493389 3382884493034658938435021)
                  ·
                    refine ⟨1268581684887997101913133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382884493034658938435021 1268581684887997101913133)
                    ·
                      rfl

theorem cell22_3705831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3705831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705831 prefixEnd_3705831 := by exact prefixLift 3705831
  have htrace : WordTrace (prefixWord ++ tailWord_3705831) baseStart_3705831 baseEnd_3705831 := by
    simpa [prefixWord, tailWord_3705831, baseEnd_3705831] using wordTrace_append hprefix tailTrace_3705831
  have hstable : (prefixWord ++ tailWord_3705831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705831).length < 2 ^ (prefixWord ++ tailWord_3705831).sum := by decide
  have hdescent : baseEnd_3705831 < baseStart_3705831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705891 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 1, 4]
def baseStart_3705891 : Nat := 118140960795 + 3705891 * 2 ^ 59
def prefixEnd_3705891 : Nat := 4983230072969 + 3 ^ 40 * 3705891 * 2
def baseEnd_3705891 : Nat := 1268602224114176945412949

theorem tailTrace_3705891 : CollatzResearch.WordTrace tailWord_3705891 prefixEnd_3705891 1268602224114176945412949 := by
  unfold tailWord_3705891
  simp only [CollatzResearch.WordTrace]
  refine ⟨135164949017197297638909527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90109966011464865092606351 135164949017197297638909527)
  ·
    refine ⟨202747423525795946458364291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135164949017197297638909527 202747423525795946458364291)
    ·
      refine ⟨304121135288693919687546437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202747423525795946458364291 304121135288693919687546437)
      ·
        refine ⟨57022712866630109941414957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304121135288693919687546437 57022712866630109941414957)
        ·
          refine ⟨21383517324986291228030609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57022712866630109941414957 21383517324986291228030609)
          ·
            refine ⟨16037637993739718421022957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21383517324986291228030609 16037637993739718421022957)
            ·
              refine ⟨6014114247652394407883609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16037637993739718421022957 6014114247652394407883609)
              ·
                refine ⟨4510585685739295805912707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6014114247652394407883609 4510585685739295805912707)
                ·
                  refine ⟨6765878528608943708869061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510585685739295805912707 6765878528608943708869061)
                  ·
                    refine ⟨1268602224114176945412949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765878528608943708869061 1268602224114176945412949)
                    ·
                      rfl

theorem cell22_3705891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 4].length) (baseStart_3705891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705891 prefixEnd_3705891 := by exact prefixLift 3705891
  have htrace : WordTrace (prefixWord ++ tailWord_3705891) baseStart_3705891 baseEnd_3705891 := by
    simpa [prefixWord, tailWord_3705891, baseEnd_3705891] using wordTrace_append hprefix tailTrace_3705891
  have hstable : (prefixWord ++ tailWord_3705891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705891).length < 2 ^ (prefixWord ++ tailWord_3705891).sum := by decide
  have hdescent : baseEnd_3705891 < baseStart_3705891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705904 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_3705904 : Nat := 118140960795 + 3705904 * 2 ^ 59
def prefixEnd_3705904 : Nat := 4983230072969 + 3 ^ 40 * 3705904 * 2
def baseEnd_3705904 : Nat := 1268606674279849244837909

theorem tailTrace_3705904 : CollatzResearch.WordTrace tailWord_3705904 prefixEnd_3705904 1268606674279849244837909 := by
  unfold tailWord_3705904
  simp only [CollatzResearch.WordTrace]
  refine ⟨67582711583075100429566383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90110282110766800572755177 67582711583075100429566383)
  ·
    refine ⟨101374067374612650644349575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67582711583075100429566383 101374067374612650644349575)
    ·
      refine ⟨152061101061918975966524363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101374067374612650644349575 152061101061918975966524363)
      ·
        refine ⟨228091651592878463949786545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152061101061918975966524363 228091651592878463949786545)
        ·
          refine ⟨171068738694658847962339909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228091651592878463949786545 171068738694658847962339909)
          ·
            refine ⟨32075388505248533992938733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171068738694658847962339909 32075388505248533992938733)
            ·
              refine ⟨12028270689468200247352025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32075388505248533992938733 12028270689468200247352025)
              ·
                refine ⟨9021203017101150185514019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028270689468200247352025 9021203017101150185514019)
                ·
                  refine ⟨13531804525651725278271029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021203017101150185514019 13531804525651725278271029)
                  ·
                    refine ⟨1268606674279849244837909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13531804525651725278271029 1268606674279849244837909)
                    ·
                      rfl

theorem cell22_3705904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_3705904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705904 prefixEnd_3705904 := by exact prefixLift 3705904
  have htrace : WordTrace (prefixWord ++ tailWord_3705904) baseStart_3705904 baseEnd_3705904 := by
    simpa [prefixWord, tailWord_3705904, baseEnd_3705904] using wordTrace_append hprefix tailTrace_3705904
  have hstable : (prefixWord ++ tailWord_3705904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705904).length < 2 ^ (prefixWord ++ tailWord_3705904).sum := by decide
  have hdescent : baseEnd_3705904 < baseStart_3705904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705906 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_3705906 : Nat := 118140960795 + 3705906 * 2 ^ 59
def prefixEnd_3705906 : Nat := 4983230072969 + 3 ^ 40 * 3705906 * 2
def baseEnd_3705906 : Nat := 422869119640240635429301

theorem tailTrace_3705906 : CollatzResearch.WordTrace tailWord_3705906 prefixEnd_3705906 422869119640240635429301 := by
  unfold tailWord_3705906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33791374028035738800176393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90110330741428636800470381 33791374028035738800176393)
  ·
    refine ⟨25343530521026804100132295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33791374028035738800176393 25343530521026804100132295)
    ·
      refine ⟨38015295781540206150198443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25343530521026804100132295 38015295781540206150198443)
      ·
        refine ⟨57022943672310309225297665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38015295781540206150198443 57022943672310309225297665)
        ·
          refine ⟨42767207754232731918973249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57022943672310309225297665 42767207754232731918973249)
          ·
            refine ⟨32075405815674548939229937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42767207754232731918973249 32075405815674548939229937)
            ·
              refine ⟨24056554361755911704422453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32075405815674548939229937 24056554361755911704422453)
              ·
                refine ⟨2255301971414616722289605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24056554361755911704422453 2255301971414616722289605)
                ·
                  refine ⟨422869119640240635429301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255301971414616722289605 422869119640240635429301)
                  ·
                    rfl

theorem cell22_3705906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_3705906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705906 prefixEnd_3705906 := by exact prefixLift 3705906
  have htrace : WordTrace (prefixWord ++ tailWord_3705906) baseStart_3705906 baseEnd_3705906 := by
    simpa [prefixWord, tailWord_3705906, baseEnd_3705906] using wordTrace_append hprefix tailTrace_3705906
  have hstable : (prefixWord ++ tailWord_3705906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705906).length < 2 ^ (prefixWord ++ tailWord_3705906).sum := by decide
  have hdescent : baseEnd_3705906 < baseStart_3705906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3705938 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_3705938 : Nat := 118140960795 + 3705938 * 2 ^ 59
def prefixEnd_3705938 : Nat := 4983230072969 + 3 ^ 40 * 3705938 * 2
def baseEnd_3705938 : Nat := 1268618313174684489487805

theorem tailTrace_3705938 : CollatzResearch.WordTrace tailWord_3705938 prefixEnd_3705938 1268618313174684489487805 := by
  unfold tailWord_3705938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33791665812006756166467617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90111108832018016443913645 33791665812006756166467617)
  ·
    refine ⟨25343749359005067124850713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33791665812006756166467617 25343749359005067124850713)
    ·
      refine ⟨19007812019253800343638035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25343749359005067124850713 19007812019253800343638035)
      ·
        refine ⟨28511718028880700515457053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19007812019253800343638035 28511718028880700515457053)
        ·
          refine ⟨10691894260830262693296395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28511718028880700515457053 10691894260830262693296395)
          ·
            refine ⟨16037841391245394039944593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10691894260830262693296395 16037841391245394039944593)
            ·
              refine ⟨12028381043434045529958445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16037841391245394039944593 12028381043434045529958445)
              ·
                refine ⟨4510642891287767073734417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12028381043434045529958445 4510642891287767073734417)
                ·
                  refine ⟨3382982168465825305300813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510642891287767073734417 3382982168465825305300813)
                  ·
                    refine ⟨1268618313174684489487805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382982168465825305300813 1268618313174684489487805)
                    ·
                      rfl

theorem cell22_3705938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_3705938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3705938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3705938 prefixEnd_3705938 := by exact prefixLift 3705938
  have htrace : WordTrace (prefixWord ++ tailWord_3705938) baseStart_3705938 baseEnd_3705938 := by
    simpa [prefixWord, tailWord_3705938, baseEnd_3705938] using wordTrace_append hprefix tailTrace_3705938
  have hstable : (prefixWord ++ tailWord_3705938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3705938).length < 2 ^ (prefixWord ++ tailWord_3705938).sum := by decide
  have hdescent : baseEnd_3705938 < baseStart_3705938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3705938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706041 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 6]
def baseStart_3706041 : Nat := 118140960795 + 3706041 * 2 ^ 59
def prefixEnd_3706041 : Nat := 4983230072969 + 3 ^ 40 * 3706041 * 2
def baseEnd_3706041 : Nat := 422884524059875518054163

theorem tailTrace_3706041 : CollatzResearch.WordTrace tailWord_3706041 prefixEnd_3706041 422884524059875518054163 := by
  unfold tailWord_3706041
  simp only [CollatzResearch.WordTrace]
  refine ⟨135170419966653873256869977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90113613311102582171246651 135170419966653873256869977)
  ·
    refine ⟨101377814974990404942652483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135170419966653873256869977 101377814974990404942652483)
    ·
      refine ⟨152066722462485607413978725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101377814974990404942652483 152066722462485607413978725)
      ·
        refine ⟨28512510461716051390121011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152066722462485607413978725 28512510461716051390121011)
        ·
          refine ⟨42768765692574077085181517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28512510461716051390121011 42768765692574077085181517)
          ·
            refine ⟨16038287134715278906943069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42768765692574077085181517 16038287134715278906943069)
            ·
              refine ⟨6014357675518229590103651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16038287134715278906943069 6014357675518229590103651)
              ·
                refine ⟨9021536513277344385155477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014357675518229590103651 9021536513277344385155477)
                ·
                  refine ⟨422884524059875518054163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9021536513277344385155477 422884524059875518054163)
                  ·
                    rfl

theorem cell22_3706041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_3706041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706041 prefixEnd_3706041 := by exact prefixLift 3706041
  have htrace : WordTrace (prefixWord ++ tailWord_3706041) baseStart_3706041 baseEnd_3706041 := by
    simpa [prefixWord, tailWord_3706041, baseEnd_3706041] using wordTrace_append hprefix tailTrace_3706041
  have hstable : (prefixWord ++ tailWord_3706041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706041).length < 2 ^ (prefixWord ++ tailWord_3706041).sum := by decide
  have hdescent : baseEnd_3706041 < baseStart_3706041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706071 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 2, 4]
def baseStart_3706071 : Nat := 118140960795 + 3706071 * 2 ^ 59
def prefixEnd_3706071 : Nat := 4983230072969 + 3 ^ 40 * 3706071 * 2
def baseEnd_3706071 : Nat := 1268663841792716475912397

theorem tailTrace_3706071 : CollatzResearch.WordTrace tailWord_3706071 prefixEnd_3706071 1268663841792716475912397 := by
  unfold tailWord_3706071
  simp only [CollatzResearch.WordTrace]
  refine ⟨135171514156545188380462067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90114342771030125586974711 135171514156545188380462067)
  ·
    refine ⟨202757271234817782570693101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135171514156545188380462067 202757271234817782570693101)
    ·
      refine ⟨76033976713056668464009913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202757271234817782570693101 76033976713056668464009913)
      ·
        refine ⟨57025482534792501348007435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76033976713056668464009913 57025482534792501348007435)
        ·
          refine ⟨85538223802188752022011153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57025482534792501348007435 85538223802188752022011153)
          ·
            refine ⟨64153667851641564016508365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85538223802188752022011153 64153667851641564016508365)
            ·
              refine ⟨24057625444365586506190637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64153667851641564016508365 24057625444365586506190637)
              ·
                refine ⟨9021609541637094939821489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24057625444365586506190637 9021609541637094939821489)
                ·
                  refine ⟨6766207156227821204866117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021609541637094939821489 6766207156227821204866117)
                  ·
                    refine ⟨1268663841792716475912397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766207156227821204866117 1268663841792716475912397)
                    ·
                      rfl

theorem cell22_3706071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_3706071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706071 prefixEnd_3706071 := by exact prefixLift 3706071
  have htrace : WordTrace (prefixWord ++ tailWord_3706071) baseStart_3706071 baseEnd_3706071 := by
    simpa [prefixWord, tailWord_3706071, baseEnd_3706071] using wordTrace_append hprefix tailTrace_3706071
  have hstable : (prefixWord ++ tailWord_3706071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706071).length < 2 ^ (prefixWord ++ tailWord_3706071).sum := by decide
  have hdescent : baseEnd_3706071 < baseStart_3706071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706077 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3706077 : Nat := 118140960795 + 3706077 * 2 ^ 59
def prefixEnd_3706077 : Nat := 4983230072969 + 3 ^ 40 * 3706077 * 2
def baseEnd_3706077 : Nat := 1268665895715334460262379

theorem tailTrace_3706077 : CollatzResearch.WordTrace tailWord_3706077 prefixEnd_3706077 1268665895715334460262379 := by
  unfold tailWord_3706077
  simp only [CollatzResearch.WordTrace]
  refine ⟨135171732994523451405180485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90114488663015634270120323 135171732994523451405180485)
  ·
    refine ⟨25344699936473147138471341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135171732994523451405180485 25344699936473147138471341)
    ·
      refine ⟨9504262476177430176926753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25344699936473147138471341 9504262476177430176926753)
      ·
        refine ⟨7128196857133072632695065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9504262476177430176926753 7128196857133072632695065)
        ·
          refine ⟨5346147642849804474521299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7128196857133072632695065 5346147642849804474521299)
          ·
            refine ⟨8019221464274706711781949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346147642849804474521299 8019221464274706711781949)
            ·
              refine ⟨3007208049103015016918231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8019221464274706711781949 3007208049103015016918231)
              ·
                refine ⟨4510812073654522525377347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007208049103015016918231 4510812073654522525377347)
                ·
                  refine ⟨6766218110481783788066021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510812073654522525377347 6766218110481783788066021)
                  ·
                    refine ⟨1268665895715334460262379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766218110481783788066021 1268665895715334460262379)
                    ·
                      rfl

theorem cell22_3706077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3706077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706077 prefixEnd_3706077 := by exact prefixLift 3706077
  have htrace : WordTrace (prefixWord ++ tailWord_3706077) baseStart_3706077 baseEnd_3706077 := by
    simpa [prefixWord, tailWord_3706077, baseEnd_3706077] using wordTrace_append hprefix tailTrace_3706077
  have hstable : (prefixWord ++ tailWord_3706077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706077).length < 2 ^ (prefixWord ++ tailWord_3706077).sum := by decide
  have hdescent : baseEnd_3706077 < baseStart_3706077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706090 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_3706090 : Nat := 118140960795 + 3706090 * 2 ^ 59
def prefixEnd_3706090 : Nat := 4983230072969 + 3 ^ 40 * 3706090 * 2
def baseEnd_3706090 : Nat := 1268670345881006759687339

theorem tailTrace_3706090 : CollatzResearch.WordTrace tailWord_3706090 prefixEnd_3706090 1268670345881006759687339 := by
  unfold tailWord_3706090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33793051785869088656350931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90114804762317569750269149 33793051785869088656350931)
  ·
    refine ⟨50689577678803632984526397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33793051785869088656350931 50689577678803632984526397)
    ·
      refine ⟨19008591629551362369197399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50689577678803632984526397 19008591629551362369197399)
      ·
        refine ⟨28512887444327043553796099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19008591629551362369197399 28512887444327043553796099)
        ·
          refine ⟨42769331166490565330694149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28512887444327043553796099 42769331166490565330694149)
          ·
            refine ⟨8019249593716980999505153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42769331166490565330694149 8019249593716980999505153)
            ·
              refine ⟨6014437195287735749628865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019249593716980999505153 6014437195287735749628865)
              ·
                refine ⟨4510827896465801812221649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6014437195287735749628865 4510827896465801812221649)
                ·
                  refine ⟨3383120922349351359166237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510827896465801812221649 3383120922349351359166237)
                  ·
                    refine ⟨1268670345881006759687339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383120922349351359166237 1268670345881006759687339)
                    ·
                      rfl

theorem cell22_3706090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_3706090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706090 prefixEnd_3706090 := by exact prefixLift 3706090
  have htrace : WordTrace (prefixWord ++ tailWord_3706090) baseStart_3706090 baseEnd_3706090 := by
    simpa [prefixWord, tailWord_3706090, baseEnd_3706090] using wordTrace_append hprefix tailTrace_3706090
  have hstable : (prefixWord ++ tailWord_3706090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706090).length < 2 ^ (prefixWord ++ tailWord_3706090).sum := by decide
  have hdescent : baseEnd_3706090 < baseStart_3706090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706152 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3706152 : Nat := 118140960795 + 3706152 * 2 ^ 59
def prefixEnd_3706152 : Nat := 4983230072969 + 3 ^ 40 * 3706152 * 2
def baseEnd_3706152 : Nat := 1268691569748059264637149

theorem tailTrace_3706152 : CollatzResearch.WordTrace tailWord_3706152 prefixEnd_3706152 1268691569748059264637149 := by
  unfold tailWord_3706152
  simp only [CollatzResearch.WordTrace]
  refine ⟨67587234234625869607080355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90116312312834492809440473 67587234234625869607080355)
  ·
    refine ⟨101380851351938804410620533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67587234234625869607080355 101380851351938804410620533)
    ·
      refine ⟨9504454814244262913495675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101380851351938804410620533 9504454814244262913495675)
      ·
        refine ⟨14256682221366394370243513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9504454814244262913495675 14256682221366394370243513)
        ·
          refine ⟨10692511666024795777682635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14256682221366394370243513 10692511666024795777682635)
          ·
            refine ⟨16038767499037193666523953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10692511666024795777682635 16038767499037193666523953)
            ·
              refine ⟨12029075624277895249892965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16038767499037193666523953 12029075624277895249892965)
              ·
                refine ⟨2255451679552105359354931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12029075624277895249892965 2255451679552105359354931)
                ·
                  refine ⟨3383177519328158039032397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255451679552105359354931 3383177519328158039032397)
                  ·
                    refine ⟨1268691569748059264637149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383177519328158039032397 1268691569748059264637149)
                    ·
                      rfl

theorem cell22_3706152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3706152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706152 prefixEnd_3706152 := by exact prefixLift 3706152
  have htrace : WordTrace (prefixWord ++ tailWord_3706152) baseStart_3706152 baseEnd_3706152 := by
    simpa [prefixWord, tailWord_3706152, baseEnd_3706152] using wordTrace_append hprefix tailTrace_3706152
  have hstable : (prefixWord ++ tailWord_3706152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706152).length < 2 ^ (prefixWord ++ tailWord_3706152).sum := by decide
  have hdescent : baseEnd_3706152 < baseStart_3706152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706165 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 5]
def baseStart_3706165 : Nat := 118140960795 + 3706165 * 2 ^ 59
def prefixEnd_3706165 : Nat := 4983230072969 + 3 ^ 40 * 3706165 * 2
def baseEnd_3706165 : Nat := 422898673304577188020703

theorem tailTrace_3706165 : CollatzResearch.WordTrace tailWord_3706165 prefixEnd_3706165 422898673304577188020703 := by
  unfold tailWord_3706165
  simp only [CollatzResearch.WordTrace]
  refine ⟨135174942618204642434383949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90116628412136428289589299 135174942618204642434383949)
  ·
    refine ⟨50690603481826740912893981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135174942618204642434383949 50690603481826740912893981)
    ·
      refine ⟨19008976305685027842335243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50690603481826740912893981 19008976305685027842335243)
      ·
        refine ⟨28513464458527541763502865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19008976305685027842335243 28513464458527541763502865)
        ·
          refine ⟨21385098343895656322627149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28513464458527541763502865 21385098343895656322627149)
          ·
            refine ⟨8019411878960871120985181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21385098343895656322627149 8019411878960871120985181)
            ·
              refine ⟨3007279454610326670369443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8019411878960871120985181 3007279454610326670369443)
              ·
                refine ⟨4510919181915490005554165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007279454610326670369443 4510919181915490005554165)
                ·
                  refine ⟨422898673304577188020703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4510919181915490005554165 422898673304577188020703)
                  ·
                    rfl

theorem cell22_3706165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_3706165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706165 prefixEnd_3706165 := by exact prefixLift 3706165
  have htrace : WordTrace (prefixWord ++ tailWord_3706165) baseStart_3706165 baseEnd_3706165 := by
    simpa [prefixWord, tailWord_3706165, baseEnd_3706165] using wordTrace_append hprefix tailTrace_3706165
  have hstable : (prefixWord ++ tailWord_3706165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706165).length < 2 ^ (prefixWord ++ tailWord_3706165).sum := by decide
  have hdescent : baseEnd_3706165 < baseStart_3706165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706176 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_3706176 : Nat := 118140960795 + 3706176 * 2 ^ 59
def prefixEnd_3706176 : Nat := 4983230072969 + 3 ^ 40 * 3706176 * 2
def baseEnd_3706176 : Nat := 422899928479510400679025

theorem tailTrace_3706176 : CollatzResearch.WordTrace tailWord_3706176 prefixEnd_3706176 422899928479510400679025 := by
  unfold tailWord_3706176
  simp only [CollatzResearch.WordTrace]
  refine ⟨67587671910582395656517191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90116895880776527542022921 67587671910582395656517191)
  ·
    refine ⟨101381507865873593484775787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67587671910582395656517191 101381507865873593484775787)
    ·
      refine ⟨152072261798810390227163681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101381507865873593484775787 152072261798810390227163681)
      ·
        refine ⟨114054196349107792670372761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152072261798810390227163681 114054196349107792670372761)
        ·
          refine ⟨85540647261830844502779571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114054196349107792670372761 85540647261830844502779571)
          ·
            refine ⟨128310970892746266754169357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85540647261830844502779571 128310970892746266754169357)
            ·
              refine ⟨48116614084779850032813509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128310970892746266754169357 48116614084779850032813509)
              ·
                refine ⟨9021865140896221881152533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48116614084779850032813509 9021865140896221881152533)
                ·
                  refine ⟨422899928479510400679025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9021865140896221881152533 422899928479510400679025)
                  ·
                    rfl

theorem cell22_3706176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_3706176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706176 prefixEnd_3706176 := by exact prefixLift 3706176
  have htrace : WordTrace (prefixWord ++ tailWord_3706176) baseStart_3706176 baseEnd_3706176 := by
    simpa [prefixWord, tailWord_3706176, baseEnd_3706176] using wordTrace_append hprefix tailTrace_3706176
  have hstable : (prefixWord ++ tailWord_3706176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706176).length < 2 ^ (prefixWord ++ tailWord_3706176).sum := by decide
  have hdescent : baseEnd_3706176 < baseStart_3706176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706229 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3706229 : Nat := 118140960795 + 3706229 * 2 ^ 59
def prefixEnd_3706229 : Nat := 4983230072969 + 3 ^ 40 * 3706229 * 2
def baseEnd_3706229 : Nat := 1268717928421656730461913

theorem tailTrace_3706229 : CollatzResearch.WordTrace tailWord_3706229 prefixEnd_3706229 1268717928421656730461913 := by
  unfold tailWord_3706229
  simp only [CollatzResearch.WordTrace]
  refine ⟨135177276889972781364713741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90118184593315187576475827 135177276889972781364713741)
  ·
    refine ⟨50691478833739793011767653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135177276889972781364713741 50691478833739793011767653)
    ·
      refine ⟨9504652281326211189706435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50691478833739793011767653 9504652281326211189706435)
      ·
        refine ⟨14256978421989316784559653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9504652281326211189706435 14256978421989316784559653)
        ·
          refine ⟨2673183454122996897104935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14256978421989316784559653 2673183454122996897104935)
          ·
            refine ⟨4009775181184495345657403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673183454122996897104935 4009775181184495345657403)
            ·
              refine ⟨6014662771776743018486105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009775181184495345657403 6014662771776743018486105)
              ·
                refine ⟨4510997078832557263864579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6014662771776743018486105 4510997078832557263864579)
                ·
                  refine ⟨6766495618248835895796869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510997078832557263864579 6766495618248835895796869)
                  ·
                    refine ⟨1268717928421656730461913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766495618248835895796869 1268717928421656730461913)
                    ·
                      rfl

theorem cell22_3706229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3706229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706229 prefixEnd_3706229 := by exact prefixLift 3706229
  have htrace : WordTrace (prefixWord ++ tailWord_3706229) baseStart_3706229 baseEnd_3706229 := by
    simpa [prefixWord, tailWord_3706229, baseEnd_3706229] using wordTrace_append hprefix tailTrace_3706229
  have hstable : (prefixWord ++ tailWord_3706229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706229).length < 2 ^ (prefixWord ++ tailWord_3706229).sum := by decide
  have hdescent : baseEnd_3706229 < baseStart_3706229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706242 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3706242 : Nat := 118140960795 + 3706242 * 2 ^ 59
def prefixEnd_3706242 : Nat := 4983230072969 + 3 ^ 40 * 3706242 * 2
def baseEnd_3706242 : Nat := 1268722378587329029886873

theorem tailTrace_3706242 : CollatzResearch.WordTrace tailWord_3706242 prefixEnd_3706242 1268722378587329029886873 := by
  unfold tailWord_3706242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33794437759731421146234245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90118500692617123056624653 33794437759731421146234245)
  ·
    refine ⟨6336457079949641464918921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33794437759731421146234245 6336457079949641464918921)
    ·
      refine ⟨4752342809962231098689191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6336457079949641464918921 4752342809962231098689191)
      ·
        refine ⟨7128514214943346648033787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752342809962231098689191 7128514214943346648033787)
        ·
          refine ⟨10692771322415019972050681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128514214943346648033787 10692771322415019972050681)
          ·
            refine ⟨8019578491811264979038011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692771322415019972050681 8019578491811264979038011)
            ·
              refine ⟨12029367737716897468557017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019578491811264979038011 12029367737716897468557017)
              ·
                refine ⟨9022025803287673101417763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12029367737716897468557017 9022025803287673101417763)
                ·
                  refine ⟨13533038704931509652126645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022025803287673101417763 13533038704931509652126645)
                  ·
                    refine ⟨1268722378587329029886873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13533038704931509652126645 1268722378587329029886873)
                    ·
                      rfl

theorem cell22_3706242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3706242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706242 prefixEnd_3706242 := by exact prefixLift 3706242
  have htrace : WordTrace (prefixWord ++ tailWord_3706242) baseStart_3706242 baseEnd_3706242 := by
    simpa [prefixWord, tailWord_3706242, baseEnd_3706242] using wordTrace_append hprefix tailTrace_3706242
  have hstable : (prefixWord ++ tailWord_3706242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706242).length < 2 ^ (prefixWord ++ tailWord_3706242).sum := by decide
  have hdescent : baseEnd_3706242 < baseStart_3706242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706328 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_3706328 : Nat := 118140960795 + 3706328 * 2 ^ 59
def prefixEnd_3706328 : Nat := 4983230072969 + 3 ^ 40 * 3706328 * 2
def baseEnd_3706328 : Nat := 422917272714951157412203

theorem tailTrace_3706328 : CollatzResearch.WordTrace tailWord_3706328 prefixEnd_3706328 422917272714951157412203 := by
  unfold tailWord_3706328
  simp only [CollatzResearch.WordTrace]
  refine ⟨67590443858307060636283819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90120591811076080848378425 67590443858307060636283819)
  ·
    refine ⟨101385665787460590954425729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67590443858307060636283819 101385665787460590954425729)
    ·
      refine ⟨76039249340595443215819297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101385665787460590954425729 76039249340595443215819297)
      ·
        refine ⟨57029437005446582411864473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76039249340595443215819297 57029437005446582411864473)
        ·
          refine ⟨42772077754084936808898355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57029437005446582411864473 42772077754084936808898355)
          ·
            refine ⟨64158116631127405213347533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42772077754084936808898355 64158116631127405213347533)
            ·
              refine ⟨24059293736672776955005325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64158116631127405213347533 24059293736672776955005325)
              ·
                refine ⟨9022235151252291358126997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24059293736672776955005325 9022235151252291358126997)
                ·
                  refine ⟨422917272714951157412203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9022235151252291358126997 422917272714951157412203)
                  ·
                    rfl

theorem cell22_3706328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_3706328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706328 prefixEnd_3706328 := by exact prefixLift 3706328
  have htrace : WordTrace (prefixWord ++ tailWord_3706328) baseStart_3706328 baseEnd_3706328 := by
    simpa [prefixWord, tailWord_3706328, baseEnd_3706328] using wordTrace_append hprefix tailTrace_3706328
  have hstable : (prefixWord ++ tailWord_3706328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706328).length < 2 ^ (prefixWord ++ tailWord_3706328).sum := by decide
  have hdescent : baseEnd_3706328 < baseStart_3706328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706360 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_3706360 : Nat := 118140960795 + 3706360 * 2 ^ 59
def prefixEnd_3706360 : Nat := 4983230072969 + 3 ^ 40 * 3706360 * 2
def baseEnd_3706360 : Nat := 1268762772398816055436511

theorem tailTrace_3706360 : CollatzResearch.WordTrace tailWord_3706360 prefixEnd_3706360 1268762772398816055436511 := by
  unfold tailWord_3706360
  simp only [CollatzResearch.WordTrace]
  refine ⟨67591027426249095368866267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90121369901665460491821689 67591027426249095368866267)
  ·
    refine ⟨101386541139373643053299401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67591027426249095368866267 101386541139373643053299401)
    ·
      refine ⟨76039905854530232289974551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101386541139373643053299401 76039905854530232289974551)
      ·
        refine ⟨114059858781795348434961827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76039905854530232289974551 114059858781795348434961827)
        ·
          refine ⟨171089788172693022652442741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114059858781795348434961827 171089788172693022652442741)
          ·
            refine ⟨16039667641189970873666507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171089788172693022652442741 16039667641189970873666507)
            ·
              refine ⟨24059501461784956310499761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16039667641189970873666507 24059501461784956310499761)
              ·
                refine ⟨18044626096338717232874821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24059501461784956310499761 18044626096338717232874821)
                ·
                  refine ⟨3383367393063509481164029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18044626096338717232874821 3383367393063509481164029)
                  ·
                    refine ⟨1268762772398816055436511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383367393063509481164029 1268762772398816055436511)
                    ·
                      rfl

theorem cell22_3706360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_3706360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706360 prefixEnd_3706360 := by exact prefixLift 3706360
  have htrace : WordTrace (prefixWord ++ tailWord_3706360) baseStart_3706360 baseEnd_3706360 := by
    simpa [prefixWord, tailWord_3706360, baseEnd_3706360] using wordTrace_append hprefix tailTrace_3706360
  have hstable : (prefixWord ++ tailWord_3706360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706360).length < 2 ^ (prefixWord ++ tailWord_3706360).sum := by decide
  have hdescent : baseEnd_3706360 < baseStart_3706360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706375 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3706375 : Nat := 118140960795 + 3706375 * 2 ^ 59
def prefixEnd_3706375 : Nat := 4983230072969 + 3 ^ 40 * 3706375 * 2
def baseEnd_3706375 : Nat := 1268767907205361016311465

theorem tailTrace_3706375 : CollatzResearch.WordTrace tailWord_3706375 prefixEnd_3706375 1268767907205361016311465 := by
  unfold tailWord_3706375
  simp only [CollatzResearch.WordTrace]
  refine ⟨135182601947443848299528579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90121734631629232199685719 135182601947443848299528579)
  ·
    refine ⟨202773902921165772449292869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135182601947443848299528579 202773902921165772449292869)
    ·
      refine ⟨38020106797718582334242413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202773902921165772449292869 38020106797718582334242413)
      ·
        refine ⟨14257540049144468375340905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38020106797718582334242413 14257540049144468375340905)
        ·
          refine ⟨10693155036858351281505679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14257540049144468375340905 10693155036858351281505679)
          ·
            refine ⟨16039732555287526922258519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693155036858351281505679 16039732555287526922258519)
            ·
              refine ⟨24059598832931290383387779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16039732555287526922258519 24059598832931290383387779)
              ·
                refine ⟨36089398249396935575081669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24059598832931290383387779 36089398249396935575081669)
                ·
                  refine ⟨6766762171761925420327813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36089398249396935575081669 6766762171761925420327813)
                  ·
                    refine ⟨1268767907205361016311465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766762171761925420327813 1268767907205361016311465)
                    ·
                      rfl

theorem cell22_3706375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3706375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706375 prefixEnd_3706375 := by exact prefixLift 3706375
  have htrace : WordTrace (prefixWord ++ tailWord_3706375) baseStart_3706375 baseEnd_3706375 := by
    simpa [prefixWord, tailWord_3706375, baseEnd_3706375] using wordTrace_append hprefix tailTrace_3706375
  have hstable : (prefixWord ++ tailWord_3706375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706375).length < 2 ^ (prefixWord ++ tailWord_3706375).sum := by decide
  have hdescent : baseEnd_3706375 < baseStart_3706375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706379 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 4]
def baseStart_3706379 : Nat := 118140960795 + 3706379 * 2 ^ 59
def prefixEnd_3706379 : Nat := 4983230072969 + 3 ^ 40 * 3706379 * 2
def baseEnd_3706379 : Nat := 422923092162368779737151

theorem tailTrace_3706379 : CollatzResearch.WordTrace tailWord_3706379 prefixEnd_3706379 422923092162368779737151 := by
  unfold tailWord_3706379
  simp only [CollatzResearch.WordTrace]
  refine ⟨135182747839429356982674191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90121831892952904655116127 135182747839429356982674191)
  ·
    refine ⟨202774121759144035474011287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135182747839429356982674191 202774121759144035474011287)
    ·
      refine ⟨304161182638716053211016931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202774121759144035474011287 304161182638716053211016931)
      ·
        refine ⟨456241773958074079816525397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304161182638716053211016931 456241773958074079816525397)
        ·
          refine ⟨5346583288571180622849907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 456241773958074079816525397 5346583288571180622849907)
          ·
            refine ⟨8019874932856770934274861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346583288571180622849907 8019874932856770934274861)
            ·
              refine ⟨3007453099821289100353073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8019874932856770934274861 3007453099821289100353073)
              ·
                refine ⟨2255589824865966825264805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3007453099821289100353073 2255589824865966825264805)
                ·
                  refine ⟨422923092162368779737151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255589824865966825264805 422923092162368779737151)
                  ·
                    rfl

theorem cell22_3706379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 4].length) (baseStart_3706379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706379 prefixEnd_3706379 := by exact prefixLift 3706379
  have htrace : WordTrace (prefixWord ++ tailWord_3706379) baseStart_3706379 baseEnd_3706379 := by
    simpa [prefixWord, tailWord_3706379, baseEnd_3706379] using wordTrace_append hprefix tailTrace_3706379
  have hstable : (prefixWord ++ tailWord_3706379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706379).length < 2 ^ (prefixWord ++ tailWord_3706379).sum := by decide
  have hdescent : baseEnd_3706379 < baseStart_3706379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706405 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_3706405 : Nat := 118140960795 + 3706405 * 2 ^ 59
def prefixEnd_3706405 : Nat := 4983230072969 + 3 ^ 40 * 3706405 * 2
def baseEnd_3706405 : Nat := 1268778176818450938061373

theorem tailTrace_3706405 : CollatzResearch.WordTrace tailWord_3706405 prefixEnd_3706405 1268778176818450938061373 := by
  unfold tailWord_3706405
  simp only [CollatzResearch.WordTrace]
  refine ⟨135183696137335163423120669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90122464091556775615413779 135183696137335163423120669)
  ·
    refine ⟨50693886051500686283670251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135183696137335163423120669 50693886051500686283670251)
    ·
      refine ⟨76040829077251029425505377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50693886051500686283670251 76040829077251029425505377)
      ·
        refine ⟨57030621807938272069129033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76040829077251029425505377 57030621807938272069129033)
        ·
          refine ⟨42772966355953704051846775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57030621807938272069129033 42772966355953704051846775)
          ·
            refine ⟨64159449533930556077770163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42772966355953704051846775 64159449533930556077770163)
            ·
              refine ⟨96239174300895834116655245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64159449533930556077770163 96239174300895834116655245)
              ·
                refine ⟨36089690362835937793745717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96239174300895834116655245 36089690362835937793745717)
                ·
                  refine ⟨3383408471515869168163661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36089690362835937793745717 3383408471515869168163661)
                  ·
                    refine ⟨1268778176818450938061373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383408471515869168163661 1268778176818450938061373)
                    ·
                      rfl

theorem cell22_3706405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_3706405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706405 prefixEnd_3706405 := by exact prefixLift 3706405
  have htrace : WordTrace (prefixWord ++ tailWord_3706405) baseStart_3706405 baseEnd_3706405 := by
    simpa [prefixWord, tailWord_3706405, baseEnd_3706405] using wordTrace_append hprefix tailTrace_3706405
  have hstable : (prefixWord ++ tailWord_3706405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706405).length < 2 ^ (prefixWord ++ tailWord_3706405).sum := by decide
  have hdescent : baseEnd_3706405 < baseStart_3706405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706450 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3706450 : Nat := 118140960795 + 3706450 * 2 ^ 59
def prefixEnd_3706450 : Nat := 4983230072969 + 3 ^ 40 * 3706450 * 2
def baseEnd_3706450 : Nat := 1268793581238085820686235

theorem tailTrace_3706450 : CollatzResearch.WordTrace tailWord_3706450 prefixEnd_3706450 1268793581238085820686235 := by
  unfold tailWord_3706450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33796334355543034027127201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90123558281448090739005869 33796334355543034027127201)
  ·
    refine ⟨25347250766657275520345401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33796334355543034027127201 25347250766657275520345401)
    ·
      refine ⟨19010438074992956640259051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25347250766657275520345401 19010438074992956640259051)
      ·
        refine ⟨28515657112489434960388577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19010438074992956640259051 28515657112489434960388577)
        ·
          refine ⟨21386742834367076220291433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28515657112489434960388577 21386742834367076220291433)
          ·
            refine ⟨16040057125775307165218575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21386742834367076220291433 16040057125775307165218575)
            ·
              refine ⟨24060085688662960747827863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040057125775307165218575 24060085688662960747827863)
              ·
                refine ⟨36090128532994441121741795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24060085688662960747827863 36090128532994441121741795)
                ·
                  refine ⟨54135192799491661682612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36090128532994441121741795 54135192799491661682612693)
                  ·
                    refine ⟨1268793581238085820686235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54135192799491661682612693 1268793581238085820686235)
                    ·
                      rfl

theorem cell22_3706450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3706450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706450 prefixEnd_3706450 := by exact prefixLift 3706450
  have htrace : WordTrace (prefixWord ++ tailWord_3706450) baseStart_3706450 baseEnd_3706450 := by
    simpa [prefixWord, tailWord_3706450, baseEnd_3706450] using wordTrace_append hprefix tailTrace_3706450
  have hstable : (prefixWord ++ tailWord_3706450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706450).length < 2 ^ (prefixWord ++ tailWord_3706450).sum := by decide
  have hdescent : baseEnd_3706450 < baseStart_3706450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706465 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3706465 : Nat := 118140960795 + 3706465 * 2 ^ 59
def prefixEnd_3706465 : Nat := 4983230072969 + 3 ^ 40 * 3706465 * 2
def baseEnd_3706465 : Nat := 1268798716044630781561189

theorem tailTrace_3706465 : CollatzResearch.WordTrace tailWord_3706465 prefixEnd_3706465 1268798716044630781561189 := by
  unfold tailWord_3706465
  simp only [CollatzResearch.WordTrace]
  refine ⟨135185884517117793670304849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90123923011411862446869899 135185884517117793670304849)
  ·
    refine ⟨101389413387838345252728637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135185884517117793670304849 101389413387838345252728637)
    ·
      refine ⟨38021030020439379469773239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101389413387838345252728637 38021030020439379469773239)
      ·
        refine ⟨57031545030659069204659859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38021030020439379469773239 57031545030659069204659859)
        ·
          refine ⟨85547317545988603806989789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57031545030659069204659859 85547317545988603806989789)
          ·
            refine ⟨32080244079745726427621171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85547317545988603806989789 32080244079745726427621171)
            ·
              refine ⟨48120366119618589641431757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32080244079745726427621171 48120366119618589641431757)
              ·
                refine ⟨18045137294856971115536909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48120366119618589641431757 18045137294856971115536909)
                ·
                  refine ⟨6766926485571364168326341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18045137294856971115536909 6766926485571364168326341)
                  ·
                    refine ⟨1268798716044630781561189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766926485571364168326341 1268798716044630781561189)
                    ·
                      rfl

theorem cell22_3706465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3706465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706465 prefixEnd_3706465 := by exact prefixLift 3706465
  have htrace : WordTrace (prefixWord ++ tailWord_3706465) baseStart_3706465 baseEnd_3706465 := by
    simpa [prefixWord, tailWord_3706465, baseEnd_3706465] using wordTrace_append hprefix tailTrace_3706465
  have hstable : (prefixWord ++ tailWord_3706465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706465).length < 2 ^ (prefixWord ++ tailWord_3706465).sum := by decide
  have hdescent : baseEnd_3706465 < baseStart_3706465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706497 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 6]
def baseStart_3706497 : Nat := 118140960795 + 3706497 * 2 ^ 59
def prefixEnd_3706497 : Nat := 4983230072969 + 3 ^ 40 * 3706497 * 2
def baseEnd_3706497 : Nat := 422936556766197788253697

theorem tailTrace_3706497 : CollatzResearch.WordTrace tailWord_3706497 prefixEnd_3706497 422936556766197788253697 := by
  unfold tailWord_3706497
  simp only [CollatzResearch.WordTrace]
  refine ⟨135187051653001863135469745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90124701102001242090313163 135187051653001863135469745)
  ·
    refine ⟨101390288739751397351602309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135187051653001863135469745 101390288739751397351602309)
    ·
      refine ⟨19010679138703387003425433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101390288739751397351602309 19010679138703387003425433)
      ·
        refine ⟨14258009354027540252569075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19010679138703387003425433 14258009354027540252569075)
        ·
          refine ⟨21387014031041310378853613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14258009354027540252569075 21387014031041310378853613)
          ·
            refine ⟨8020130261640491392070105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21387014031041310378853613 8020130261640491392070105)
            ·
              refine ⟨6015097696230368544052579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8020130261640491392070105 6015097696230368544052579)
              ·
                refine ⟨9022646544345552816078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015097696230368544052579 9022646544345552816078869)
                ·
                  refine ⟨422936556766197788253697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9022646544345552816078869 422936556766197788253697)
                  ·
                    rfl

theorem cell22_3706497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_3706497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706497 prefixEnd_3706497 := by exact prefixLift 3706497
  have htrace : WordTrace (prefixWord ++ tailWord_3706497) baseStart_3706497 baseEnd_3706497 := by
    simpa [prefixWord, tailWord_3706497, baseEnd_3706497] using wordTrace_append hprefix tailTrace_3706497
  have hstable : (prefixWord ++ tailWord_3706497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706497).length < 2 ^ (prefixWord ++ tailWord_3706497).sum := by decide
  have hdescent : baseEnd_3706497 < baseStart_3706497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706512 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_3706512 : Nat := 118140960795 + 3706512 * 2 ^ 59
def prefixEnd_3706512 : Nat := 4983230072969 + 3 ^ 40 * 3706512 * 2
def baseEnd_3706512 : Nat := 1268814805105138325636045

theorem tailTrace_3706512 : CollatzResearch.WordTrace tailWord_3706512 prefixEnd_3706512 1268814805105138325636045 := by
  unfold tailWord_3706512
  simp only [CollatzResearch.WordTrace]
  refine ⟨67593799373973760348632895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90125065831965013798177193 67593799373973760348632895)
  ·
    refine ⟨101390699060960640522949343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67593799373973760348632895 101390699060960640522949343)
    ·
      refine ⟨152086048591440960784424015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101390699060960640522949343 152086048591440960784424015)
      ·
        refine ⟨228129072887161441176636023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152086048591440960784424015 228129072887161441176636023)
        ·
          refine ⟨342193609330742161764954035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228129072887161441176636023 342193609330742161764954035)
          ·
            refine ⟨513290413996113242647431053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342193609330742161764954035 513290413996113242647431053)
            ·
              refine ⟨192483905248542465992786645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513290413996113242647431053 192483905248542465992786645)
              ·
                refine ⟨4511341529262714046705937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192483905248542465992786645 4511341529262714046705937)
                ·
                  refine ⟨3383506146947035535029453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4511341529262714046705937 3383506146947035535029453)
                  ·
                    refine ⟨1268814805105138325636045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383506146947035535029453 1268814805105138325636045)
                    ·
                      rfl

theorem cell22_3706512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_3706512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706512 prefixEnd_3706512 := by exact prefixLift 3706512
  have htrace : WordTrace (prefixWord ++ tailWord_3706512) baseStart_3706512 baseEnd_3706512 := by
    simpa [prefixWord, tailWord_3706512, baseEnd_3706512] using wordTrace_append hprefix tailTrace_3706512
  have hstable : (prefixWord ++ tailWord_3706512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706512).length < 2 ^ (prefixWord ++ tailWord_3706512).sum := by decide
  have hdescent : baseEnd_3706512 < baseStart_3706512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706516 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3706516 : Nat := 118140960795 + 3706516 * 2 ^ 59
def prefixEnd_3706516 : Nat := 4983230072969 + 3 ^ 40 * 3706516 * 2
def baseEnd_3706516 : Nat := 1268816174386883648536033

theorem tailTrace_3706516 : CollatzResearch.WordTrace tailWord_3706516 prefixEnd_3706516 1268816174386883648536033 := by
  unfold tailWord_3706516
  simp only [CollatzResearch.WordTrace]
  refine ⟨67593872319966514690205701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90125163093288686253607601 67593872319966514690205701)
  ·
    refine ⟨12673851059993721504413569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67593872319966514690205701 12673851059993721504413569)
    ·
      refine ⟨9505388294995291128310177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12673851059993721504413569 9505388294995291128310177)
      ·
        refine ⟨7129041221246468346232633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9505388294995291128310177 7129041221246468346232633)
        ·
          refine ⟨5346780915934851259674475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7129041221246468346232633 5346780915934851259674475)
          ·
            refine ⟨8020171373902276889511713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346780915934851259674475 8020171373902276889511713)
            ·
              refine ⟨6015128530426707667133785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8020171373902276889511713 6015128530426707667133785)
              ·
                refine ⟨4511346397820030750350339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6015128530426707667133785 4511346397820030750350339)
                ·
                  refine ⟨6767019596730046125525509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511346397820030750350339 6767019596730046125525509)
                  ·
                    refine ⟨1268816174386883648536033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6767019596730046125525509 1268816174386883648536033)
                    ·
                      rfl

theorem cell22_3706516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3706516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706516 prefixEnd_3706516 := by exact prefixLift 3706516
  have htrace : WordTrace (prefixWord ++ tailWord_3706516) baseStart_3706516 baseEnd_3706516 := by
    simpa [prefixWord, tailWord_3706516, baseEnd_3706516] using wordTrace_append hprefix tailTrace_3706516
  have hstable : (prefixWord ++ tailWord_3706516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706516).length < 2 ^ (prefixWord ++ tailWord_3706516).sum := by decide
  have hdescent : baseEnd_3706516 < baseStart_3706516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706632 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_3706632 : Nat := 118140960795 + 3706632 * 2 ^ 59
def prefixEnd_3706632 : Nat := 4983230072969 + 3 ^ 40 * 3706632 * 2
def baseEnd_3706632 : Nat := 422951961185832670878559

theorem tailTrace_3706632 : CollatzResearch.WordTrace tailWord_3706632 prefixEnd_3706632 422951961185832670878559 := by
  unfold tailWord_3706632
  simp only [CollatzResearch.WordTrace]
  refine ⟨67595987753756390595817075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90127983671675187461089433 67595987753756390595817075)
  ·
    refine ⟨101393981630634585893725613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67595987753756390595817075 101393981630634585893725613)
    ·
      refine ⟨38022743111487969710147105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101393981630634585893725613 38022743111487969710147105)
      ·
        refine ⟨28517057333615977282610329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38022743111487969710147105 28517057333615977282610329)
        ·
          refine ⟨21387793000211982961957747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28517057333615977282610329 21387793000211982961957747)
          ·
            refine ⟨32081689500317974442936621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21387793000211982961957747 32081689500317974442936621)
            ·
              refine ⟨12030633562619240416101233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32081689500317974442936621 12030633562619240416101233)
              ·
                refine ⟨9022975171964430312075925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12030633562619240416101233 9022975171964430312075925)
                ·
                  refine ⟨422951961185832670878559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9022975171964430312075925 422951961185832670878559)
                  ·
                    rfl

theorem cell22_3706632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_3706632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706632 prefixEnd_3706632 := by exact prefixLift 3706632
  have htrace : WordTrace (prefixWord ++ tailWord_3706632) baseStart_3706632 baseEnd_3706632 := by
    simpa [prefixWord, tailWord_3706632, baseEnd_3706632] using wordTrace_append hprefix tailTrace_3706632
  have hstable : (prefixWord ++ tailWord_3706632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706632).length < 2 ^ (prefixWord ++ tailWord_3706632).sum := by decide
  have hdescent : baseEnd_3706632 < baseStart_3706632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706737 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3706737 : Nat := 118140960795 + 3706737 * 2 ^ 59
def prefixEnd_3706737 : Nat := 4983230072969 + 3 ^ 40 * 3706737 * 2
def baseEnd_3706737 : Nat := 1268891827203312738760355

theorem tailTrace_3706737 : CollatzResearch.WordTrace tailWord_3706737 prefixEnd_3706737 1268891827203312738760355 := by
  unfold tailWord_3706737
  simp only [CollatzResearch.WordTrace]
  refine ⟨135195805172132384124206465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90130536781421589416137643 135195805172132384124206465)
  ·
    refine ⟨101396853879099288093154849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135195805172132384124206465 101396853879099288093154849)
    ·
      refine ⟨76047640409324466069866137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101396853879099288093154849 76047640409324466069866137)
      ·
        refine ⟨57035730306993349552399603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76047640409324466069866137 57035730306993349552399603)
        ·
          refine ⟨85553595460490024328599405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57035730306993349552399603 85553595460490024328599405)
          ·
            refine ⟨32082598297683759123224777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85553595460490024328599405 32082598297683759123224777)
            ·
              refine ⟨24061948723262819342418583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32082598297683759123224777 24061948723262819342418583)
              ·
                refine ⟨36092923084894229013627875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24061948723262819342418583 36092923084894229013627875)
                ·
                  refine ⟨54139384627341343520441813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36092923084894229013627875 54139384627341343520441813)
                  ·
                    refine ⟨1268891827203312738760355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54139384627341343520441813 1268891827203312738760355)
                    ·
                      rfl

theorem cell22_3706737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3706737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706737 prefixEnd_3706737 := by exact prefixLift 3706737
  have htrace : WordTrace (prefixWord ++ tailWord_3706737) baseStart_3706737 baseEnd_3706737 := by
    simpa [prefixWord, tailWord_3706737, baseEnd_3706737] using wordTrace_append hprefix tailTrace_3706737
  have hstable : (prefixWord ++ tailWord_3706737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706737).length < 2 ^ (prefixWord ++ tailWord_3706737).sum := by decide
  have hdescent : baseEnd_3706737 < baseStart_3706737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706769 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_3706769 : Nat := 118140960795 + 3706769 * 2 ^ 59
def prefixEnd_3706769 : Nat := 4983230072969 + 3 ^ 40 * 3706769 * 2
def baseEnd_3706769 : Nat := 1268902781457275321960257

theorem tailTrace_3706769 : CollatzResearch.WordTrace tailWord_3706769 prefixEnd_3706769 1268902781457275321960257 := by
  unfold tailWord_3706769
  simp only [CollatzResearch.WordTrace]
  refine ⟨135196972308016453589371361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90131314872010969059580907 135196972308016453589371361)
  ·
    refine ⟨101397729231012340192028521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135196972308016453589371361 101397729231012340192028521)
    ·
      refine ⟨76048296923259255144021391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101397729231012340192028521 76048296923259255144021391)
      ·
        refine ⟨114072445384888882716032087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76048296923259255144021391 114072445384888882716032087)
        ·
          refine ⟨171108668077333324074048131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114072445384888882716032087 171108668077333324074048131)
          ·
            refine ⟨256663002115999986111072197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171108668077333324074048131 256663002115999986111072197)
            ·
              refine ⟨48124312896749997395826037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256663002115999986111072197 48124312896749997395826037)
              ·
                refine ⟨4511654334070312255858691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48124312896749997395826037 4511654334070312255858691)
                ·
                  refine ⟨6767481501105468383788037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511654334070312255858691 6767481501105468383788037)
                  ·
                    refine ⟨1268902781457275321960257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6767481501105468383788037 1268902781457275321960257)
                    ·
                      rfl

theorem cell22_3706769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_3706769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706769 prefixEnd_3706769 := by exact prefixLift 3706769
  have htrace : WordTrace (prefixWord ++ tailWord_3706769) baseStart_3706769 baseEnd_3706769 := by
    simpa [prefixWord, tailWord_3706769, baseEnd_3706769] using wordTrace_append hprefix tailTrace_3706769
  have hstable : (prefixWord ++ tailWord_3706769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706769).length < 2 ^ (prefixWord ++ tailWord_3706769).sum := by decide
  have hdescent : baseEnd_3706769 < baseStart_3706769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706799 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 1, 5]
def baseStart_3706799 : Nat := 118140960795 + 3706799 * 2 ^ 59
def prefixEnd_3706799 : Nat := 4983230072969 + 3 ^ 40 * 3706799 * 2
def baseEnd_3706799 : Nat := 1268913051070365243710165

theorem tailTrace_3706799 : CollatzResearch.WordTrace tailWord_3706799 prefixEnd_3706799 1268913051070365243710165 := by
  unfold tailWord_3706799
  simp only [CollatzResearch.WordTrace]
  refine ⟨135198066497907768712963451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90132044331938512475308967 135198066497907768712963451)
  ·
    refine ⟨202797099746861653069445177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135198066497907768712963451 202797099746861653069445177)
    ·
      refine ⟨152097824810146239802083883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202797099746861653069445177 152097824810146239802083883)
      ·
        refine ⟨228146737215219359703125825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152097824810146239802083883 228146737215219359703125825)
        ·
          refine ⟨171110052911414519777344369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228146737215219359703125825 171110052911414519777344369)
          ·
            refine ⟨128332539683560889833008277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171110052911414519777344369 128332539683560889833008277)
            ·
              refine ⟨6015587797666916710922263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128332539683560889833008277 6015587797666916710922263)
              ·
                refine ⟨9023381696500375066383395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015587797666916710922263 9023381696500375066383395)
                ·
                  refine ⟨13535072544750562599575093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9023381696500375066383395 13535072544750562599575093)
                  ·
                    refine ⟨1268913051070365243710165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13535072544750562599575093 1268913051070365243710165)
                    ·
                      rfl

theorem cell22_3706799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_3706799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706799 prefixEnd_3706799 := by exact prefixLift 3706799
  have htrace : WordTrace (prefixWord ++ tailWord_3706799) baseStart_3706799 baseEnd_3706799 := by
    simpa [prefixWord, tailWord_3706799, baseEnd_3706799] using wordTrace_append hprefix tailTrace_3706799
  have hstable : (prefixWord ++ tailWord_3706799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706799).length < 2 ^ (prefixWord ++ tailWord_3706799).sum := by decide
  have hdescent : baseEnd_3706799 < baseStart_3706799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706850 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3706850 : Nat := 118140960795 + 3706850 * 2 ^ 59
def prefixEnd_3706850 : Nat := 4983230072969 + 3 ^ 40 * 3706850 * 2
def baseEnd_3706850 : Nat := 1268930509412618110685009

theorem tailTrace_3706850 : CollatzResearch.WordTrace tailWord_3706850 prefixEnd_3706850 1268930509412618110685009 := by
  unfold tailWord_3706850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33799981655180751105767501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90133284413815336282046669 33799981655180751105767501)
  ·
    refine ⟨12674993120692781664662813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33799981655180751105767501 12674993120692781664662813)
    ·
      refine ⟨4753122420259793124248555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12674993120692781664662813 4753122420259793124248555)
      ·
        refine ⟨7129683630389689686372833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753122420259793124248555 7129683630389689686372833)
        ·
          refine ⟨5347262722792267264779625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7129683630389689686372833 5347262722792267264779625)
          ·
            refine ⟨4010447042094200448584719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5347262722792267264779625 4010447042094200448584719)
            ·
              refine ⟨6015670563141300672877079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010447042094200448584719 6015670563141300672877079)
              ·
                refine ⟨9023505844711951009315619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015670563141300672877079 9023505844711951009315619)
                ·
                  refine ⟨13535258767067926513973429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9023505844711951009315619 13535258767067926513973429)
                  ·
                    refine ⟨1268930509412618110685009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13535258767067926513973429 1268930509412618110685009)
                    ·
                      rfl

theorem cell22_3706850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3706850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706850 prefixEnd_3706850 := by exact prefixLift 3706850
  have htrace : WordTrace (prefixWord ++ tailWord_3706850) baseStart_3706850 baseEnd_3706850 := by
    simpa [prefixWord, tailWord_3706850, baseEnd_3706850] using wordTrace_append hprefix tailTrace_3706850
  have hstable : (prefixWord ++ tailWord_3706850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706850).length < 2 ^ (prefixWord ++ tailWord_3706850).sum := by decide
  have hdescent : baseEnd_3706850 < baseStart_3706850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706886 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3706886 : Nat := 118140960795 + 3706886 * 2 ^ 59
def prefixEnd_3706886 : Nat := 4983230072969 + 3 ^ 40 * 3706886 * 2
def baseEnd_3706886 : Nat := 422980944316108672261633

theorem tailTrace_3706886 : CollatzResearch.WordTrace tailWord_3706886 prefixEnd_3706886 422980944316108672261633 := by
  unfold tailWord_3706886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225038739018518205355641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90134159765728388380920341 4225038739018518205355641)
  ·
    refine ⟨3168779054263888654016731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4225038739018518205355641 3168779054263888654016731)
    ·
      refine ⟨4753168581395832981025097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3168779054263888654016731 4753168581395832981025097)
      ·
        refine ⟨3564876436046874735768823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4753168581395832981025097 3564876436046874735768823)
        ·
          refine ⟨5347314654070312103653235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564876436046874735768823 5347314654070312103653235)
          ·
            refine ⟨8020971981105468155479853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347314654070312103653235 8020971981105468155479853)
            ·
              refine ⟨3007864492914550558304945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8020971981105468155479853 3007864492914550558304945)
              ·
                refine ⟨2255898369685912918728709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3007864492914550558304945 2255898369685912918728709)
                ·
                  refine ⟨422980944316108672261633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255898369685912918728709 422980944316108672261633)
                  ·
                    rfl

theorem cell22_3706886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3706886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706886 prefixEnd_3706886 := by exact prefixLift 3706886
  have htrace : WordTrace (prefixWord ++ tailWord_3706886) baseStart_3706886 baseEnd_3706886 := by
    simpa [prefixWord, tailWord_3706886, baseEnd_3706886] using wordTrace_append hprefix tailTrace_3706886
  have hstable : (prefixWord ++ tailWord_3706886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706886).length < 2 ^ (prefixWord ++ tailWord_3706886).sum := by decide
  have hdescent : baseEnd_3706886 < baseStart_3706886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706908 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 5]
def baseStart_3706908 : Nat := 118140960795 + 3706908 * 2 ^ 59
def prefixEnd_3706908 : Nat := 4983230072969 + 3 ^ 40 * 3706908 * 2
def baseEnd_3706908 : Nat := 422983454665975097578277

theorem tailTrace_3706908 : CollatzResearch.WordTrace tailWord_3706908 prefixEnd_3706908 422983454665975097578277 := by
  unfold tailWord_3706908
  simp only [CollatzResearch.WordTrace]
  refine ⟨67601021027256440164340689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90134694703008586885787585 67601021027256440164340689)
  ·
    refine ⟨50700765770442330123255517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67601021027256440164340689 50700765770442330123255517)
    ·
      refine ⟨19012787163915873796220819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50700765770442330123255517 19012787163915873796220819)
      ·
        refine ⟨28519180745873810694331229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19012787163915873796220819 28519180745873810694331229)
        ·
          refine ⟨10694692779702679010374211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28519180745873810694331229 10694692779702679010374211)
          ·
            refine ⟨16042039169554018515561317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694692779702679010374211 16042039169554018515561317)
            ·
              refine ⟨3007882344291378471667747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16042039169554018515561317 3007882344291378471667747)
              ·
                refine ⟨4511823516437067707501621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007882344291378471667747 4511823516437067707501621)
                ·
                  refine ⟨422983454665975097578277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4511823516437067707501621 422983454665975097578277)
                  ·
                    rfl

theorem cell22_3706908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_3706908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706908 prefixEnd_3706908 := by exact prefixLift 3706908
  have htrace : WordTrace (prefixWord ++ tailWord_3706908) baseStart_3706908 baseEnd_3706908 := by
    simpa [prefixWord, tailWord_3706908, baseEnd_3706908] using wordTrace_append hprefix tailTrace_3706908
  have hstable : (prefixWord ++ tailWord_3706908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706908).length < 2 ^ (prefixWord ++ tailWord_3706908).sum := by decide
  have hdescent : baseEnd_3706908 < baseStart_3706908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706949 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_3706949 : Nat := 118140960795 + 3706949 * 2 ^ 59
def prefixEnd_3706949 : Nat := 4983230072969 + 3 ^ 40 * 3706949 * 2
def baseEnd_3706949 : Nat := 1268964399135814852459705

theorem tailTrace_3706949 : CollatzResearch.WordTrace tailWord_3706949 prefixEnd_3706949 1268964399135814852459705 := by
  unfold tailWord_3706949
  simp only [CollatzResearch.WordTrace]
  refine ⟨135203537447364344330923901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90135691631576229553949267 135203537447364344330923901)
  ·
    refine ⟨50701326542761629124096463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135203537447364344330923901 50701326542761629124096463)
    ·
      refine ⟨76051989814142443686144695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50701326542761629124096463 76051989814142443686144695)
      ·
        refine ⟨114077984721213665529217043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76051989814142443686144695 114077984721213665529217043)
        ·
          refine ⟨171116977081820498293825565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114077984721213665529217043 171116977081820498293825565)
          ·
            refine ⟨64168866405682686860184587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171116977081820498293825565 64168866405682686860184587)
            ·
              refine ⟨96253299608524030290276881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64168866405682686860184587 96253299608524030290276881)
              ·
                refine ⟨72189974706393022717707661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96253299608524030290276881 72189974706393022717707661)
                ·
                  refine ⟨27071240514897383519140373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72189974706393022717707661 27071240514897383519140373)
                  ·
                    refine ⟨1268964399135814852459705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27071240514897383519140373 1268964399135814852459705)
                    ·
                      rfl

theorem cell22_3706949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_3706949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706949 prefixEnd_3706949 := by exact prefixLift 3706949
  have htrace : WordTrace (prefixWord ++ tailWord_3706949) baseStart_3706949 baseEnd_3706949 := by
    simpa [prefixWord, tailWord_3706949, baseEnd_3706949] using wordTrace_append hprefix tailTrace_3706949
  have hstable : (prefixWord ++ tailWord_3706949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706949).length < 2 ^ (prefixWord ++ tailWord_3706949).sum := by decide
  have hdescent : baseEnd_3706949 < baseStart_3706949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3706968 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_3706968 : Nat := 118140960795 + 3706968 * 2 ^ 59
def prefixEnd_3706968 : Nat := 4983230072969 + 3 ^ 40 * 3706968 * 2
def baseEnd_3706968 : Nat := 1268970903224105136234647

theorem tailTrace_3706968 : CollatzResearch.WordTrace tailWord_3706968 prefixEnd_3706968 1268970903224105136234647 := by
  unfold tailWord_3706968
  simp only [CollatzResearch.WordTrace]
  refine ⟨67602115217147755287932779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90136153622863673717243705 67602115217147755287932779)
  ·
    refine ⟨101403172825721632931899169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67602115217147755287932779 101403172825721632931899169)
    ·
      refine ⟨76052379619291224698924377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101403172825721632931899169 76052379619291224698924377)
      ·
        refine ⟨57039284714468418524193283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76052379619291224698924377 57039284714468418524193283)
        ·
          refine ⟨85558927071702627786289925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57039284714468418524193283 85558927071702627786289925)
          ·
            refine ⟨16042298825944242709929361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85558927071702627786289925 16042298825944242709929361)
            ·
              refine ⟨12031724119458182032447021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16042298825944242709929361 12031724119458182032447021)
              ·
                refine ⟨4511896544796818262167633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12031724119458182032447021 4511896544796818262167633)
                ·
                  refine ⟨3383922408597613696625725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4511896544796818262167633 3383922408597613696625725)
                  ·
                    refine ⟨1268970903224105136234647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383922408597613696625725 1268970903224105136234647)
                    ·
                      rfl

theorem cell22_3706968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_3706968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3706968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3706968 prefixEnd_3706968 := by exact prefixLift 3706968
  have htrace : WordTrace (prefixWord ++ tailWord_3706968) baseStart_3706968 baseEnd_3706968 := by
    simpa [prefixWord, tailWord_3706968, baseEnd_3706968] using wordTrace_append hprefix tailTrace_3706968
  have hstable : (prefixWord ++ tailWord_3706968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3706968).length < 2 ^ (prefixWord ++ tailWord_3706968).sum := by decide
  have hdescent : baseEnd_3706968 < baseStart_3706968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3706968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707013 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_3707013 : Nat := 118140960795 + 3707013 * 2 ^ 59
def prefixEnd_3707013 : Nat := 4983230072969 + 3 ^ 40 * 3707013 * 2
def baseEnd_3707013 : Nat := 1268986307643740018859509

theorem tailTrace_3707013 : CollatzResearch.WordTrace tailWord_3707013 prefixEnd_3707013 1268986307643740018859509 := by
  unfold tailWord_3707013
  simp only [CollatzResearch.WordTrace]
  refine ⟨135205871719132483261253693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90137247812754988840835795 135205871719132483261253693)
  ·
    refine ⟨50702201894674681222970135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135205871719132483261253693 50702201894674681222970135)
    ·
      refine ⟨76053302842012021834455203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50702201894674681222970135 76053302842012021834455203)
      ·
        refine ⟨114079954263018032751682805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76053302842012021834455203 114079954263018032751682805)
        ·
          refine ⟨10694995712157940570470263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114079954263018032751682805 10694995712157940570470263)
          ·
            refine ⟨16042493568236910855705395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694995712157940570470263 16042493568236910855705395)
            ·
              refine ⟨24063740352355366283558093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16042493568236910855705395 24063740352355366283558093)
              ·
                refine ⟨9023902632133262356334285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24063740352355366283558093 9023902632133262356334285)
                ·
                  refine ⟨3383963487049973383625357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9023902632133262356334285 3383963487049973383625357)
                  ·
                    refine ⟨1268986307643740018859509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383963487049973383625357 1268986307643740018859509)
                    ·
                      rfl

theorem cell22_3707013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_3707013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707013 prefixEnd_3707013 := by exact prefixLift 3707013
  have htrace : WordTrace (prefixWord ++ tailWord_3707013) baseStart_3707013 baseEnd_3707013 := by
    simpa [prefixWord, tailWord_3707013, baseEnd_3707013] using wordTrace_append hprefix tailTrace_3707013
  have hstable : (prefixWord ++ tailWord_3707013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707013).length < 2 ^ (prefixWord ++ tailWord_3707013).sum := by decide
  have hdescent : baseEnd_3707013 < baseStart_3707013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707090 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_3707090 : Nat := 118140960795 + 3707090 * 2 ^ 59
def prefixEnd_3707090 : Nat := 4983230072969 + 3 ^ 40 * 3707090 * 2
def baseEnd_3707090 : Nat := 1269012666317337484684273

theorem tailTrace_3707090 : CollatzResearch.WordTrace tailWord_3707090 prefixEnd_3707090 1269012666317337484684273 := by
  unfold tailWord_3707090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33802170034963381352951681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90139120093235683607871149 33802170034963381352951681)
  ·
    refine ⟨25351627526222536014713761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33802170034963381352951681 25351627526222536014713761)
    ·
      refine ⟨19013720644666902011035321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25351627526222536014713761 19013720644666902011035321)
      ·
        refine ⟨14260290483500176508276491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19013720644666902011035321 14260290483500176508276491)
        ·
          refine ⟨21390435725250264762414737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14260290483500176508276491 21390435725250264762414737)
          ·
            refine ⟨16042826793937698571811053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21390435725250264762414737 16042826793937698571811053)
            ·
              refine ⟨6016060047726636964429145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16042826793937698571811053 6016060047726636964429145)
              ·
                refine ⟨4512045035794977723321859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016060047726636964429145 4512045035794977723321859)
                ·
                  refine ⟨6768067553692466584982789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512045035794977723321859 6768067553692466584982789)
                  ·
                    refine ⟨1269012666317337484684273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768067553692466584982789 1269012666317337484684273)
                    ·
                      rfl

theorem cell22_3707090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_3707090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707090 prefixEnd_3707090 := by exact prefixLift 3707090
  have htrace : WordTrace (prefixWord ++ tailWord_3707090) baseStart_3707090 baseEnd_3707090 := by
    simpa [prefixWord, tailWord_3707090, baseEnd_3707090] using wordTrace_append hprefix tailTrace_3707090
  have hstable : (prefixWord ++ tailWord_3707090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707090).length < 2 ^ (prefixWord ++ tailWord_3707090).sum := by decide
  have hdescent : baseEnd_3707090 < baseStart_3707090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707122 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3707122 : Nat := 118140960795 + 3707122 * 2 ^ 59
def prefixEnd_3707122 : Nat := 4983230072969 + 3 ^ 40 * 3707122 * 2
def baseEnd_3707122 : Nat := 423007873523766689294725

theorem tailTrace_3707122 : CollatzResearch.WordTrace tailWord_3707122 prefixEnd_3707122 423007873523766689294725 := by
  unfold tailWord_3707122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33802461818934398719242905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90139898183825063251314413 33802461818934398719242905)
  ·
    refine ⟨25351846364200799039432179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33802461818934398719242905 25351846364200799039432179)
    ·
      refine ⟨38027769546301198559148269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25351846364200799039432179 38027769546301198559148269)
      ·
        refine ⟨14260413579862949459680601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38027769546301198559148269 14260413579862949459680601)
        ·
          refine ⟨10695310184897212094760451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14260413579862949459680601 10695310184897212094760451)
          ·
            refine ⟨16042965277345818142140677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10695310184897212094760451 16042965277345818142140677)
            ·
              refine ⟨3008055989502340901651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16042965277345818142140677 3008055989502340901651377)
              ·
                refine ⟨2256041992126755676238533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008055989502340901651377 2256041992126755676238533)
                ·
                  refine ⟨423007873523766689294725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2256041992126755676238533 423007873523766689294725)
                  ·
                    rfl

theorem cell22_3707122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3707122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707122 prefixEnd_3707122 := by exact prefixLift 3707122
  have htrace : WordTrace (prefixWord ++ tailWord_3707122) baseStart_3707122 baseEnd_3707122 := by
    simpa [prefixWord, tailWord_3707122, baseEnd_3707122] using wordTrace_append hprefix tailTrace_3707122
  have hstable : (prefixWord ++ tailWord_3707122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707122).length < 2 ^ (prefixWord ++ tailWord_3707122).sum := by decide
  have hdescent : baseEnd_3707122 < baseStart_3707122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707208 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_3707208 : Nat := 118140960795 + 3707208 * 2 ^ 59
def prefixEnd_3707208 : Nat := 4983230072969 + 3 ^ 40 * 3707208 * 2
def baseEnd_3707208 : Nat := 1269053060128824510233911

theorem tailTrace_3707208 : CollatzResearch.WordTrace tailWord_3707208 prefixEnd_3707208 1269053060128824510233911 := by
  unfold tailWord_3707208
  simp only [CollatzResearch.WordTrace]
  refine ⟨67606491976713015782301139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90141989302284021043068185 67606491976713015782301139)
  ·
    refine ⟨101409737965069523673451709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67606491976713015782301139 101409737965069523673451709)
    ·
      refine ⟨38028651736901071377544391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101409737965069523673451709 38028651736901071377544391)
      ·
        refine ⟨57042977605351607066316587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38028651736901071377544391 57042977605351607066316587)
        ·
          refine ⟨85564466408027410599474881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57042977605351607066316587 85564466408027410599474881)
          ·
            refine ⟨64173349806020557949606161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85564466408027410599474881 64173349806020557949606161)
            ·
              refine ⟨48130012354515418462204621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64173349806020557949606161 48130012354515418462204621)
              ·
                refine ⟨18048754632943281923326733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48130012354515418462204621 18048754632943281923326733)
                ·
                  refine ⟨6768282987353730721247525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18048754632943281923326733 6768282987353730721247525)
                  ·
                    refine ⟨1269053060128824510233911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768282987353730721247525 1269053060128824510233911)
                    ·
                      rfl

theorem cell22_3707208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_3707208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707208 prefixEnd_3707208 := by exact prefixLift 3707208
  have htrace : WordTrace (prefixWord ++ tailWord_3707208) baseStart_3707208 baseEnd_3707208 := by
    simpa [prefixWord, tailWord_3707208, baseEnd_3707208] using wordTrace_append hprefix tailTrace_3707208
  have hstable : (prefixWord ++ tailWord_3707208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707208).length < 2 ^ (prefixWord ++ tailWord_3707208).sum := by decide
  have hdescent : baseEnd_3707208 < baseStart_3707208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707240 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_3707240 : Nat := 118140960795 + 3707240 * 2 ^ 59
def prefixEnd_3707240 : Nat := 4983230072969 + 3 ^ 40 * 3707240 * 2
def baseEnd_3707240 : Nat := 423021338127595697811271

theorem tailTrace_3707240 : CollatzResearch.WordTrace tailWord_3707240 prefixEnd_3707240 423021338127595697811271 := by
  unfold tailWord_3707240
  simp only [CollatzResearch.WordTrace]
  refine ⟨67607075544655050514883587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90142767392873400686511449 67607075544655050514883587)
  ·
    refine ⟨101410613316982575772325381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67607075544655050514883587 101410613316982575772325381)
    ·
      refine ⟨19014489996934232957311009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101410613316982575772325381 19014489996934232957311009)
      ·
        refine ⟨14260867497700674717983257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19014489996934232957311009 14260867497700674717983257)
        ·
          refine ⟨10695650623275506038487443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14260867497700674717983257 10695650623275506038487443)
          ·
            refine ⟨16043475934913259057731165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10695650623275506038487443 16043475934913259057731165)
            ·
              refine ⟨6016303475592472146649187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16043475934913259057731165 6016303475592472146649187)
              ·
                refine ⟨9024455213388708219973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016303475592472146649187 9024455213388708219973781)
                ·
                  refine ⟨423021338127595697811271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9024455213388708219973781 423021338127595697811271)
                  ·
                    rfl

theorem cell22_3707240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_3707240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707240 prefixEnd_3707240 := by exact prefixLift 3707240
  have htrace : WordTrace (prefixWord ++ tailWord_3707240) baseStart_3707240 baseEnd_3707240 := by
    simpa [prefixWord, tailWord_3707240, baseEnd_3707240] using wordTrace_append hprefix tailTrace_3707240
  have hstable : (prefixWord ++ tailWord_3707240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707240).length < 2 ^ (prefixWord ++ tailWord_3707240).sum := by decide
  have hdescent : baseEnd_3707240 < baseStart_3707240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707268 : List Nat := [2, 3, 2, 1, 1, 2, 1, 10]
def baseStart_3707268 : Nat := 118140960795 + 3707268 * 2 ^ 59
def prefixEnd_3707268 : Nat := 4983230072969 + 3 ^ 40 * 3707268 * 2
def baseEnd_3707268 : Nat := 141008177706111594859303

theorem tailTrace_3707268 : CollatzResearch.WordTrace tailWord_3707268 prefixEnd_3707268 141008177706111594859303 := by
  unfold tailWord_3707268
  simp only [CollatzResearch.WordTrace]
  refine ⟨67607586166604330905893229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90143448222139107874524305 67607586166604330905893229)
  ·
    refine ⟨25352844812476624089709961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67607586166604330905893229 25352844812476624089709961)
    ·
      refine ⟨19014633609357468067282471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25352844812476624089709961 19014633609357468067282471)
      ·
        refine ⟨28521950414036202100923707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19014633609357468067282471 28521950414036202100923707)
        ·
          refine ⟨42782925621054303151385561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28521950414036202100923707 42782925621054303151385561)
          ·
            refine ⟨32087194215790727363539171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42782925621054303151385561 32087194215790727363539171)
            ·
              refine ⟨48130791323686091045308757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32087194215790727363539171 48130791323686091045308757)
              ·
                refine ⟨141008177706111594859303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48130791323686091045308757 141008177706111594859303)
                ·
                  rfl

theorem cell22_3707268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_3707268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707268 prefixEnd_3707268 := by exact prefixLift 3707268
  have htrace : WordTrace (prefixWord ++ tailWord_3707268) baseStart_3707268 baseEnd_3707268 := by
    simpa [prefixWord, tailWord_3707268, baseEnd_3707268] using wordTrace_append hprefix tailTrace_3707268
  have hstable : (prefixWord ++ tailWord_3707268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707268).length < 2 ^ (prefixWord ++ tailWord_3707268).sum := by decide
  have hdescent : baseEnd_3707268 < baseStart_3707268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707306 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3707306 : Nat := 118140960795 + 3707306 * 2 ^ 59
def prefixEnd_3707306 : Nat := 4983230072969 + 3 ^ 40 * 3707306 * 2
def baseEnd_3707306 : Nat := 1269086607531584921283611

theorem tailTrace_3707306 : CollatzResearch.WordTrace tailWord_3707306 prefixEnd_3707306 1269086607531584921283611 := by
  unfold tailWord_3707306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804139576767748575417443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90144372204713996201113181 33804139576767748575417443)
  ·
    refine ⟨50706209365151622863126165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33804139576767748575417443 50706209365151622863126165)
    ·
      refine ⟨2376853563991482321709039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50706209365151622863126165 2376853563991482321709039)
      ·
        refine ⟨3565280345987223482563559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376853563991482321709039 3565280345987223482563559)
        ·
          refine ⟨5347920518980835223845339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565280345987223482563559 5347920518980835223845339)
          ·
            refine ⟨8021880778471252835768009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347920518980835223845339 8021880778471252835768009)
            ·
              refine ⟨6016410583853439626826007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8021880778471252835768009 6016410583853439626826007)
              ·
                refine ⟨9024615875780159440239011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016410583853439626826007 9024615875780159440239011)
                ·
                  refine ⟨13536923813670239160358517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024615875780159440239011 13536923813670239160358517)
                  ·
                    refine ⟨1269086607531584921283611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13536923813670239160358517 1269086607531584921283611)
                    ·
                      rfl

theorem cell22_3707306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3707306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707306 prefixEnd_3707306 := by exact prefixLift 3707306
  have htrace : WordTrace (prefixWord ++ tailWord_3707306) baseStart_3707306 baseEnd_3707306 := by
    simpa [prefixWord, tailWord_3707306, baseEnd_3707306] using wordTrace_append hprefix tailTrace_3707306
  have hstable : (prefixWord ++ tailWord_3707306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707306).length < 2 ^ (prefixWord ++ tailWord_3707306).sum := by decide
  have hdescent : baseEnd_3707306 < baseStart_3707306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707328 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_3707328 : Nat := 118140960795 + 3707328 * 2 ^ 59
def prefixEnd_3707328 : Nat := 4983230072969 + 3 ^ 40 * 3707328 * 2
def baseEnd_3707328 : Nat := 1269094138581184197233543

theorem tailTrace_3707328 : CollatzResearch.WordTrace tailWord_3707328 prefixEnd_3707328 1269094138581184197233543 := by
  unfold tailWord_3707328
  simp only [CollatzResearch.WordTrace]
  refine ⟨67608680356495646029485319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90144907141994194705980425 67608680356495646029485319)
  ·
    refine ⟨101413020534743469044227979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67608680356495646029485319 101413020534743469044227979)
    ·
      refine ⟨152119530802115203566341969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101413020534743469044227979 152119530802115203566341969)
      ·
        refine ⟨114089648101586402674756477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152119530802115203566341969 114089648101586402674756477)
        ·
          refine ⟨42783618038094901003033679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114089648101586402674756477 42783618038094901003033679)
          ·
            refine ⟨64175427057142351504550519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42783618038094901003033679 64175427057142351504550519)
            ·
              refine ⟨96263140585713527256825779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64175427057142351504550519 96263140585713527256825779)
              ·
                refine ⟨144394710878570290885238669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96263140585713527256825779 144394710878570290885238669)
                ·
                  refine ⟨54148016579463859081964501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144394710878570290885238669 54148016579463859081964501)
                  ·
                    refine ⟨1269094138581184197233543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54148016579463859081964501 1269094138581184197233543)
                    ·
                      rfl

theorem cell22_3707328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_3707328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707328 prefixEnd_3707328 := by exact prefixLift 3707328
  have htrace : WordTrace (prefixWord ++ tailWord_3707328) baseStart_3707328 baseEnd_3707328 := by
    simpa [prefixWord, tailWord_3707328, baseEnd_3707328] using wordTrace_append hprefix tailTrace_3707328
  have hstable : (prefixWord ++ tailWord_3707328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707328).length < 2 ^ (prefixWord ++ tailWord_3707328).sum := by decide
  have hdescent : baseEnd_3707328 < baseStart_3707328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707377 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_3707377 : Nat := 118140960795 + 3707377 * 2 ^ 59
def prefixEnd_3707377 : Nat := 4983230072969 + 3 ^ 40 * 3707377 * 2
def baseEnd_3707377 : Nat := 1269110912282564402758393

theorem tailTrace_3707377 : CollatzResearch.WordTrace tailWord_3707377 prefixEnd_3707377 1269110912282564402758393 := by
  unfold tailWord_3707377
  simp only [CollatzResearch.WordTrace]
  refine ⟨135219147889813773427504385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90146098593209182285002923 135219147889813773427504385)
  ·
    refine ⟨101414360917360330070628289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135219147889813773427504385 101414360917360330070628289)
    ·
      refine ⟨76060770688020247552971217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101414360917360330070628289 76060770688020247552971217)
      ·
        refine ⟨57045578016015185664728413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76060770688020247552971217 57045578016015185664728413)
        ·
          refine ⟨21392091756005694624273155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57045578016015185664728413 21392091756005694624273155)
          ·
            refine ⟨32088137634008541936409733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21392091756005694624273155 32088137634008541936409733)
            ·
              refine ⟨6016525806376601613076825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32088137634008541936409733 6016525806376601613076825)
              ·
                refine ⟨4512394354782451209807619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016525806376601613076825 4512394354782451209807619)
                ·
                  refine ⟨6768591532173676814711429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512394354782451209807619 6768591532173676814711429)
                  ·
                    refine ⟨1269110912282564402758393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768591532173676814711429 1269110912282564402758393)
                    ·
                      rfl

theorem cell22_3707377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_3707377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707377 prefixEnd_3707377 := by exact prefixLift 3707377
  have htrace : WordTrace (prefixWord ++ tailWord_3707377) baseStart_3707377 baseEnd_3707377 := by
    simpa [prefixWord, tailWord_3707377, baseEnd_3707377] using wordTrace_append hprefix tailTrace_3707377
  have hstable : (prefixWord ++ tailWord_3707377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707377).length < 2 ^ (prefixWord ++ tailWord_3707377).sum := by decide
  have hdescent : baseEnd_3707377 < baseStart_3707377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707420 : List Nat := [2, 2, 3, 1, 2, 2, 1, 9]
def baseStart_3707420 : Nat := 118140960795 + 3707420 * 2 ^ 59
def prefixEnd_3707420 : Nat := 4983230072969 + 3 ^ 40 * 3707420 * 2
def baseEnd_3707420 : Nat := 141013959117925180437029

theorem tailTrace_3707420 : CollatzResearch.WordTrace tailWord_3707420 prefixEnd_3707420 141013959117925180437029 := by
  unfold tailWord_3707420
  simp only [CollatzResearch.WordTrace]
  refine ⟨67610358114328995885659857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90147144152438661180879809 67610358114328995885659857)
  ·
    refine ⟨50707768585746746914244893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67610358114328995885659857 50707768585746746914244893)
    ·
      refine ⟨19015413219655030092841835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50707768585746746914244893 19015413219655030092841835)
      ·
        refine ⟨28523119829482545139262753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19015413219655030092841835 28523119829482545139262753)
        ·
          refine ⟨21392339872111908854447065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28523119829482545139262753 21392339872111908854447065)
          ·
            refine ⟨16044254904083931640835299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21392339872111908854447065 16044254904083931640835299)
            ·
              refine ⟨24066382356125897461252949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16044254904083931640835299 24066382356125897461252949)
              ·
                refine ⟨141013959117925180437029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24066382356125897461252949 141013959117925180437029)
                ·
                  rfl

theorem cell22_3707420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_3707420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707420 prefixEnd_3707420 := by exact prefixLift 3707420
  have htrace : WordTrace (prefixWord ++ tailWord_3707420) baseStart_3707420 baseEnd_3707420 := by
    simpa [prefixWord, tailWord_3707420, baseEnd_3707420] using wordTrace_append hprefix tailTrace_3707420
  have hstable : (prefixWord ++ tailWord_3707420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707420).length < 2 ^ (prefixWord ++ tailWord_3707420).sum := by decide
  have hdescent : baseEnd_3707420 < baseStart_3707420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707428 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_3707428 : Nat := 118140960795 + 3707428 * 2 ^ 59
def prefixEnd_3707428 : Nat := 4983230072969 + 3 ^ 40 * 3707428 * 2
def baseEnd_3707428 : Nat := 1269128370624817269733237

theorem tailTrace_3707428 : CollatzResearch.WordTrace tailWord_3707428 prefixEnd_3707428 1269128370624817269733237 := by
  unfold tailWord_3707428
  simp only [CollatzResearch.WordTrace]
  refine ⟨67610504006314504568805469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90147338675086006091740625 67610504006314504568805469)
  ·
    refine ⟨25353939002367939213302051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67610504006314504568805469 25353939002367939213302051)
    ·
      refine ⟨38030908503551908819953077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25353939002367939213302051 38030908503551908819953077)
      ·
        refine ⟨3565397672207991451870601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38030908503551908819953077 3565397672207991451870601)
        ·
          refine ⟨2674048254155993588902951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565397672207991451870601 2674048254155993588902951)
          ·
            refine ⟨4011072381233990383354427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674048254155993588902951 4011072381233990383354427)
            ·
              refine ⟨6016608571850985575031641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011072381233990383354427 6016608571850985575031641)
              ·
                refine ⟨4512456428888239181273731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016608571850985575031641 4512456428888239181273731)
                ·
                  refine ⟨6768684643332358771910597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512456428888239181273731 6768684643332358771910597)
                  ·
                    refine ⟨1269128370624817269733237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768684643332358771910597 1269128370624817269733237)
                    ·
                      rfl

theorem cell22_3707428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_3707428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707428 prefixEnd_3707428 := by exact prefixLift 3707428
  have htrace : WordTrace (prefixWord ++ tailWord_3707428) baseStart_3707428 baseEnd_3707428 := by
    simpa [prefixWord, tailWord_3707428, baseEnd_3707428] using wordTrace_append hprefix tailTrace_3707428
  have hstable : (prefixWord ++ tailWord_3707428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707428).length < 2 ^ (prefixWord ++ tailWord_3707428).sum := by decide
  have hdescent : baseEnd_3707428 < baseStart_3707428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707454 : List Nat := [4, 2, 1, 4, 2, 9]
def baseStart_3707454 : Nat := 118140960795 + 3707454 * 2 ^ 59
def prefixEnd_3707454 : Nat := 4983230072969 + 3 ^ 40 * 3707454 * 2
def baseEnd_3707454 : Nat := 15668361369829158871397

theorem tailTrace_3707454 : CollatzResearch.WordTrace tailWord_3707454 prefixEnd_3707454 15668361369829158871397 := by
  unfold tailWord_3707454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902744538816851947257177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90147970873689877052038277 16902744538816851947257177)
  ·
    refine ⟨12677058404112638960442883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16902744538816851947257177 12677058404112638960442883)
    ·
      refine ⟨19015587606168958440664325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12677058404112638960442883 19015587606168958440664325)
      ·
        refine ⟨3565422676156679707624561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19015587606168958440664325 3565422676156679707624561)
        ·
          refine ⟨2674067007117509780718421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565422676156679707624561 2674067007117509780718421)
          ·
            refine ⟨15668361369829158871397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2674067007117509780718421 15668361369829158871397)
            ·
              rfl

theorem cell22_3707454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 9].length) (baseStart_3707454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707454 prefixEnd_3707454 := by exact prefixLift 3707454
  have htrace : WordTrace (prefixWord ++ tailWord_3707454) baseStart_3707454 baseEnd_3707454 := by
    simpa [prefixWord, tailWord_3707454, baseEnd_3707454] using wordTrace_append hprefix tailTrace_3707454
  have hstable : (prefixWord ++ tailWord_3707454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707454).length < 2 ^ (prefixWord ++ tailWord_3707454).sum := by decide
  have hdescent : baseEnd_3707454 < baseStart_3707454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707480 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_3707480 : Nat := 118140960795 + 3707480 * 2 ^ 59
def prefixEnd_3707480 : Nat := 4983230072969 + 3 ^ 40 * 3707480 * 2
def baseEnd_3707480 : Nat := 1269146171287506467433077

theorem tailTrace_3707480 : CollatzResearch.WordTrace tailWord_3707480 prefixEnd_3707480 1269146171287506467433077 := by
  unfold tailWord_3707480
  simp only [CollatzResearch.WordTrace]
  refine ⟨67611452304220311009251947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90148603072293748012335929 67611452304220311009251947)
  ·
    refine ⟨101417178456330466513877921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67611452304220311009251947 101417178456330466513877921)
    ·
      refine ⟨76062883842247849885408441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101417178456330466513877921 76062883842247849885408441)
      ·
        refine ⟨57047162881685887414056331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76062883842247849885408441 57047162881685887414056331)
        ·
          refine ⟨85570744322528831121084497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57047162881685887414056331 85570744322528831121084497)
          ·
            refine ⟨64178058241896623340813373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85570744322528831121084497 64178058241896623340813373)
            ·
              refine ⟨24066771840711233752805015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64178058241896623340813373 24066771840711233752805015)
              ·
                refine ⟨36100157761066850629207523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24066771840711233752805015 36100157761066850629207523)
                ·
                  refine ⟨54150236641600275943811285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36100157761066850629207523 54150236641600275943811285)
                  ·
                    refine ⟨1269146171287506467433077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54150236641600275943811285 1269146171287506467433077)
                    ·
                      rfl

theorem cell22_3707480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_3707480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707480 prefixEnd_3707480 := by exact prefixLift 3707480
  have htrace : WordTrace (prefixWord ++ tailWord_3707480) baseStart_3707480 baseEnd_3707480 := by
    simpa [prefixWord, tailWord_3707480, baseEnd_3707480] using wordTrace_append hprefix tailTrace_3707480
  have hstable : (prefixWord ++ tailWord_3707480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707480).length < 2 ^ (prefixWord ++ tailWord_3707480).sum := by decide
  have hdescent : baseEnd_3707480 < baseStart_3707480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707512 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_3707512 : Nat := 118140960795 + 3707512 * 2 ^ 59
def prefixEnd_3707512 : Nat := 4983230072969 + 3 ^ 40 * 3707512 * 2
def baseEnd_3707512 : Nat := 1269157125541469050632979

theorem tailTrace_3707512 : CollatzResearch.WordTrace tailWord_3707512 prefixEnd_3707512 1269157125541469050632979 := by
  unfold tailWord_3707512
  simp only [CollatzResearch.WordTrace]
  refine ⟨67612035872162345741834395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90149381162883127655779193 67612035872162345741834395)
  ·
    refine ⟨101418053808243518612751593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67612035872162345741834395 101418053808243518612751593)
    ·
      refine ⟨76063540356182638959563695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101418053808243518612751593 76063540356182638959563695)
      ·
        refine ⟨114095310534273958439345543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76063540356182638959563695 114095310534273958439345543)
        ·
          refine ⟨171142965801410937659018315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114095310534273958439345543 171142965801410937659018315)
          ·
            refine ⟨256714448702116406488527473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171142965801410937659018315 256714448702116406488527473)
            ·
              refine ⟨192535836526587304866395605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256714448702116406488527473 192535836526587304866395605)
              ·
                refine ⟨4512558668591889957806147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192535836526587304866395605 4512558668591889957806147)
                ·
                  refine ⟨6768838002887834936709221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512558668591889957806147 6768838002887834936709221)
                  ·
                    refine ⟨1269157125541469050632979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768838002887834936709221 1269157125541469050632979)
                    ·
                      rfl

theorem cell22_3707512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_3707512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707512 prefixEnd_3707512 := by exact prefixLift 3707512
  have htrace : WordTrace (prefixWord ++ tailWord_3707512) baseStart_3707512 baseEnd_3707512 := by
    simpa [prefixWord, tailWord_3707512, baseEnd_3707512] using wordTrace_append hprefix tailTrace_3707512
  have hstable : (prefixWord ++ tailWord_3707512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707512).length < 2 ^ (prefixWord ++ tailWord_3707512).sum := by decide
  have hdescent : baseEnd_3707512 < baseStart_3707512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707527 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 6]
def baseStart_3707527 : Nat := 118140960795 + 3707527 * 2 ^ 59
def prefixEnd_3707527 : Nat := 4983230072969 + 3 ^ 40 * 3707527 * 2
def baseEnd_3707527 : Nat := 423054086782671337169311

theorem tailTrace_3707527 : CollatzResearch.WordTrace tailWord_3707527 prefixEnd_3707527 423054086782671337169311 := by
  unfold tailWord_3707527
  simp only [CollatzResearch.WordTrace]
  refine ⟨135224618839270349045464835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90149745892846899363643223 135224618839270349045464835)
  ·
    refine ⟨202836928258905523568197253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135224618839270349045464835 202836928258905523568197253)
    ·
      refine ⟨38031924048544785669036985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202836928258905523568197253 38031924048544785669036985)
      ·
        refine ⟨28523943036408589251777739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38031924048544785669036985 28523943036408589251777739)
        ·
          refine ⟨42785914554612883877666609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28523943036408589251777739 42785914554612883877666609)
          ·
            refine ⟨32089435915959662908249957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42785914554612883877666609 32089435915959662908249957)
            ·
              refine ⟨6016769234242436795296867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32089435915959662908249957 6016769234242436795296867)
              ·
                refine ⟨9025153851363655192945301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016769234242436795296867 9025153851363655192945301)
                ·
                  refine ⟨423054086782671337169311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9025153851363655192945301 423054086782671337169311)
                  ·
                    rfl

theorem cell22_3707527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 6].length) (baseStart_3707527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707527 prefixEnd_3707527 := by exact prefixLift 3707527
  have htrace : WordTrace (prefixWord ++ tailWord_3707527) baseStart_3707527 baseEnd_3707527 := by
    simpa [prefixWord, tailWord_3707527, baseEnd_3707527] using wordTrace_append hprefix tailTrace_3707527
  have hstable : (prefixWord ++ tailWord_3707527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707527).length < 2 ^ (prefixWord ++ tailWord_3707527).sum := by decide
  have hdescent : baseEnd_3707527 < baseStart_3707527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707557 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3707557 : Nat := 118140960795 + 3707557 * 2 ^ 59
def prefixEnd_3707557 : Nat := 4983230072969 + 3 ^ 40 * 3707557 * 2
def baseEnd_3707557 : Nat := 1269172529961103933257841

theorem tailTrace_3707557 : CollatzResearch.WordTrace tailWord_3707557 prefixEnd_3707557 1269172529961103933257841 := by
  unfold tailWord_3707557
  simp only [CollatzResearch.WordTrace]
  refine ⟨135225713029161664169056925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90150475352774442779371283 135225713029161664169056925)
  ·
    refine ⟨50709642385935624063396347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135225713029161664169056925 50709642385935624063396347)
    ·
      refine ⟨76064463578903436095094521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50709642385935624063396347 76064463578903436095094521)
      ·
        refine ⟨57048347684177577071320891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76064463578903436095094521 57048347684177577071320891)
        ·
          refine ⟨85572521526266365606981337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57048347684177577071320891 85572521526266365606981337)
          ·
            refine ⟨64179391144699774205236003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85572521526266365606981337 64179391144699774205236003)
            ·
              refine ⟨96269086717049661307854005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64179391144699774205236003 96269086717049661307854005)
              ·
                refine ⟨9025226879723405747611313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96269086717049661307854005 9025226879723405747611313)
                ·
                  refine ⟨6768920159792554310708485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9025226879723405747611313 6768920159792554310708485)
                  ·
                    refine ⟨1269172529961103933257841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768920159792554310708485 1269172529961103933257841)
                    ·
                      rfl

theorem cell22_3707557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3707557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707557 prefixEnd_3707557 := by exact prefixLift 3707557
  have htrace : WordTrace (prefixWord ++ tailWord_3707557) baseStart_3707557 baseEnd_3707557 := by
    simpa [prefixWord, tailWord_3707557, baseEnd_3707557] using wordTrace_append hprefix tailTrace_3707557
  have hstable : (prefixWord ++ tailWord_3707557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707557).length < 2 ^ (prefixWord ++ tailWord_3707557).sum := by decide
  have hdescent : baseEnd_3707557 < baseStart_3707557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707632 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_3707632 : Nat := 118140960795 + 3707632 * 2 ^ 59
def prefixEnd_3707632 : Nat := 4983230072969 + 3 ^ 40 * 3707632 * 2
def baseEnd_3707632 : Nat := 1269198203993828737632611

theorem tailTrace_3707632 : CollatzResearch.WordTrace tailWord_3707632 prefixEnd_3707632 1269198203993828737632611 := by
  unfold tailWord_3707632
  simp only [CollatzResearch.WordTrace]
  refine ⟨67614224251944975989018575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90152299002593301318691433 67614224251944975989018575)
  ·
    refine ⟨101421336377917463983527863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67614224251944975989018575 101421336377917463983527863)
    ·
      refine ⟨152132004566876195975291795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101421336377917463983527863 152132004566876195975291795)
      ·
        refine ⟨228198006850314293962937693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152132004566876195975291795 228198006850314293962937693)
        ·
          refine ⟨85574252568867860236101635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228198006850314293962937693 85574252568867860236101635)
          ·
            refine ⟨128361378853301790354152453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85574252568867860236101635 128361378853301790354152453)
            ·
              refine ⟨24067758534994085691403585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128361378853301790354152453 24067758534994085691403585)
              ·
                refine ⟨18050818901245564268552689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24067758534994085691403585 18050818901245564268552689)
                ·
                  refine ⟨13538114175934173201414517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18050818901245564268552689 13538114175934173201414517)
                  ·
                    refine ⟨1269198203993828737632611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13538114175934173201414517 1269198203993828737632611)
                    ·
                      rfl

theorem cell22_3707632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_3707632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707632 prefixEnd_3707632 := by exact prefixLift 3707632
  have htrace : WordTrace (prefixWord ++ tailWord_3707632) baseStart_3707632 baseEnd_3707632 := by
    simpa [prefixWord, tailWord_3707632, baseEnd_3707632] using wordTrace_append hprefix tailTrace_3707632
  have hstable : (prefixWord ++ tailWord_3707632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707632).length < 2 ^ (prefixWord ++ tailWord_3707632).sum := by decide
  have hdescent : baseEnd_3707632 < baseStart_3707632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707634 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_3707634 : Nat := 118140960795 + 3707634 * 2 ^ 59
def prefixEnd_3707634 : Nat := 4983230072969 + 3 ^ 40 * 3707634 * 2
def baseEnd_3707634 : Nat := 423066296211567133027535

theorem tailTrace_3707634 : CollatzResearch.WordTrace tailWord_3707634 prefixEnd_3707634 423066296211567133027535 := by
  unfold tailWord_3707634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33807130362470676579902489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90152347633255137546406637 33807130362470676579902489)
  ·
    refine ⟨25355347771853007434926867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33807130362470676579902489 25355347771853007434926867)
    ·
      refine ⟨38033021657779511152390301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25355347771853007434926867 38033021657779511152390301)
      ·
        refine ⟨14262383121667316682146363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38033021657779511152390301 14262383121667316682146363)
        ·
          refine ⟨21393574682500975023219545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262383121667316682146363 21393574682500975023219545)
          ·
            refine ⟨16045181011875731267414659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21393574682500975023219545 16045181011875731267414659)
            ·
              refine ⟨24067771517813596901121989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16045181011875731267414659 24067771517813596901121989)
              ·
                refine ⟨4512707159590049418960373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24067771517813596901121989 4512707159590049418960373)
                ·
                  refine ⟨423066296211567133027535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4512707159590049418960373 423066296211567133027535)
                  ·
                    rfl

theorem cell22_3707634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_3707634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707634 prefixEnd_3707634 := by exact prefixLift 3707634
  have htrace : WordTrace (prefixWord ++ tailWord_3707634) baseStart_3707634 baseEnd_3707634 := by
    simpa [prefixWord, tailWord_3707634, baseEnd_3707634] using wordTrace_append hprefix tailTrace_3707634
  have hstable : (prefixWord ++ tailWord_3707634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707634).length < 2 ^ (prefixWord ++ tailWord_3707634).sum := by decide
  have hdescent : baseEnd_3707634 < baseStart_3707634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707638 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3707638 : Nat := 118140960795 + 3707638 * 2 ^ 59
def prefixEnd_3707638 : Nat := 4983230072969 + 3 ^ 40 * 3707638 * 2
def baseEnd_3707638 : Nat := 1269200257916446721982593

theorem tailTrace_3707638 : CollatzResearch.WordTrace tailWord_3707638 prefixEnd_3707638 1269200257916446721982593 := by
  unfold tailWord_3707638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451791708866763437672223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90152444894578810001837045 8451791708866763437672223)
  ·
    refine ⟨12677687563300145156508335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8451791708866763437672223 12677687563300145156508335)
    ·
      refine ⟨19016531344950217734762503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12677687563300145156508335 19016531344950217734762503)
      ·
        refine ⟨28524797017425326602143755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19016531344950217734762503 28524797017425326602143755)
        ·
          refine ⟨42787195526137989903215633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28524797017425326602143755 42787195526137989903215633)
          ·
            refine ⟨32090396644603492427411725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42787195526137989903215633 32090396644603492427411725)
            ·
              refine ⟨12033898741726309660279397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32090396644603492427411725 12033898741726309660279397)
              ·
                refine ⟨2256356014073683061302387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12033898741726309660279397 2256356014073683061302387)
                ·
                  refine ⟨3384534021110524591953581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256356014073683061302387 3384534021110524591953581)
                  ·
                    refine ⟨1269200257916446721982593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3384534021110524591953581 1269200257916446721982593)
                    ·
                      rfl

theorem cell22_3707638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3707638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707638 prefixEnd_3707638 := by exact prefixLift 3707638
  have htrace : WordTrace (prefixWord ++ tailWord_3707638) baseStart_3707638 baseEnd_3707638 := by
    simpa [prefixWord, tailWord_3707638, baseEnd_3707638] using wordTrace_append hprefix tailTrace_3707638
  have hstable : (prefixWord ++ tailWord_3707638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707638).length < 2 ^ (prefixWord ++ tailWord_3707638).sum := by decide
  have hdescent : baseEnd_3707638 < baseStart_3707638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707711 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 1, 5]
def baseStart_3707711 : Nat := 118140960795 + 3707711 * 2 ^ 59
def prefixEnd_3707711 : Nat := 4983230072969 + 3 ^ 40 * 3707711 * 2
def baseEnd_3707711 : Nat := 1269225247308298864907369

theorem tailTrace_3707711 : CollatzResearch.WordTrace tailWord_3707711 prefixEnd_3707711 1269225247308298864907369 := by
  unfold tailWord_3707711
  simp only [CollatzResearch.WordTrace]
  refine ⟨135231329870603748470162987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90154219913735832313441991 135231329870603748470162987)
  ·
    refine ⟨202846994805905622705244481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135231329870603748470162987 202846994805905622705244481)
    ·
      refine ⟨152135246104429217028933361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202846994805905622705244481 152135246104429217028933361)
      ·
        refine ⟨114101434578321912771700021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152135246104429217028933361 114101434578321912771700021)
        ·
          refine ⟨10697009491717679322346877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114101434578321912771700021 10697009491717679322346877)
          ·
            refine ⟨4011378559394129745880079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10697009491717679322346877 4011378559394129745880079)
            ·
              refine ⟨6017067839091194618820119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011378559394129745880079 6017067839091194618820119)
              ·
                refine ⟨9025601758636791928230179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017067839091194618820119 9025601758636791928230179)
                ·
                  refine ⟨13538402637955187892345269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025601758636791928230179 13538402637955187892345269)
                  ·
                    refine ⟨1269225247308298864907369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13538402637955187892345269 1269225247308298864907369)
                    ·
                      rfl

theorem cell22_3707711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_3707711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707711 prefixEnd_3707711 := by exact prefixLift 3707711
  have htrace : WordTrace (prefixWord ++ tailWord_3707711) baseStart_3707711 baseEnd_3707711 := by
    simpa [prefixWord, tailWord_3707711, baseEnd_3707711] using wordTrace_append hprefix tailTrace_3707711
  have hstable : (prefixWord ++ tailWord_3707711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707711).length < 2 ^ (prefixWord ++ tailWord_3707711).sum := by decide
  have hdescent : baseEnd_3707711 < baseStart_3707711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707724 : List Nat := [2, 2, 1, 3, 3, 2, 1, 8]
def baseStart_3707724 : Nat := 118140960795 + 3707724 * 2 ^ 59
def prefixEnd_3707724 : Nat := 4983230072969 + 3 ^ 40 * 3707724 * 2
def baseEnd_3707724 : Nat := 141025521941552351592481

theorem tailTrace_3707724 : CollatzResearch.WordTrace tailWord_3707724 prefixEnd_3707724 141025521941552351592481 := by
  unfold tailWord_3707724
  simp only [CollatzResearch.WordTrace]
  refine ⟨67615902009778325845193113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90154536013037767793590817 67615902009778325845193113)
  ·
    refine ⟨50711926507333744383894835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67615902009778325845193113 50711926507333744383894835)
    ·
      refine ⟨76067889761000616575842253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50711926507333744383894835 76067889761000616575842253)
      ·
        refine ⟨28525458660375231215940845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76067889761000616575842253 28525458660375231215940845)
        ·
          refine ⟨10697046997640711705977817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28525458660375231215940845 10697046997640711705977817)
          ·
            refine ⟨8022785248230533779483363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10697046997640711705977817 8022785248230533779483363)
            ·
              refine ⟨12034177872345800669225045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8022785248230533779483363 12034177872345800669225045)
              ·
                refine ⟨141025521941552351592481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12034177872345800669225045 141025521941552351592481)
                ·
                  rfl

theorem cell22_3707724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_3707724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707724 prefixEnd_3707724 := by exact prefixLift 3707724
  have htrace : WordTrace (prefixWord ++ tailWord_3707724) baseStart_3707724 baseEnd_3707724 := by
    simpa [prefixWord, tailWord_3707724, baseEnd_3707724] using wordTrace_append hprefix tailTrace_3707724
  have hstable : (prefixWord ++ tailWord_3707724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707724).length < 2 ^ (prefixWord ++ tailWord_3707724).sum := by decide
  have hdescent : baseEnd_3707724 < baseStart_3707724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707807 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 1, 3]
def baseStart_3707807 : Nat := 118140960795 + 3707807 * 2 ^ 59
def prefixEnd_3707807 : Nat := 4983230072969 + 3 ^ 40 * 3707807 * 2
def baseEnd_3707807 : Nat := 1269258110070186614507075

theorem tailTrace_3707807 : CollatzResearch.WordTrace tailWord_3707807 prefixEnd_3707807 1269258110070186614507075 := by
  unfold tailWord_3707807
  simp only [CollatzResearch.WordTrace]
  refine ⟨135234831278255956865657675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90156554185503971243771783 135234831278255956865657675)
  ·
    refine ⟨202852246917383935298486513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135234831278255956865657675 202852246917383935298486513)
    ·
      refine ⟨152139185188037951473864885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202852246917383935298486513 152139185188037951473864885)
      ·
        refine ⟨14263048611378557950674833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152139185188037951473864885 14263048611378557950674833)
        ·
          refine ⟨10697286458533918463006125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14263048611378557950674833 10697286458533918463006125)
          ·
            refine ⟨4011482421950219423627297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10697286458533918463006125 4011482421950219423627297)
            ·
              refine ⟨3008611816462664567720473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011482421950219423627297 3008611816462664567720473)
              ·
                refine ⟨2256458862346998425790355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008611816462664567720473 2256458862346998425790355)
                ·
                  refine ⟨3384688293520497638685533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256458862346998425790355 3384688293520497638685533)
                  ·
                    refine ⟨1269258110070186614507075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3384688293520497638685533 1269258110070186614507075)
                    ·
                      rfl

theorem cell22_3707807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_3707807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707807 prefixEnd_3707807 := by exact prefixLift 3707807
  have htrace : WordTrace (prefixWord ++ tailWord_3707807) baseStart_3707807 baseEnd_3707807 := by
    simpa [prefixWord, tailWord_3707807, baseEnd_3707807] using wordTrace_append hprefix tailTrace_3707807
  have hstable : (prefixWord ++ tailWord_3707807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707807).length < 2 ^ (prefixWord ++ tailWord_3707807).sum := by decide
  have hdescent : baseEnd_3707807 < baseStart_3707807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707919 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_3707919 : Nat := 118140960795 + 3707919 * 2 ^ 59
def prefixEnd_3707919 : Nat := 4983230072969 + 3 ^ 40 * 3707919 * 2
def baseEnd_3707919 : Nat := 1269296449959055655706731

theorem tailTrace_3707919 : CollatzResearch.WordTrace tailWord_3707919 prefixEnd_3707919 1269296449959055655706731 := by
  unfold tailWord_3707919
  simp only [CollatzResearch.WordTrace]
  refine ⟨135238916253850199993734811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90159277502566799995823207 135238916253850199993734811)
  ·
    refine ⟨202858374380775299990602217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135238916253850199993734811 202858374380775299990602217)
    ·
      refine ⟨152143780785581474992951663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202858374380775299990602217 152143780785581474992951663)
      ·
        refine ⟨228215671178372212489427495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152143780785581474992951663 228215671178372212489427495)
        ·
          refine ⟨342323506767558318734141243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228215671178372212489427495 342323506767558318734141243)
          ·
            refine ⟨513485260151337478101211865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342323506767558318734141243 513485260151337478101211865)
            ·
              refine ⟨385113945113503108575908899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513485260151337478101211865 385113945113503108575908899)
              ·
                refine ⟨577670917670254662863863349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385113945113503108575908899 577670917670254662863863349)
                ·
                  refine ⟨54156648531586374643487189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577670917670254662863863349 54156648531586374643487189)
                  ·
                    refine ⟨1269296449959055655706731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54156648531586374643487189 1269296449959055655706731)
                    ·
                      rfl

theorem cell22_3707919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_3707919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707919 prefixEnd_3707919 := by exact prefixLift 3707919
  have htrace : WordTrace (prefixWord ++ tailWord_3707919) baseStart_3707919 baseEnd_3707919 := by
    simpa [prefixWord, tailWord_3707919, baseEnd_3707919] using wordTrace_append hprefix tailTrace_3707919
  have hstable : (prefixWord ++ tailWord_3707919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707919).length < 2 ^ (prefixWord ++ tailWord_3707919).sum := by decide
  have hdescent : baseEnd_3707919 < baseStart_3707919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707925 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_3707925 : Nat := 118140960795 + 3707925 * 2 ^ 59
def prefixEnd_3707925 : Nat := 4983230072969 + 3 ^ 40 * 3707925 * 2
def baseEnd_3707925 : Nat := 1269298503881673640056713

theorem tailTrace_3707925 : CollatzResearch.WordTrace tailWord_3707925 prefixEnd_3707925 1269298503881673640056713 := by
  unfold tailWord_3707925
  simp only [CollatzResearch.WordTrace]
  refine ⟨135239135091828463018453229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90159423394552308678968819 135239135091828463018453229)
  ·
    refine ⟨50714675659435673631919961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135239135091828463018453229 50714675659435673631919961)
    ·
      refine ⟨38036006744576755223939971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50714675659435673631919961 38036006744576755223939971)
      ·
        refine ⟨57054010116865132835909957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38036006744576755223939971 57054010116865132835909957)
        ·
          refine ⟨10697626896912212406733117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57054010116865132835909957 10697626896912212406733117)
          ·
            refine ⟨4011610086342079652524919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10697626896912212406733117 4011610086342079652524919)
            ·
              refine ⟨6017415129513119478787379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011610086342079652524919 6017415129513119478787379)
              ·
                refine ⟨9026122694269679218181069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017415129513119478787379 9026122694269679218181069)
                ·
                  refine ⟨3384796010351129706817901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9026122694269679218181069 3384796010351129706817901)
                  ·
                    refine ⟨1269298503881673640056713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3384796010351129706817901 1269298503881673640056713)
                    ·
                      rfl

theorem cell22_3707925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_3707925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707925 prefixEnd_3707925 := by exact prefixLift 3707925
  have htrace : WordTrace (prefixWord ++ tailWord_3707925) baseStart_3707925 baseEnd_3707925 := by
    simpa [prefixWord, tailWord_3707925, baseEnd_3707925] using wordTrace_append hprefix tailTrace_3707925
  have hstable : (prefixWord ++ tailWord_3707925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707925).length < 2 ^ (prefixWord ++ tailWord_3707925).sum := by decide
  have hdescent : baseEnd_3707925 < baseStart_3707925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3707938 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3707938 : Nat := 118140960795 + 3707938 * 2 ^ 59
def prefixEnd_3707938 : Nat := 4983230072969 + 3 ^ 40 * 3707938 * 2
def baseEnd_3707938 : Nat := 423100984682448646493891

theorem tailTrace_3707938 : CollatzResearch.WordTrace tailWord_3707938 prefixEnd_3707938 423100984682448646493891 := by
  unfold tailWord_3707938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33809902310195341559669117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90159739493854244159117645 33809902310195341559669117)
  ·
    refine ⟨12678713366323253084875919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33809902310195341559669117 12678713366323253084875919)
    ·
      refine ⟨19018070049484879627313879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12678713366323253084875919 19018070049484879627313879)
      ·
        refine ⟨28527105074227319440970819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19018070049484879627313879 28527105074227319440970819)
        ·
          refine ⟨42790657611340979161456229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28527105074227319440970819 42790657611340979161456229)
          ·
            refine ⟨8023248302126433592773043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42790657611340979161456229 8023248302126433592773043)
            ·
              refine ⟨12034872453189650389159565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023248302126433592773043 12034872453189650389159565)
              ·
                refine ⟨4513077169946118895934837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12034872453189650389159565 4513077169946118895934837)
                ·
                  refine ⟨423100984682448646493891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4513077169946118895934837 423100984682448646493891)
                  ·
                    rfl

theorem cell22_3707938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3707938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3707938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3707938 prefixEnd_3707938 := by exact prefixLift 3707938
  have htrace : WordTrace (prefixWord ++ tailWord_3707938) baseStart_3707938 baseEnd_3707938 := by
    simpa [prefixWord, tailWord_3707938, baseEnd_3707938] using wordTrace_append hprefix tailTrace_3707938
  have hstable : (prefixWord ++ tailWord_3707938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3707938).length < 2 ^ (prefixWord ++ tailWord_3707938).sum := by decide
  have hdescent : baseEnd_3707938 < baseStart_3707938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3707938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708013 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3708013 : Nat := 118140960795 + 3708013 * 2 ^ 59
def prefixEnd_3708013 : Nat := 4983230072969 + 3 ^ 40 * 3708013 * 2
def baseEnd_3708013 : Nat := 1269328628080070743856443

theorem tailTrace_3708013 : CollatzResearch.WordTrace tailWord_3708013 prefixEnd_3708013 1269328628080070743856443 := by
  unfold tailWord_3708013
  simp only [CollatzResearch.WordTrace]
  refine ⟨135242344715509654047656693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90161563143673102698437795 135242344715509654047656693)
  ·
    refine ⟨12678969817079030066967815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135242344715509654047656693 12678969817079030066967815)
    ·
      refine ⟨19018454725618545100451723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12678969817079030066967815 19018454725618545100451723)
      ·
        refine ⟨28527682088427817650677585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19018454725618545100451723 28527682088427817650677585)
        ·
          refine ⟨21395761566320863238008189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28527682088427817650677585 21395761566320863238008189)
          ·
            refine ⟨8023410587370323714253071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21395761566320863238008189 8023410587370323714253071)
            ·
              refine ⟨12035115881055485571379607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023410587370323714253071 12035115881055485571379607)
              ·
                refine ⟨18052673821583228357069411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12035115881055485571379607 18052673821583228357069411)
                ·
                  refine ⟨27079010732374842535604117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18052673821583228357069411 27079010732374842535604117)
                  ·
                    refine ⟨1269328628080070743856443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27079010732374842535604117 1269328628080070743856443)
                    ·
                      rfl

theorem cell22_3708013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3708013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708013 prefixEnd_3708013 := by exact prefixLift 3708013
  have htrace : WordTrace (prefixWord ++ tailWord_3708013) baseStart_3708013 baseEnd_3708013 := by
    simpa [prefixWord, tailWord_3708013, baseEnd_3708013] using wordTrace_append hprefix tailTrace_3708013
  have hstable : (prefixWord ++ tailWord_3708013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708013).length < 2 ^ (prefixWord ++ tailWord_3708013).sum := by decide
  have hdescent : baseEnd_3708013 < baseStart_3708013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708060 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3708060 : Nat := 118140960795 + 3708060 * 2 ^ 59
def prefixEnd_3708060 : Nat := 4983230072969 + 3 ^ 40 * 3708060 * 2
def baseEnd_3708060 : Nat := 1269344717140578287931299

theorem tailTrace_3708060 : CollatzResearch.WordTrace tailWord_3708060 prefixEnd_3708060 1269344717140578287931299 := by
  unfold tailWord_3708060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67622029473169690537308817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90162705964226254049745089 67622029473169690537308817)
  ·
    refine ⟨50716522104877267902981613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67622029473169690537308817 50716522104877267902981613)
    ·
      refine ⟨19018695789328975463618105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50716522104877267902981613 19018695789328975463618105)
      ·
        refine ⟨14264021841996731597713579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19018695789328975463618105 14264021841996731597713579)
        ·
          refine ⟨21396032762995097396570369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14264021841996731597713579 21396032762995097396570369)
          ·
            refine ⟨16047024572246323047427777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21396032762995097396570369 16047024572246323047427777)
            ·
              refine ⟨12035268429184742285570833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16047024572246323047427777 12035268429184742285570833)
              ·
                refine ⟨9026451321888556714178125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12035268429184742285570833 9026451321888556714178125)
                ·
                  refine ⟨3384919245708208767816797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9026451321888556714178125 3384919245708208767816797)
                  ·
                    refine ⟨1269344717140578287931299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3384919245708208767816797 1269344717140578287931299)
                    ·
                      rfl

theorem cell22_3708060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3708060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708060 prefixEnd_3708060 := by exact prefixLift 3708060
  have htrace : WordTrace (prefixWord ++ tailWord_3708060) baseStart_3708060 baseEnd_3708060 := by
    simpa [prefixWord, tailWord_3708060, baseEnd_3708060] using wordTrace_append hprefix tailTrace_3708060
  have hstable : (prefixWord ++ tailWord_3708060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708060).length < 2 ^ (prefixWord ++ tailWord_3708060).sum := by decide
  have hdescent : baseEnd_3708060 < baseStart_3708060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708062 : List Nat := [4, 3, 1, 1, 2, 3, 2, 6]
def baseStart_3708062 : Nat := 118140960795 + 3708062 * 2 ^ 59
def prefixEnd_3708062 : Nat := 4983230072969 + 3 ^ 40 * 3708062 * 2
def baseEnd_3708062 : Nat := 141038377975716772153477

theorem tailTrace_3708062 : CollatzResearch.WordTrace tailWord_3708062 prefixEnd_3708062 141038377975716772153477 := by
  unfold tailWord_3708062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16905516486541516927023805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90162754594888090277460293 16905516486541516927023805)
  ·
    refine ⟨6339568682453068847633927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16905516486541516927023805 6339568682453068847633927)
    ·
      refine ⟨9509353023679603271450891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6339568682453068847633927 9509353023679603271450891)
      ·
        refine ⟨14264029535519404907176337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509353023679603271450891 14264029535519404907176337)
        ·
          refine ⟨10698022151639553680382253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14264029535519404907176337 10698022151639553680382253)
          ·
            refine ⟨4011758306864832630143345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10698022151639553680382253 4011758306864832630143345)
            ·
              refine ⟨3008818730148624472607509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011758306864832630143345 3008818730148624472607509)
              ·
                refine ⟨141038377975716772153477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3008818730148624472607509 141038377975716772153477)
                ·
                  rfl

theorem cell22_3708062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_3708062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708062 prefixEnd_3708062 := by exact prefixLift 3708062
  have htrace : WordTrace (prefixWord ++ tailWord_3708062) baseStart_3708062 baseEnd_3708062 := by
    simpa [prefixWord, tailWord_3708062, baseEnd_3708062] using wordTrace_append hprefix tailTrace_3708062
  have hstable : (prefixWord ++ tailWord_3708062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708062).length < 2 ^ (prefixWord ++ tailWord_3708062).sum := by decide
  have hdescent : baseEnd_3708062 < baseStart_3708062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708120 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_3708120 : Nat := 118140960795 + 3708120 * 2 ^ 59
def prefixEnd_3708120 : Nat := 4983230072969 + 3 ^ 40 * 3708120 * 2
def baseEnd_3708120 : Nat := 1269365256366758131431115

theorem tailTrace_3708120 : CollatzResearch.WordTrace tailWord_3708120 prefixEnd_3708120 1269365256366758131431115 := by
  unfold tailWord_3708120
  simp only [CollatzResearch.WordTrace]
  refine ⟨67623123663061005660900907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90164164884081340881201209 67623123663061005660900907)
  ·
    refine ⟨101434685494591508491351361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67623123663061005660900907 101434685494591508491351361)
    ·
      refine ⟨76076014120943631368513521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101434685494591508491351361 76076014120943631368513521)
      ·
        refine ⟨57057010590707723526385141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76076014120943631368513521 57057010590707723526385141)
        ·
          refine ⟨5349094742878849080598607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57057010590707723526385141 5349094742878849080598607)
          ·
            refine ⟨8023642114318273620897911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5349094742878849080598607 8023642114318273620897911)
            ·
              refine ⟨12035463171477410431346867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023642114318273620897911 12035463171477410431346867)
              ·
                refine ⟨18053194757216115647020301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12035463171477410431346867 18053194757216115647020301)
                ·
                  refine ⟨6769948033956043367632613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18053194757216115647020301 6769948033956043367632613)
                  ·
                    refine ⟨1269365256366758131431115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6769948033956043367632613 1269365256366758131431115)
                    ·
                      rfl

theorem cell22_3708120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_3708120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708120 prefixEnd_3708120 := by exact prefixLift 3708120
  have htrace : WordTrace (prefixWord ++ tailWord_3708120) baseStart_3708120 baseEnd_3708120 := by
    simpa [prefixWord, tailWord_3708120, baseEnd_3708120] using wordTrace_append hprefix tailTrace_3708120
  have hstable : (prefixWord ++ tailWord_3708120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708120).length < 2 ^ (prefixWord ++ tailWord_3708120).sum := by decide
  have hdescent : baseEnd_3708120 < baseStart_3708120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708163 : List Nat := [1, 1, 1, 3, 2, 4, 3, 7]
def baseStart_3708163 : Nat := 118140960795 + 3708163 * 2 ^ 59
def prefixEnd_3708163 : Nat := 4983230072969 + 3 ^ 40 * 3708163 * 2
def baseEnd_3708163 : Nat := 141042219571724483622887

theorem tailTrace_3708163 : CollatzResearch.WordTrace tailWord_3708163 prefixEnd_3708163 141042219571724483622887 := by
  unfold tailWord_3708163
  simp only [CollatzResearch.WordTrace]
  refine ⟨135247815664966229665617143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90165210443310819777078095 135247815664966229665617143)
  ·
    refine ⟨202871723497449344498425715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135247815664966229665617143 202871723497449344498425715)
    ·
      refine ⟨304307585246174016747638573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202871723497449344498425715 304307585246174016747638573)
      ·
        refine ⟨114115344467315256280364465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304307585246174016747638573 114115344467315256280364465)
        ·
          refine ⟨85586508350486442210273349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114115344467315256280364465 85586508350486442210273349)
          ·
            refine ⟨16047470315716207914426253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85586508350486442210273349 16047470315716207914426253)
            ·
              refine ⟨6017801368393577967909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16047470315716207914426253 6017801368393577967909845)
              ·
                refine ⟨141042219571724483622887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6017801368393577967909845 141042219571724483622887)
                ·
                  rfl

theorem cell22_3708163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 7].length) (baseStart_3708163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708163 prefixEnd_3708163 := by exact prefixLift 3708163
  have htrace : WordTrace (prefixWord ++ tailWord_3708163) baseStart_3708163 baseEnd_3708163 := by
    simpa [prefixWord, tailWord_3708163, baseEnd_3708163] using wordTrace_append hprefix tailTrace_3708163
  have hstable : (prefixWord ++ tailWord_3708163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708163).length < 2 ^ (prefixWord ++ tailWord_3708163).sum := by decide
  have hdescent : baseEnd_3708163 < baseStart_3708163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708208 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_3708208 : Nat := 118140960795 + 3708208 * 2 ^ 59
def prefixEnd_3708208 : Nat := 4983230072969 + 3 ^ 40 * 3708208 * 2
def baseEnd_3708208 : Nat := 423131793521718411743615

theorem tailTrace_3708208 : CollatzResearch.WordTrace tailWord_3708208 prefixEnd_3708208 423131793521718411743615 := by
  unfold tailWord_3708208
  simp only [CollatzResearch.WordTrace]
  refine ⟨67624728474901601175502639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90166304633202134900670185 67624728474901601175502639)
  ·
    refine ⟨101437092712352401763253959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67624728474901601175502639 101437092712352401763253959)
    ·
      refine ⟨152155639068528602644880939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101437092712352401763253959 152155639068528602644880939)
      ·
        refine ⟨228233458602792903967321409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152155639068528602644880939 228233458602792903967321409)
        ·
          refine ⟨171175093952094677975491057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228233458602792903967321409 171175093952094677975491057)
          ·
            refine ⟨128381320464071008481618293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171175093952094677975491057 128381320464071008481618293)
            ·
              refine ⟨12035748793506657045151715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128381320464071008481618293 12035748793506657045151715)
              ·
                refine ⟨18053623190259985567727573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12035748793506657045151715 18053623190259985567727573)
                ·
                  refine ⟨423131793521718411743615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18053623190259985567727573 423131793521718411743615)
                  ·
                    rfl

theorem cell22_3708208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_3708208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708208 prefixEnd_3708208 := by exact prefixLift 3708208
  have htrace : WordTrace (prefixWord ++ tailWord_3708208) baseStart_3708208 baseEnd_3708208 := by
    simpa [prefixWord, tailWord_3708208, baseEnd_3708208] using wordTrace_append hprefix tailTrace_3708208
  have hstable : (prefixWord ++ tailWord_3708208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708208).length < 2 ^ (prefixWord ++ tailWord_3708208).sum := by decide
  have hdescent : baseEnd_3708208 < baseStart_3708208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708285 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3708285 : Nat := 118140960795 + 3708285 * 2 ^ 59
def prefixEnd_3708285 : Nat := 4983230072969 + 3 ^ 40 * 3708285 * 2
def baseEnd_3708285 : Nat := 1269421739238752701055609

theorem tailTrace_3708285 : CollatzResearch.WordTrace tailWord_3708285 prefixEnd_3708285 1269421739238752701055609 := by
  unfold tailWord_3708285
  simp only [CollatzResearch.WordTrace]
  refine ⟨135252265370524244501558309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90168176913682829667705539 135252265370524244501558309)
  ·
    refine ⟨25359799756973295844042183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135252265370524244501558309 25359799756973295844042183)
    ·
      refine ⟨38039699635459943766063275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25359799756973295844042183 38039699635459943766063275)
      ·
        refine ⟨57059549453189915649094913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38039699635459943766063275 57059549453189915649094913)
        ·
          refine ⟨42794662089892436736821185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57059549453189915649094913 42794662089892436736821185)
          ·
            refine ⟨32095996567419327552615889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42794662089892436736821185 32095996567419327552615889)
            ·
              refine ⟨24071997425564495664461917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32095996567419327552615889 24071997425564495664461917)
              ·
                refine ⟨9026999034586685874173219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24071997425564495664461917 9026999034586685874173219)
                ·
                  refine ⟨13540498551880028811259829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026999034586685874173219 13540498551880028811259829)
                  ·
                    refine ⟨1269421739238752701055609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13540498551880028811259829 1269421739238752701055609)
                    ·
                      rfl

theorem cell22_3708285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3708285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708285 prefixEnd_3708285 := by exact prefixLift 3708285
  have htrace : WordTrace (prefixWord ++ tailWord_3708285) baseStart_3708285 baseEnd_3708285 := by
    simpa [prefixWord, tailWord_3708285, baseEnd_3708285] using wordTrace_append hprefix tailTrace_3708285
  have hstable : (prefixWord ++ tailWord_3708285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708285).length < 2 ^ (prefixWord ++ tailWord_3708285).sum := by decide
  have hdescent : baseEnd_3708285 < baseStart_3708285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708317 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3708317 : Nat := 118140960795 + 3708317 * 2 ^ 59
def prefixEnd_3708317 : Nat := 4983230072969 + 3 ^ 40 * 3708317 * 2
def baseEnd_3708317 : Nat := 1269432693492715284255511

theorem tailTrace_3708317 : CollatzResearch.WordTrace tailWord_3708317 prefixEnd_3708317 1269432693492715284255511 := by
  unfold tailWord_3708317
  simp only [CollatzResearch.WordTrace]
  refine ⟨135253432506408313966723205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90168955004272209311148803 135253432506408313966723205)
  ·
    refine ⟨25360018594951558868760601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135253432506408313966723205 25360018594951558868760601)
    ·
      refine ⟨19020013946213669151570451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25360018594951558868760601 19020013946213669151570451)
      ·
        refine ⟨28530020919320503727355677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19020013946213669151570451 28530020919320503727355677)
        ·
          refine ⟨10698757844745188897758379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28530020919320503727355677 10698757844745188897758379)
          ·
            refine ⟨16048136767117783346637569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10698757844745188897758379 16048136767117783346637569)
            ·
              refine ⟨12036102575338337509978177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16048136767117783346637569 12036102575338337509978177)
              ·
                refine ⟨9027076931503753132483633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12036102575338337509978177 9027076931503753132483633)
                ·
                  refine ⟨6770307698627814849362725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027076931503753132483633 6770307698627814849362725)
                  ·
                    refine ⟨1269432693492715284255511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6770307698627814849362725 1269432693492715284255511)
                    ·
                      rfl

theorem cell22_3708317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3708317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708317 prefixEnd_3708317 := by exact prefixLift 3708317
  have htrace : WordTrace (prefixWord ++ tailWord_3708317) baseStart_3708317 baseEnd_3708317 := by
    simpa [prefixWord, tailWord_3708317, baseEnd_3708317] using wordTrace_append hprefix tailTrace_3708317
  have hstable : (prefixWord ++ tailWord_3708317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708317).length < 2 ^ (prefixWord ++ tailWord_3708317).sum := by decide
  have hdescent : baseEnd_3708317 < baseStart_3708317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708319 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 2, 3]
def baseStart_3708319 : Nat := 118140960795 + 3708319 * 2 ^ 59
def prefixEnd_3708319 : Nat := 4983230072969 + 3 ^ 40 * 3708319 * 2
def baseEnd_3708319 : Nat := 1269433378133587945705505

theorem tailTrace_3708319 : CollatzResearch.WordTrace tailWord_3708319 prefixEnd_3708319 1269433378133587945705505 := by
  unfold tailWord_3708319
  simp only [CollatzResearch.WordTrace]
  refine ⟨135253505452401068308296011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90169003634934045538864007 135253505452401068308296011)
  ·
    refine ⟨202880258178601602462444017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135253505452401068308296011 202880258178601602462444017)
    ·
      refine ⟨152160193633951201846833013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202880258178601602462444017 152160193633951201846833013)
      ·
        refine ⟨14265018153182925173140595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152160193633951201846833013 14265018153182925173140595)
        ·
          refine ⟨21397527229774387759710893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14265018153182925173140595 21397527229774387759710893)
          ·
            refine ⟨8024072711165395409891585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21397527229774387759710893 8024072711165395409891585)
            ·
              refine ⟨6018054533374046557418689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8024072711165395409891585 6018054533374046557418689)
              ·
                refine ⟨4513540900030534918064017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6018054533374046557418689 4513540900030534918064017)
                ·
                  refine ⟨3385155675022901188548013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513540900030534918064017 3385155675022901188548013)
                  ·
                    refine ⟨1269433378133587945705505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385155675022901188548013 1269433378133587945705505)
                    ·
                      rfl

theorem cell22_3708319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_3708319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708319 prefixEnd_3708319 := by exact prefixLift 3708319
  have htrace : WordTrace (prefixWord ++ tailWord_3708319) baseStart_3708319 baseEnd_3708319 := by
    simpa [prefixWord, tailWord_3708319, baseEnd_3708319] using wordTrace_append hprefix tailTrace_3708319
  have hstable : (prefixWord ++ tailWord_3708319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708319).length < 2 ^ (prefixWord ++ tailWord_3708319).sum := by decide
  have hdescent : baseEnd_3708319 < baseStart_3708319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708360 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_3708360 : Nat := 118140960795 + 3708360 * 2 ^ 59
def prefixEnd_3708360 : Nat := 4983230072969 + 3 ^ 40 * 3708360 * 2
def baseEnd_3708360 : Nat := 423149137757159168476793

theorem tailTrace_3708360 : CollatzResearch.WordTrace tailWord_3708360 prefixEnd_3708360 423149137757159168476793 := by
  unfold tailWord_3708360
  simp only [CollatzResearch.WordTrace]
  refine ⟨67627500422626266155269267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90170000563501688207025689 67627500422626266155269267)
  ·
    refine ⟨101441250633939399232903901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67627500422626266155269267 101441250633939399232903901)
    ·
      refine ⟨38040468987727274712338963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101441250633939399232903901 38040468987727274712338963)
      ·
        refine ⟨57060703481590912068508445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38040468987727274712338963 57060703481590912068508445)
        ·
          refine ⟨21397763805596592025690667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57060703481590912068508445 21397763805596592025690667)
          ·
            refine ⟨32096645708394888038536001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21397763805596592025690667 32096645708394888038536001)
            ·
              refine ⟨24072484281296166028902001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32096645708394888038536001 24072484281296166028902001)
              ·
                refine ⟨18054363210972124521676501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24072484281296166028902001 18054363210972124521676501)
                ·
                  refine ⟨423149137757159168476793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18054363210972124521676501 423149137757159168476793)
                  ·
                    rfl

theorem cell22_3708360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_3708360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708360 prefixEnd_3708360 := by exact prefixLift 3708360
  have htrace : WordTrace (prefixWord ++ tailWord_3708360) baseStart_3708360 baseEnd_3708360 := by
    simpa [prefixWord, tailWord_3708360, baseEnd_3708360] using wordTrace_append hprefix tailTrace_3708360
  have hstable : (prefixWord ++ tailWord_3708360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708360).length < 2 ^ (prefixWord ++ tailWord_3708360).sum := by decide
  have hdescent : baseEnd_3708360 < baseStart_3708360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708377 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 5]
def baseStart_3708377 : Nat := 118140960795 + 3708377 * 2 ^ 59
def prefixEnd_3708377 : Nat := 4983230072969 + 3 ^ 40 * 3708377 * 2
def baseEnd_3708377 : Nat := 423151077572965042585109

theorem tailTrace_3708377 : CollatzResearch.WordTrace tailWord_3708377 prefixEnd_3708377 423151077572965042585109 := by
  unfold tailWord_3708377
  simp only [CollatzResearch.WordTrace]
  refine ⟨135255620886190944213907385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90170413924127296142604923 135255620886190944213907385)
  ·
    refine ⟨101441715664643208160430539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135255620886190944213907385 101441715664643208160430539)
    ·
      refine ⟨152162573496964812240645809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101441715664643208160430539 152162573496964812240645809)
      ·
        refine ⟨114121930122723609180484357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152162573496964812240645809 114121930122723609180484357)
        ·
          refine ⟨21397861898010676721340817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114121930122723609180484357 21397861898010676721340817)
          ·
            refine ⟨16048396423508007541005613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21397861898010676721340817 16048396423508007541005613)
            ·
              refine ⟨6018148658815502827877105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16048396423508007541005613 6018148658815502827877105)
              ·
                refine ⟨4513611494111627120907829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6018148658815502827877105 4513611494111627120907829)
                ·
                  refine ⟨423151077572965042585109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4513611494111627120907829 423151077572965042585109)
                  ·
                    rfl

theorem cell22_3708377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_3708377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708377 prefixEnd_3708377 := by exact prefixLift 3708377
  have htrace : WordTrace (prefixWord ++ tailWord_3708377) baseStart_3708377 baseEnd_3708377 := by
    simpa [prefixWord, tailWord_3708377, baseEnd_3708377] using wordTrace_append hprefix tailTrace_3708377
  have hstable : (prefixWord ++ tailWord_3708377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708377).length < 2 ^ (prefixWord ++ tailWord_3708377).sum := by decide
  have hdescent : baseEnd_3708377 < baseStart_3708377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708381 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3708381 : Nat := 118140960795 + 3708381 * 2 ^ 59
def prefixEnd_3708381 : Nat := 4983230072969 + 3 ^ 40 * 3708381 * 2
def baseEnd_3708381 : Nat := 1269454602000640450655315

theorem tailTrace_3708381 : CollatzResearch.WordTrace tailWord_3708381 prefixEnd_3708381 1269454602000640450655315 := by
  unfold tailWord_3708381
  simp only [CollatzResearch.WordTrace]
  refine ⟨135255766778176452897052997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90170511185450968598035331 135255766778176452897052997)
  ·
    refine ⟨25360456270908084918197437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135255766778176452897052997 25360456270908084918197437)
    ·
      refine ⟨9510171101590531844324039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25360456270908084918197437 9510171101590531844324039)
      ·
        refine ⟨14265256652385797766486059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9510171101590531844324039 14265256652385797766486059)
        ·
          refine ⟨21397884978578696649729089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14265256652385797766486059 21397884978578696649729089)
          ·
            refine ⟨16048413733934022487296817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21397884978578696649729089 16048413733934022487296817)
            ·
              refine ⟨12036310300450516865472613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16048413733934022487296817 12036310300450516865472613)
              ·
                refine ⟨2256808181334471912276115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12036310300450516865472613 2256808181334471912276115)
                ·
                  refine ⟨3385212272001707868414173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256808181334471912276115 3385212272001707868414173)
                  ·
                    refine ⟨1269454602000640450655315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385212272001707868414173 1269454602000640450655315)
                    ·
                      rfl

theorem cell22_3708381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3708381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708381 prefixEnd_3708381 := by exact prefixLift 3708381
  have htrace : WordTrace (prefixWord ++ tailWord_3708381) baseStart_3708381 baseEnd_3708381 := by
    simpa [prefixWord, tailWord_3708381, baseEnd_3708381] using wordTrace_append hprefix tailTrace_3708381
  have hstable : (prefixWord ++ tailWord_3708381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708381).length < 2 ^ (prefixWord ++ tailWord_3708381).sum := by decide
  have hdescent : baseEnd_3708381 < baseStart_3708381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708469 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3708469 : Nat := 118140960795 + 3708469 * 2 ^ 59
def prefixEnd_3708469 : Nat := 4983230072969 + 3 ^ 40 * 3708469 * 2
def baseEnd_3708469 : Nat := 1269484726199037554455045

theorem tailTrace_3708469 : CollatzResearch.WordTrace tailWord_3708469 prefixEnd_3708469 1269484726199037554455045 := by
  unfold tailWord_3708469
  simp only [CollatzResearch.WordTrace]
  refine ⟨135258976401857643926256461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90172650934571762617504307 135258976401857643926256461)
  ·
    refine ⟨50722116150696616472346173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135258976401857643926256461 50722116150696616472346173)
    ·
      refine ⟨19020793556511231177129815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50722116150696616472346173 19020793556511231177129815)
      ·
        refine ⟨28531190334766846765694723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19020793556511231177129815 28531190334766846765694723)
        ·
          refine ⟨42796785502150270148542085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28531190334766846765694723 42796785502150270148542085)
          ·
            refine ⟨8024397281653175652851641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42796785502150270148542085 8024397281653175652851641)
            ·
              refine ⟨6018297961239881739638731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8024397281653175652851641 6018297961239881739638731)
              ·
                refine ⟨9027446941859822609458097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018297961239881739638731 9027446941859822609458097)
                ·
                  refine ⟨6770585206394866957093573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027446941859822609458097 6770585206394866957093573)
                  ·
                    refine ⟨1269484726199037554455045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6770585206394866957093573 1269484726199037554455045)
                    ·
                      rfl

theorem cell22_3708469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3708469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708469 prefixEnd_3708469 := by exact prefixLift 3708469
  have htrace : WordTrace (prefixWord ++ tailWord_3708469) baseStart_3708469 baseEnd_3708469 := by
    simpa [prefixWord, tailWord_3708469, baseEnd_3708469] using wordTrace_append hprefix tailTrace_3708469
  have hstable : (prefixWord ++ tailWord_3708469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708469).length < 2 ^ (prefixWord ++ tailWord_3708469).sum := by decide
  have hdescent : baseEnd_3708469 < baseStart_3708469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708533 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3708533 : Nat := 118140960795 + 3708533 * 2 ^ 59
def prefixEnd_3708533 : Nat := 4983230072969 + 3 ^ 40 * 3708533 * 2
def baseEnd_3708533 : Nat := 1269506634706962720854849

theorem tailTrace_3708533 : CollatzResearch.WordTrace tailWord_3708533 prefixEnd_3708533 1269506634706962720854849 := by
  unfold tailWord_3708533
  simp only [CollatzResearch.WordTrace]
  refine ⟨135261310673625782856586253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90174207115750521904390835 135261310673625782856586253)
  ·
    refine ⟨50722991502609668571219845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135261310673625782856586253 50722991502609668571219845)
    ·
      refine ⟨9510560906739312857103721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50722991502609668571219845 9510560906739312857103721)
      ·
        refine ⟨7132920680054484642827791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9510560906739312857103721 7132920680054484642827791)
        ·
          refine ⟨10699381020081726964241687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7132920680054484642827791 10699381020081726964241687)
          ·
            refine ⟨16049071530122590446362531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10699381020081726964241687 16049071530122590446362531)
            ·
              refine ⟨24073607295183885669543797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16049071530122590446362531 24073607295183885669543797)
              ·
                refine ⟨2256900683923489281519731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24073607295183885669543797 2256900683923489281519731)
                ·
                  refine ⟨3385351025885233922279597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256900683923489281519731 3385351025885233922279597)
                  ·
                    refine ⟨1269506634706962720854849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385351025885233922279597 1269506634706962720854849)
                    ·
                      rfl

theorem cell22_3708533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3708533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708533 prefixEnd_3708533 := by exact prefixLift 3708533
  have htrace : WordTrace (prefixWord ++ tailWord_3708533) baseStart_3708533 baseEnd_3708533 := by
    simpa [prefixWord, tailWord_3708533, baseEnd_3708533] using wordTrace_append hprefix tailTrace_3708533
  have hstable : (prefixWord ++ tailWord_3708533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708533).length < 2 ^ (prefixWord ++ tailWord_3708533).sum := by decide
  have hdescent : baseEnd_3708533 < baseStart_3708533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708576 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_3708576 : Nat := 118140960795 + 3708576 * 2 ^ 59
def prefixEnd_3708576 : Nat := 4983230072969 + 3 ^ 40 * 3708576 * 2
def baseEnd_3708576 : Nat := 1269521354485724942029717

theorem tailTrace_3708576 : CollatzResearch.WordTrace tailWord_3708576 prefixEnd_3708576 1269521354485724942029717 := by
  unfold tailWord_3708576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631439506235000600200791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90175252674980000800267721 67631439506235000600200791)
  ·
    refine ⟨101447159259352500900301187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67631439506235000600200791 101447159259352500900301187)
    ·
      refine ⟨152170738889028751350451781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101447159259352500900301187 152170738889028751350451781)
      ·
        refine ⟨28532013541692890878209709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152170738889028751350451781 28532013541692890878209709)
        ·
          refine ⟨10699505078134834079328641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28532013541692890878209709 10699505078134834079328641)
          ·
            refine ⟨8024628808601125559496481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10699505078134834079328641 8024628808601125559496481)
            ·
              refine ⟨6018471606450844169622361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8024628808601125559496481 6018471606450844169622361)
              ·
                refine ⟨4513853704838133127216771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6018471606450844169622361 4513853704838133127216771)
                ·
                  refine ⟨6770780557257199690825157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513853704838133127216771 6770780557257199690825157)
                  ·
                    refine ⟨1269521354485724942029717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6770780557257199690825157 1269521354485724942029717)
                    ·
                      rfl

theorem cell22_3708576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_3708576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708576 prefixEnd_3708576 := by exact prefixLift 3708576
  have htrace : WordTrace (prefixWord ++ tailWord_3708576) baseStart_3708576 baseEnd_3708576 := by
    simpa [prefixWord, tailWord_3708576, baseEnd_3708576] using wordTrace_append hprefix tailTrace_3708576
  have hstable : (prefixWord ++ tailWord_3708576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708576).length < 2 ^ (prefixWord ++ tailWord_3708576).sum := by decide
  have hdescent : baseEnd_3708576 < baseStart_3708576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708584 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3708584 : Nat := 118140960795 + 3708584 * 2 ^ 59
def prefixEnd_3708584 : Nat := 4983230072969 + 3 ^ 40 * 3708584 * 2
def baseEnd_3708584 : Nat := 1269524093049215587829693

theorem tailTrace_3708584 : CollatzResearch.WordTrace tailWord_3708584 prefixEnd_3708584 1269524093049215587829693 := by
  unfold tailWord_3708584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631585398220509283346403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90175447197627345711128537 67631585398220509283346403)
  ·
    refine ⟨101447378097330763925019605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67631585398220509283346403 101447378097330763925019605)
    ·
      refine ⟨2377672924156189779492647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101447378097330763925019605 2377672924156189779492647)
      ·
        refine ⟨3566509386234284669238971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377672924156189779492647 3566509386234284669238971)
        ·
          refine ⟨5349764079351427003858457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566509386234284669238971 5349764079351427003858457)
          ·
            refine ⟨4012323059513570252893843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5349764079351427003858457 4012323059513570252893843)
            ·
              refine ⟨6018484589270355379340765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012323059513570252893843 6018484589270355379340765)
              ·
                refine ⟨2256931720976383267252787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6018484589270355379340765 2256931720976383267252787)
                ·
                  refine ⟨3385397581464574900879181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256931720976383267252787 3385397581464574900879181)
                  ·
                    refine ⟨1269524093049215587829693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385397581464574900879181 1269524093049215587829693)
                    ·
                      rfl

theorem cell22_3708584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3708584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708584 prefixEnd_3708584 := by exact prefixLift 3708584
  have htrace : WordTrace (prefixWord ++ tailWord_3708584) baseStart_3708584 baseEnd_3708584 := by
    simpa [prefixWord, tailWord_3708584, baseEnd_3708584] using wordTrace_append hprefix tailTrace_3708584
  have hstable : (prefixWord ++ tailWord_3708584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708584).length < 2 ^ (prefixWord ++ tailWord_3708584).sum := by decide
  have hdescent : baseEnd_3708584 < baseStart_3708584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708589 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3708589 : Nat := 118140960795 + 3708589 * 2 ^ 59
def prefixEnd_3708589 : Nat := 4983230072969 + 3 ^ 40 * 3708589 * 2
def baseEnd_3708589 : Nat := 1269525804651397241454677

theorem tailTrace_3708589 : CollatzResearch.WordTrace tailWord_3708589 prefixEnd_3708589 1269525804651397241454677 := by
  unfold tailWord_3708589
  simp only [CollatzResearch.WordTrace]
  refine ⟨135263353161422904420624821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90175568774281936280416547 135263353161422904420624821)
  ·
    refine ⟨12680939358883397289433577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135263353161422904420624821 12680939358883397289433577)
    ·
      refine ⟨9510704519162547967075183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12680939358883397289433577 9510704519162547967075183)
      ·
        refine ⟨14266056778743821950612775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9510704519162547967075183 14266056778743821950612775)
        ·
          refine ⟨21399085168115732925919163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14266056778743821950612775 21399085168115732925919163)
          ·
            refine ⟨32098627752173599388878745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21399085168115732925919163 32098627752173599388878745)
            ·
              refine ⟨24073970814130199541659059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32098627752173599388878745 24073970814130199541659059)
              ·
                refine ⟨36110956221195299312488589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24073970814130199541659059 36110956221195299312488589)
                ·
                  refine ⟨13541608582948237242183221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36110956221195299312488589 13541608582948237242183221)
                  ·
                    refine ⟨1269525804651397241454677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13541608582948237242183221 1269525804651397241454677)
                    ·
                      rfl

theorem cell22_3708589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3708589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708589 prefixEnd_3708589 := by exact prefixLift 3708589
  have htrace : WordTrace (prefixWord ++ tailWord_3708589) baseStart_3708589 baseEnd_3708589 := by
    simpa [prefixWord, tailWord_3708589, baseEnd_3708589] using wordTrace_append hprefix tailTrace_3708589
  have hstable : (prefixWord ++ tailWord_3708589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708589).length < 2 ^ (prefixWord ++ tailWord_3708589).sum := by decide
  have hdescent : baseEnd_3708589 < baseStart_3708589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708602 : List Nat := [3, 1, 1, 1, 2, 4, 10]
def baseStart_3708602 : Nat := 118140960795 + 3708602 * 2 ^ 59
def prefixEnd_3708602 : Nat := 4983230072969 + 3 ^ 40 * 3708602 * 2
def baseEnd_3708602 : Nat := 47019639067298871884431

theorem tailTrace_3708602 : CollatzResearch.WordTrace tailWord_3708602 prefixEnd_3708602 47019639067298871884431 := by
  unfold tailWord_3708602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815956827593951910212015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90175884873583871760565373 33815956827593951910212015)
  ·
    refine ⟨50723935241390927865318023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33815956827593951910212015 50723935241390927865318023)
    ·
      refine ⟨76085902862086391797977035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50723935241390927865318023 76085902862086391797977035)
      ·
        refine ⟨114128854293129587696965553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76085902862086391797977035 114128854293129587696965553)
        ·
          refine ⟨85596640719847190772724165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114128854293129587696965553 85596640719847190772724165)
          ·
            refine ⟨16049370134971348269885781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85596640719847190772724165 16049370134971348269885781)
            ·
              refine ⟨47019639067298871884431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16049370134971348269885781 47019639067298871884431)
              ·
                rfl

theorem cell22_3708602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 10].length) (baseStart_3708602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708602 prefixEnd_3708602 := by exact prefixLift 3708602
  have htrace : WordTrace (prefixWord ++ tailWord_3708602) baseStart_3708602 baseEnd_3708602 := by
    simpa [prefixWord, tailWord_3708602, baseEnd_3708602] using wordTrace_append hprefix tailTrace_3708602
  have hstable : (prefixWord ++ tailWord_3708602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708602).length < 2 ^ (prefixWord ++ tailWord_3708602).sum := by decide
  have hdescent : baseEnd_3708602 < baseStart_3708602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708604 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_3708604 : Nat := 118140960795 + 3708604 * 2 ^ 59
def prefixEnd_3708604 : Nat := 4983230072969 + 3 ^ 40 * 3708604 * 2
def baseEnd_3708604 : Nat := 1269530939457942202329631

theorem tailTrace_3708604 : CollatzResearch.WordTrace tailWord_3708604 prefixEnd_3708604 1269530939457942202329631 := by
  unfold tailWord_3708604
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631950128184280991210433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90175933504245707988280577 67631950128184280991210433)
  ·
    refine ⟨50723962596138210743407825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67631950128184280991210433 50723962596138210743407825)
    ·
      refine ⟨38042971947103658057555869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50723962596138210743407825 38042971947103658057555869)
      ·
        refine ⟨14266114480163871771583451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38042971947103658057555869 14266114480163871771583451)
        ·
          refine ⟨21399171720245807657375177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14266114480163871771583451 21399171720245807657375177)
          ·
            refine ⟨16049378790184355743031383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21399171720245807657375177 16049378790184355743031383)
            ·
              refine ⟨24074068185276533614547075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16049378790184355743031383 24074068185276533614547075)
              ·
                refine ⟨36111102277914800421820613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24074068185276533614547075 36111102277914800421820613)
                ·
                  refine ⟨6770831677109025079091365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36111102277914800421820613 6770831677109025079091365)
                  ·
                    refine ⟨1269530939457942202329631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6770831677109025079091365 1269530939457942202329631)
                    ·
                      rfl

theorem cell22_3708604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_3708604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708604 prefixEnd_3708604 := by exact prefixLift 3708604
  have htrace : WordTrace (prefixWord ++ tailWord_3708604) baseStart_3708604 baseEnd_3708604 := by
    simpa [prefixWord, tailWord_3708604, baseEnd_3708604] using wordTrace_append hprefix tailTrace_3708604
  have hstable : (prefixWord ++ tailWord_3708604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708604).length < 2 ^ (prefixWord ++ tailWord_3708604).sum := by decide
  have hdescent : baseEnd_3708604 < baseStart_3708604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708606 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3708606 : Nat := 118140960795 + 3708606 * 2 ^ 59
def prefixEnd_3708606 : Nat := 4983230072969 + 3 ^ 40 * 3708606 * 2
def baseEnd_3708606 : Nat := 1269531624098814863779625

theorem tailTrace_3708606 : CollatzResearch.WordTrace tailWord_3708606 prefixEnd_3708606 1269531624098814863779625 := by
  unfold tailWord_3708606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16907996650295164540499209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90175982134907544215995781 16907996650295164540499209)
  ·
    refine ⟨12680997487721373405374407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16907996650295164540499209 12680997487721373405374407)
    ·
      refine ⟨19021496231582060108061611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12680997487721373405374407 19021496231582060108061611)
      ·
        refine ⟨28532244347373090162092417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19021496231582060108061611 28532244347373090162092417)
        ·
          refine ⟨21399183260529817621569313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28532244347373090162092417 21399183260529817621569313)
          ·
            refine ⟨16049387445397363216176985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21399183260529817621569313 16049387445397363216176985)
            ·
              refine ⟨12037040584048022412132739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16049387445397363216176985 12037040584048022412132739)
              ·
                refine ⟨18055560876072033618199109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12037040584048022412132739 18055560876072033618199109)
                ·
                  refine ⟨3385417664263506303412333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18055560876072033618199109 3385417664263506303412333)
                  ·
                    refine ⟨1269531624098814863779625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385417664263506303412333 1269531624098814863779625)
                    ·
                      rfl

theorem cell22_3708606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3708606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708606 prefixEnd_3708606 := by exact prefixLift 3708606
  have htrace : WordTrace (prefixWord ++ tailWord_3708606) baseStart_3708606 baseEnd_3708606 := by
    simpa [prefixWord, tailWord_3708606, baseEnd_3708606] using wordTrace_append hprefix tailTrace_3708606
  have hstable : (prefixWord ++ tailWord_3708606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708606).length < 2 ^ (prefixWord ++ tailWord_3708606).sum := by decide
  have hdescent : baseEnd_3708606 < baseStart_3708606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708668 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_3708668 : Nat := 118140960795 + 3708668 * 2 ^ 59
def prefixEnd_3708668 : Nat := 4983230072969 + 3 ^ 40 * 3708668 * 2
def baseEnd_3708668 : Nat := 1269552847965867368729435

theorem tailTrace_3708668 : CollatzResearch.WordTrace tailWord_3708668 prefixEnd_3708668 1269552847965867368729435 := by
  unfold tailWord_3708668
  simp only [CollatzResearch.WordTrace]
  refine ⟨67633117264068350456375329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90177489685424467275167105 67633117264068350456375329)
  ·
    refine ⟨50724837948051262842281497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67633117264068350456375329 50724837948051262842281497)
    ·
      refine ⟨38043628461038447131711123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50724837948051262842281497 38043628461038447131711123)
      ·
        refine ⟨57065442691557670697566685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38043628461038447131711123 57065442691557670697566685)
        ·
          refine ⟨21399541009334126511587507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57065442691557670697566685 21399541009334126511587507)
          ·
            refine ⟨32099311514001189767381261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21399541009334126511587507 32099311514001189767381261)
            ·
              refine ⟨12037241817750446162767973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32099311514001189767381261 12037241817750446162767973)
              ·
                refine ⟨2256982840828208655518995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12037241817750446162767973 2256982840828208655518995)
                ·
                  refine ⟨3385474261242312983278493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256982840828208655518995 3385474261242312983278493)
                  ·
                    refine ⟨1269552847965867368729435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385474261242312983278493 1269552847965867368729435)
                    ·
                      rfl

theorem cell22_3708668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_3708668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708668 prefixEnd_3708668 := by exact prefixLift 3708668
  have htrace : WordTrace (prefixWord ++ tailWord_3708668) baseStart_3708668 baseEnd_3708668 := by
    simpa [prefixWord, tailWord_3708668, baseEnd_3708668] using wordTrace_append hprefix tailTrace_3708668
  have hstable : (prefixWord ++ tailWord_3708668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708668).length < 2 ^ (prefixWord ++ tailWord_3708668).sum := by decide
  have hdescent : baseEnd_3708668 < baseStart_3708668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708739 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_3708739 : Nat := 118140960795 + 3708739 * 2 ^ 59
def prefixEnd_3708739 : Nat := 4983230072969 + 3 ^ 40 * 3708739 * 2
def baseEnd_3708739 : Nat := 1269577152716846850204217

theorem tailTrace_3708739 : CollatzResearch.WordTrace tailWord_3708739 prefixEnd_3708739 1269577152716846850204217 := by
  unfold tailWord_3708739
  simp only [CollatzResearch.WordTrace]
  refine ⟨135268824110879480038585271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90179216073919653359056847 135268824110879480038585271)
  ·
    refine ⟨202903236166319220057877907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135268824110879480038585271 202903236166319220057877907)
    ·
      refine ⟨304354854249478830086816861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202903236166319220057877907 304354854249478830086816861)
      ·
        refine ⟨114133070343554561282556323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304354854249478830086816861 114133070343554561282556323)
        ·
          refine ⟨171199605515331841923834485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114133070343554561282556323 171199605515331841923834485)
          ·
            refine ⟨16049963017062360180359483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171199605515331841923834485 16049963017062360180359483)
            ·
              refine ⟨24074944525593540270539225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16049963017062360180359483 24074944525593540270539225)
              ·
                refine ⟨18056208394195155202904419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24074944525593540270539225 18056208394195155202904419)
                ·
                  refine ⟨27084312591292732804356629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18056208394195155202904419 27084312591292732804356629)
                  ·
                    refine ⟨1269577152716846850204217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27084312591292732804356629 1269577152716846850204217)
                    ·
                      rfl

theorem cell22_3708739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_3708739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708739 prefixEnd_3708739 := by exact prefixLift 3708739
  have htrace : WordTrace (prefixWord ++ tailWord_3708739) baseStart_3708739 baseEnd_3708739 := by
    simpa [prefixWord, tailWord_3708739, baseEnd_3708739] using wordTrace_append hprefix tailTrace_3708739
  have hstable : (prefixWord ++ tailWord_3708739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708739).length < 2 ^ (prefixWord ++ tailWord_3708739).sum := by decide
  have hdescent : baseEnd_3708739 < baseStart_3708739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708756 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3708756 : Nat := 118140960795 + 3708756 * 2 ^ 59
def prefixEnd_3708756 : Nat := 4983230072969 + 3 ^ 40 * 3708756 * 2
def baseEnd_3708756 : Nat := 1269582972164264472529165

theorem tailTrace_3708756 : CollatzResearch.WordTrace tailWord_3708756 prefixEnd_3708756 1269582972164264472529165 := by
  unfold tailWord_3708756
  simp only [CollatzResearch.WordTrace]
  refine ⟨67634722075908945970977061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90179629434545261294636081 67634722075908945970977061)
  ·
    refine ⟨12681510389232927369558199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67634722075908945970977061 12681510389232927369558199)
    ·
      refine ⟨19022265583849391054337299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681510389232927369558199 19022265583849391054337299)
      ·
        refine ⟨28533398375774086581505949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19022265583849391054337299 28533398375774086581505949)
        ·
          refine ⟨10700024390915282468064731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28533398375774086581505949 10700024390915282468064731)
          ·
            refine ⟨16050036586372923702097097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10700024390915282468064731 16050036586372923702097097)
            ·
              refine ⟨12037527439779692776572823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16050036586372923702097097 12037527439779692776572823)
              ·
                refine ⟨18056291159669539164859235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12037527439779692776572823 18056291159669539164859235)
                ·
                  refine ⟨27084436739504308747288853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18056291159669539164859235 27084436739504308747288853)
                  ·
                    refine ⟨1269582972164264472529165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27084436739504308747288853 1269582972164264472529165)
                    ·
                      rfl

theorem cell22_3708756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3708756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708756 prefixEnd_3708756 := by exact prefixLift 3708756
  have htrace : WordTrace (prefixWord ++ tailWord_3708756) baseStart_3708756 baseEnd_3708756 := by
    simpa [prefixWord, tailWord_3708756, baseEnd_3708756] using wordTrace_append hprefix tailTrace_3708756
  have hstable : (prefixWord ++ tailWord_3708756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708756).length < 2 ^ (prefixWord ++ tailWord_3708756).sum := by decide
  have hdescent : baseEnd_3708756 < baseStart_3708756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708771 : List Nat := [1, 1, 1, 5, 4, 2, 8]
def baseStart_3708771 : Nat := 118140960795 + 3708771 * 2 ^ 59
def prefixEnd_3708771 : Nat := 4983230072969 + 3 ^ 40 * 3708771 * 2
def baseEnd_3708771 : Nat := 47021781739659608644597

theorem tailTrace_3708771 : CollatzResearch.WordTrace tailWord_3708771 prefixEnd_3708771 47021781739659608644597 := by
  unfold tailWord_3708771
  simp only [CollatzResearch.WordTrace]
  refine ⟨135269991246763549503750167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90179994164509033002500111 135269991246763549503750167)
  ·
    refine ⟨202904986870145324255625251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135269991246763549503750167 202904986870145324255625251)
    ·
      refine ⟨304357480305217986383437877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202904986870145324255625251 304357480305217986383437877)
      ·
        refine ⟨28533513778614186223447301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304357480305217986383437877 28533513778614186223447301)
        ·
          refine ⟨5350033833490159916896369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28533513778614186223447301 5350033833490159916896369)
          ·
            refine ⟨4012525375117619937672277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350033833490159916896369 4012525375117619937672277)
            ·
              refine ⟨47021781739659608644597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4012525375117619937672277 47021781739659608644597)
              ·
                rfl

theorem cell22_3708771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 8].length) (baseStart_3708771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708771 prefixEnd_3708771 := by exact prefixLift 3708771
  have htrace : WordTrace (prefixWord ++ tailWord_3708771) baseStart_3708771 baseEnd_3708771 := by
    simpa [prefixWord, tailWord_3708771, baseEnd_3708771] using wordTrace_append hprefix tailTrace_3708771
  have hstable : (prefixWord ++ tailWord_3708771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708771).length < 2 ^ (prefixWord ++ tailWord_3708771).sum := by decide
  have hdescent : baseEnd_3708771 < baseStart_3708771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708784 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_3708784 : Nat := 118140960795 + 3708784 * 2 ^ 59
def prefixEnd_3708784 : Nat := 4983230072969 + 3 ^ 40 * 3708784 * 2
def baseEnd_3708784 : Nat := 1269592557136481732829079

theorem tailTrace_3708784 : CollatzResearch.WordTrace tailWord_3708784 prefixEnd_3708784 1269592557136481732829079 := by
  unfold tailWord_3708784
  simp only [CollatzResearch.WordTrace]
  refine ⟨67635232697858226361986703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90180310263810968482648937 67635232697858226361986703)
  ·
    refine ⟨101452849046787339542980055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67635232697858226361986703 101452849046787339542980055)
    ·
      refine ⟨152179273570181009314470083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101452849046787339542980055 152179273570181009314470083)
      ·
        refine ⟨228268910355271513971705125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152179273570181009314470083 228268910355271513971705125)
        ·
          refine ⟨42800420691613408869694711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228268910355271513971705125 42800420691613408869694711)
          ·
            refine ⟨64200631037420113304542067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42800420691613408869694711 64200631037420113304542067)
            ·
              refine ⟨96300946556130169956813101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64200631037420113304542067 96300946556130169956813101)
              ·
                refine ⟨36112854958548813733804913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96300946556130169956813101 36112854958548813733804913)
                ·
                  refine ⟨27084641218911610300353685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36112854958548813733804913 27084641218911610300353685)
                  ·
                    refine ⟨1269592557136481732829079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27084641218911610300353685 1269592557136481732829079)
                    ·
                      rfl

theorem cell22_3708784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_3708784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708784 prefixEnd_3708784 := by exact prefixLift 3708784
  have htrace : WordTrace (prefixWord ++ tailWord_3708784) baseStart_3708784 baseEnd_3708784 := by
    simpa [prefixWord, tailWord_3708784, baseEnd_3708784] using wordTrace_append hprefix tailTrace_3708784
  have hstable : (prefixWord ++ tailWord_3708784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708784).length < 2 ^ (prefixWord ++ tailWord_3708784).sum := by decide
  have hdescent : baseEnd_3708784 < baseStart_3708784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708861 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3708861 : Nat := 118140960795 + 3708861 * 2 ^ 59
def prefixEnd_3708861 : Nat := 4983230072969 + 3 ^ 40 * 3708861 * 2
def baseEnd_3708861 : Nat := 423206305270026399551281

theorem tailTrace_3708861 : CollatzResearch.WordTrace tailWord_3708861 prefixEnd_3708861 423206305270026399551281 := by
  unfold tailWord_3708861
  simp only [CollatzResearch.WordTrace]
  refine ⟨135273273816437494874526437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90182182544291663249684291 135273273816437494874526437)
  ·
    refine ⟨25363738840582030288973707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135273273816437494874526437 25363738840582030288973707)
    ·
      refine ⟨38045608260873045433460561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25363738840582030288973707 38045608260873045433460561)
      ·
        refine ⟨28534206195654784075095421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38045608260873045433460561 28534206195654784075095421)
        ·
          refine ⟨10700327323370544028160783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28534206195654784075095421 10700327323370544028160783)
          ·
            refine ⟨16050490985055816042241175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10700327323370544028160783 16050490985055816042241175)
            ·
              refine ⟨24075736477583724063361763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16050490985055816042241175 24075736477583724063361763)
              ·
                refine ⟨36113604716375586095042645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24075736477583724063361763 36113604716375586095042645)
                ·
                  refine ⟨423206305270026399551281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36113604716375586095042645 423206305270026399551281)
                  ·
                    rfl

theorem cell22_3708861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3708861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708861 prefixEnd_3708861 := by exact prefixLift 3708861
  have htrace : WordTrace (prefixWord ++ tailWord_3708861) baseStart_3708861 baseEnd_3708861 := by
    simpa [prefixWord, tailWord_3708861, baseEnd_3708861] using wordTrace_append hprefix tailTrace_3708861
  have hstable : (prefixWord ++ tailWord_3708861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708861).length < 2 ^ (prefixWord ++ tailWord_3708861).sum := by decide
  have hdescent : baseEnd_3708861 < baseStart_3708861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708906 : List Nat := [3, 1, 3, 1, 2, 1, 2, 9]
def baseStart_3708906 : Nat := 118140960795 + 3708906 * 2 ^ 59
def prefixEnd_3708906 : Nat := 4983230072969 + 3 ^ 40 * 3708906 * 2
def baseEnd_3708906 : Nat := 141070480025523786808745

theorem tailTrace_3708906 : CollatzResearch.WordTrace tailWord_3708906 prefixEnd_3708906 141070480025523786808745 := by
  unfold tailWord_3708906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33818728775318616889978643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90183276734182978373276381 33818728775318616889978643)
  ·
    refine ⟨50728093162977925334967965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33818728775318616889978643 50728093162977925334967965)
    ·
      refine ⟨19023034936116722000612987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50728093162977925334967965 19023034936116722000612987)
      ·
        refine ⟨28534552404175083000919481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19023034936116722000612987 28534552404175083000919481)
        ·
          refine ⟨21400914303131312250689611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28534552404175083000919481 21400914303131312250689611)
          ·
            refine ⟨32101371454696968376034417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21400914303131312250689611 32101371454696968376034417)
            ·
              refine ⟨24076028591022726282025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32101371454696968376034417 24076028591022726282025813)
              ·
                refine ⟨141070480025523786808745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24076028591022726282025813 141070480025523786808745)
                ·
                  rfl

theorem cell22_3708906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_3708906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708906 prefixEnd_3708906 := by exact prefixLift 3708906
  have htrace : WordTrace (prefixWord ++ tailWord_3708906) baseStart_3708906 baseEnd_3708906 := by
    simpa [prefixWord, tailWord_3708906, baseEnd_3708906] using wordTrace_append hprefix tailTrace_3708906
  have hstable : (prefixWord ++ tailWord_3708906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708906).length < 2 ^ (prefixWord ++ tailWord_3708906).sum := by decide
  have hdescent : baseEnd_3708906 < baseStart_3708906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3708910 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3708910 : Nat := 118140960795 + 3708910 * 2 ^ 59
def prefixEnd_3708910 : Nat := 4983230072969 + 3 ^ 40 * 3708910 * 2
def baseEnd_3708910 : Nat := 1269635689511459404178693

theorem tailTrace_3708910 : CollatzResearch.WordTrace tailWord_3708910 prefixEnd_3708910 1269635689511459404178693 := by
  unfold tailWord_3708910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909382624157497030382523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90183373995506650828706789 16909382624157497030382523)
  ·
    refine ⟨25364073936236245545573785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16909382624157497030382523 25364073936236245545573785)
    ·
      refine ⟨19023055452177184159180339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25364073936236245545573785 19023055452177184159180339)
      ·
        refine ⟨28534583178265776238770509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19023055452177184159180339 28534583178265776238770509)
        ·
          refine ⟨10700468691849666089538941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28534583178265776238770509 10700468691849666089538941)
          ·
            refine ⟨4012675759443624783577103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10700468691849666089538941 4012675759443624783577103)
            ·
              refine ⟨6019013639165437175365655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012675759443624783577103 6019013639165437175365655)
              ·
                refine ⟨9028520458748155763048483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019013639165437175365655 9028520458748155763048483)
                ·
                  refine ⟨13542780688122233644572725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9028520458748155763048483 13542780688122233644572725)
                  ·
                    refine ⟨1269635689511459404178693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13542780688122233644572725 1269635689511459404178693)
                    ·
                      rfl

theorem cell22_3708910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3708910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3708910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3708910 prefixEnd_3708910 := by exact prefixLift 3708910
  have htrace : WordTrace (prefixWord ++ tailWord_3708910) baseStart_3708910 baseEnd_3708910 := by
    simpa [prefixWord, tailWord_3708910, baseEnd_3708910] using wordTrace_append hprefix tailTrace_3708910
  have hstable : (prefixWord ++ tailWord_3708910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3708910).length < 2 ^ (prefixWord ++ tailWord_3708910).sum := by decide
  have hdescent : baseEnd_3708910 < baseStart_3708910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3708910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709028 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3709028 : Nat := 118140960795 + 3709028 * 2 ^ 59
def prefixEnd_3709028 : Nat := 4983230072969 + 3 ^ 40 * 3709028 * 2
def baseEnd_3709028 : Nat := 1269676083322946429728331

theorem tailTrace_3709028 : CollatzResearch.WordTrace tailWord_3709028 prefixEnd_3709028 1269676083322946429728331 := by
  unfold tailWord_3709028
  simp only [CollatzResearch.WordTrace]
  refine ⟨67639682403416241197927869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90186243204554988263903825 67639682403416241197927869)
  ·
    refine ⟨25364880901281090449222951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67639682403416241197927869 25364880901281090449222951)
    ·
      refine ⟨38047321351921635673834427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25364880901281090449222951 38047321351921635673834427)
      ·
        refine ⟨57070982027882453510751641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38047321351921635673834427 57070982027882453510751641)
        ·
          refine ⟨42803236520911840133063731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57070982027882453510751641 42803236520911840133063731)
          ·
            refine ⟨64204854781367760199595597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42803236520911840133063731 64204854781367760199595597)
            ·
              refine ⟨24076820543012910074848349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64204854781367760199595597 24076820543012910074848349)
              ·
                refine ⟨9028807703629841278068131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24076820543012910074848349 9028807703629841278068131)
                ·
                  refine ⟨13543211555444761917102197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9028807703629841278068131 13543211555444761917102197)
                  ·
                    refine ⟨1269676083322946429728331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13543211555444761917102197 1269676083322946429728331)
                    ·
                      rfl

theorem cell22_3709028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3709028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709028 prefixEnd_3709028 := by exact prefixLift 3709028
  have htrace : WordTrace (prefixWord ++ tailWord_3709028) baseStart_3709028 baseEnd_3709028 := by
    simpa [prefixWord, tailWord_3709028, baseEnd_3709028] using wordTrace_append hprefix tailTrace_3709028
  have hstable : (prefixWord ++ tailWord_3709028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709028).length < 2 ^ (prefixWord ++ tailWord_3709028).sum := by decide
  have hdescent : baseEnd_3709028 < baseStart_3709028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3709079 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 2, 3]
def baseStart_3709079 : Nat := 118140960795 + 3709079 * 2 ^ 59
def prefixEnd_3709079 : Nat := 4983230072969 + 3 ^ 40 * 3709079 * 2
def baseEnd_3709079 : Nat := 1269693541665199296703175

theorem tailTrace_3709079 : CollatzResearch.WordTrace tailWord_3709079 prefixEnd_3709079 1269693541665199296703175 := by
  unfold tailWord_3709079
  simp only [CollatzResearch.WordTrace]
  refine ⟨135281224929647718105962291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90187483286431812070641527 135281224929647718105962291)
  ·
    refine ⟨202921837394471577158943437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135281224929647718105962291 202921837394471577158943437)
    ·
      refine ⟨76095689022926841434603789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202921837394471577158943437 76095689022926841434603789)
      ·
        refine ⟨28535883383597565537976421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76095689022926841434603789 28535883383597565537976421)
        ·
          refine ⟨5350478134424543538370579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28535883383597565537976421 5350478134424543538370579)
          ·
            refine ⟨8025717201636815307555869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350478134424543538370579 8025717201636815307555869)
            ·
              refine ⟨3009643950613805740333451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8025717201636815307555869 3009643950613805740333451)
              ·
                refine ⟨4514465925920708610500177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009643950613805740333451 4514465925920708610500177)
                ·
                  refine ⟨3385849444440531457875133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514465925920708610500177 3385849444440531457875133)
                  ·
                    refine ⟨1269693541665199296703175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385849444440531457875133 1269693541665199296703175)
                    ·
                      rfl

theorem cell22_3709079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_3709079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3709079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3709079 prefixEnd_3709079 := by exact prefixLift 3709079
  have htrace : WordTrace (prefixWord ++ tailWord_3709079) baseStart_3709079 baseEnd_3709079 := by
    simpa [prefixWord, tailWord_3709079, baseEnd_3709079] using wordTrace_append hprefix tailTrace_3709079
  have hstable : (prefixWord ++ tailWord_3709079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3709079).length < 2 ^ (prefixWord ++ tailWord_3709079).sum := by decide
  have hdescent : baseEnd_3709079 < baseStart_3709079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3709079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
