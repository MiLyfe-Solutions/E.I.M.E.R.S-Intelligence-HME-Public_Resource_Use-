import V185TrunkScan22Chunk275

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2460824 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 5]
def baseStart_2460824 : Nat := 118140960795 + 2460824 * 2 ^ 59
def prefixEnd_2460824 : Nat := 4983230072969 + 3 ^ 40 * 2460824 * 2
def baseEnd_2460824 : Nat := 280796781804396721885085

theorem tailTrace_2460824 : CollatzResearch.WordTrace tailWord_2460824 prefixEnd_2460824 280796781804396721885085 := by
  unfold tailWord_2460824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44876812418431199062242763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59835749891241598749657017 44876812418431199062242763)
  ·
    refine ⟨67315218627646798593364145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44876812418431199062242763 67315218627646798593364145)
    ·
      refine ⟨50486413970735098945023109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67315218627646798593364145 50486413970735098945023109)
      ·
        refine ⟨9466202619512831052191833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50486413970735098945023109 9466202619512831052191833)
        ·
          refine ⟨7099651964634623289143875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9466202619512831052191833 7099651964634623289143875)
          ·
            refine ⟨10649477946951934933715813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7099651964634623289143875 10649477946951934933715813)
            ·
              refine ⟨1996777115053487800071715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10649477946951934933715813 1996777115053487800071715)
              ·
                refine ⟨2995165672580231700107573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996777115053487800071715 2995165672580231700107573)
                ·
                  refine ⟨280796781804396721885085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2995165672580231700107573 280796781804396721885085)
                  ·
                    rfl

theorem cell22_2460824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_2460824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460824 prefixEnd_2460824 := by exact prefixLift 2460824
  have htrace : WordTrace (prefixWord ++ tailWord_2460824) baseStart_2460824 baseEnd_2460824 := by
    simpa [prefixWord, tailWord_2460824, baseEnd_2460824] using wordTrace_append hprefix tailTrace_2460824
  have hstable : (prefixWord ++ tailWord_2460824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460824).length < 2 ^ (prefixWord ++ tailWord_2460824).sum := by decide
  have hdescent : baseEnd_2460824 < baseStart_2460824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460835 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 6]
def baseStart_2460835 : Nat := 118140960795 + 2460835 * 2 ^ 59
def prefixEnd_2460835 : Nat := 4983230072969 + 3 ^ 40 * 2460835 * 2
def baseEnd_2460835 : Nat := 280798036979329934543407

theorem tailTrace_2460835 : CollatzResearch.WordTrace tailWord_2460835 prefixEnd_2460835 280798036979329934543407 := by
  unfold tailWord_2460835
  simp only [CollatzResearch.WordTrace]
  refine ⟨89754026039822547003135959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59836017359881698002090639 89754026039822547003135959)
  ·
    refine ⟨134631039059733820504703939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89754026039822547003135959 134631039059733820504703939)
    ·
      refine ⟨201946558589600730757055909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134631039059733820504703939 201946558589600730757055909)
      ·
        refine ⟨37864979735550137016947983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201946558589600730757055909 37864979735550137016947983)
        ·
          refine ⟨56797469603325205525421975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37864979735550137016947983 56797469603325205525421975)
          ·
            refine ⟨85196204404987808288132963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56797469603325205525421975 85196204404987808288132963)
            ·
              refine ⟨127794306607481712432199445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85196204404987808288132963 127794306607481712432199445)
              ·
                refine ⟨5990358122225705270259349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127794306607481712432199445 5990358122225705270259349)
                ·
                  refine ⟨280798036979329934543407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5990358122225705270259349 280798036979329934543407)
                  ·
                    rfl

theorem cell22_2460835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_2460835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460835 prefixEnd_2460835 := by exact prefixLift 2460835
  have htrace : WordTrace (prefixWord ++ tailWord_2460835) baseStart_2460835 baseEnd_2460835 := by
    simpa [prefixWord, tailWord_2460835, baseEnd_2460835] using wordTrace_append hprefix tailTrace_2460835
  have hstable : (prefixWord ++ tailWord_2460835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460835).length < 2 ^ (prefixWord ++ tailWord_2460835).sum := by decide
  have hdescent : baseEnd_2460835 < baseStart_2460835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460837 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_2460837 : Nat := 118140960795 + 2460837 * 2 ^ 59
def prefixEnd_2460837 : Nat := 4983230072969 + 3 ^ 40 * 2460837 * 2
def baseEnd_2460837 : Nat := 842394795578862465080215

theorem tailTrace_2460837 : CollatzResearch.WordTrace tailWord_2460837 prefixEnd_2460837 842394795578862465080215 := by
  unfold tailWord_2460837
  simp only [CollatzResearch.WordTrace]
  refine ⟨89754098985815301344708765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59836065990543534229805843 89754098985815301344708765)
  ·
    refine ⟨33657787119680738004265787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89754098985815301344708765 33657787119680738004265787)
    ·
      refine ⟨50486680679521107006398681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33657787119680738004265787 50486680679521107006398681)
      ·
        refine ⟨37865010509640830254799011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50486680679521107006398681 37865010509640830254799011)
        ·
          refine ⟨56797515764461245382198517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37865010509640830254799011 56797515764461245382198517)
          ·
            refine ⟨5324767102918241754581111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56797515764461245382198517 5324767102918241754581111)
            ·
              refine ⟨7987150654377362631871667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324767102918241754581111 7987150654377362631871667)
              ·
                refine ⟨11980725981566043947807501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7987150654377362631871667 11980725981566043947807501)
                ·
                  refine ⟨4492772243087266480427813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11980725981566043947807501 4492772243087266480427813)
                  ·
                    refine ⟨842394795578862465080215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4492772243087266480427813 842394795578862465080215)
                    ·
                      rfl

theorem cell22_2460837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_2460837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460837 prefixEnd_2460837 := by exact prefixLift 2460837
  have htrace : WordTrace (prefixWord ++ tailWord_2460837) baseStart_2460837 baseEnd_2460837 := by
    simpa [prefixWord, tailWord_2460837, baseEnd_2460837] using wordTrace_append hprefix tailTrace_2460837
  have hstable : (prefixWord ++ tailWord_2460837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460837).length < 2 ^ (prefixWord ++ tailWord_2460837).sum := by decide
  have hdescent : baseEnd_2460837 < baseStart_2460837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460882 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2460882 : Nat := 118140960795 + 2460882 * 2 ^ 59
def prefixEnd_2460882 : Nat := 4983230072969 + 3 ^ 40 * 2460882 * 2
def baseEnd_2460882 : Nat := 842410199998497347705077

theorem tailTrace_2460882 : CollatzResearch.WordTrace tailWord_2460882 prefixEnd_2460882 842410199998497347705077 := by
  unfold tailWord_2460882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22438935067663068507524225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59837160180434849353397933 22438935067663068507524225)
  ·
    refine ⟨16829201300747301380643169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22438935067663068507524225 16829201300747301380643169)
    ·
      refine ⟨12621900975560476035482377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16829201300747301380643169 12621900975560476035482377)
      ·
        refine ⟨9466425731670357026611783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12621900975560476035482377 9466425731670357026611783)
        ·
          refine ⟨14199638597505535539917675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9466425731670357026611783 14199638597505535539917675)
          ·
            refine ⟨21299457896258303309876513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14199638597505535539917675 21299457896258303309876513)
            ·
              refine ⟨15974593422193727482407385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21299457896258303309876513 15974593422193727482407385)
              ·
                refine ⟨11980945066645295611805539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15974593422193727482407385 11980945066645295611805539)
                ·
                  refine ⟨17971417599967943417708309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11980945066645295611805539 17971417599967943417708309)
                  ·
                    refine ⟨842410199998497347705077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17971417599967943417708309 842410199998497347705077)
                    ·
                      rfl

theorem cell22_2460882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2460882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460882 prefixEnd_2460882 := by exact prefixLift 2460882
  have htrace : WordTrace (prefixWord ++ tailWord_2460882) baseStart_2460882 baseEnd_2460882 := by
    simpa [prefixWord, tailWord_2460882, baseEnd_2460882] using wordTrace_append hprefix tailTrace_2460882
  have hstable : (prefixWord ++ tailWord_2460882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460882).length < 2 ^ (prefixWord ++ tailWord_2460882).sum := by decide
  have hdescent : baseEnd_2460882 < baseStart_2460882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460886 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2460886 : Nat := 118140960795 + 2460886 * 2 ^ 59
def prefixEnd_2460886 : Nat := 4983230072969 + 3 ^ 40 * 2460886 * 2
def baseEnd_2460886 : Nat := 280803856426747556868355

theorem tailTrace_2460886 : CollatzResearch.WordTrace tailWord_2460886 prefixEnd_2460886 280803856426747556868355 := by
  unfold tailWord_2460886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609742885164861419577657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59837257441758521808828341 5609742885164861419577657)
  ·
    refine ⟨4207307163873646064683243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5609742885164861419577657 4207307163873646064683243)
    ·
      refine ⟨6310960745810469097024865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207307163873646064683243 6310960745810469097024865)
      ·
        refine ⟨4733220559357851822768649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6310960745810469097024865 4733220559357851822768649)
        ·
          refine ⟨3549915419518388867076487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4733220559357851822768649 3549915419518388867076487)
          ·
            refine ⟨5324873129277583300614731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549915419518388867076487 5324873129277583300614731)
            ·
              refine ⟨7987309693916374950922097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324873129277583300614731 7987309693916374950922097)
              ·
                refine ⟨5990482270437281213191573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7987309693916374950922097 5990482270437281213191573)
                ·
                  refine ⟨280803856426747556868355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5990482270437281213191573 280803856426747556868355)
                  ·
                    rfl

theorem cell22_2460886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2460886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460886 prefixEnd_2460886 := by exact prefixLift 2460886
  have htrace : WordTrace (prefixWord ++ tailWord_2460886) baseStart_2460886 baseEnd_2460886 := by
    simpa [prefixWord, tailWord_2460886, baseEnd_2460886] using wordTrace_append hprefix tailTrace_2460886
  have hstable : (prefixWord ++ tailWord_2460886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460886).length < 2 ^ (prefixWord ++ tailWord_2460886).sum := by decide
  have hdescent : baseEnd_2460886 < baseStart_2460886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460929 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2460929 : Nat := 118140960795 + 2460929 * 2 ^ 59
def prefixEnd_2460929 : Nat := 4983230072969 + 3 ^ 40 * 2460929 * 2
def baseEnd_2460929 : Nat := 842426289059004891779933

theorem tailTrace_2460929 : CollatzResearch.WordTrace tailWord_2460929 prefixEnd_2460929 842426289059004891779933 := by
  unfold tailWord_2460929
  simp only [CollatzResearch.WordTrace]
  refine ⟨89757454501482001057057841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59838303000988000704705227 89757454501482001057057841)
  ·
    refine ⟨67318090876111500792793381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89757454501482001057057841 67318090876111500792793381)
    ·
      refine ⟨12622142039270906398648759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67318090876111500792793381 12622142039270906398648759)
      ·
        refine ⟨18933213058906359597973139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12622142039270906398648759 18933213058906359597973139)
        ·
          refine ⟨28399819588359539396959709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18933213058906359597973139 28399819588359539396959709)
          ·
            refine ⟨10649932345634827273859891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28399819588359539396959709 10649932345634827273859891)
            ·
              refine ⟨15974898518452240910789837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10649932345634827273859891 15974898518452240910789837)
              ·
                refine ⟨5990586944419590341546189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15974898518452240910789837 5990586944419590341546189)
                ·
                  refine ⟨2246470104157346378079821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5990586944419590341546189 2246470104157346378079821)
                  ·
                    refine ⟨842426289059004891779933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246470104157346378079821 842426289059004891779933)
                    ·
                      rfl

theorem cell22_2460929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2460929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460929 prefixEnd_2460929 := by exact prefixLift 2460929
  have htrace : WordTrace (prefixWord ++ tailWord_2460929) baseStart_2460929 baseEnd_2460929 := by
    simpa [prefixWord, tailWord_2460929, baseEnd_2460929] using wordTrace_append hprefix tailTrace_2460929
  have hstable : (prefixWord ++ tailWord_2460929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460929).length < 2 ^ (prefixWord ++ tailWord_2460929).sum := by decide
  have hdescent : baseEnd_2460929 < baseStart_2460929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460963 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 1, 3]
def baseStart_2460963 : Nat := 118140960795 + 2460963 * 2 ^ 59
def prefixEnd_2460963 : Nat := 4983230072969 + 3 ^ 40 * 2460963 * 2
def baseEnd_2460963 : Nat := 842437927953840136429829

theorem tailTrace_2460963 : CollatzResearch.WordTrace tailWord_2460963 prefixEnd_2460963 842437927953840136429829 := by
  unfold tailWord_2460963
  simp only [CollatzResearch.WordTrace]
  refine ⟨89758694583358824863795543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59839129722239216575863695 89758694583358824863795543)
  ·
    refine ⟨134638041875038237295693315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89758694583358824863795543 134638041875038237295693315)
    ·
      refine ⟨201957062812557355943539973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134638041875038237295693315 201957062812557355943539973)
      ·
        refine ⟨37866949277354504239413745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201957062812557355943539973 37866949277354504239413745)
        ·
          refine ⟨28400211958015878179560309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37866949277354504239413745 28400211958015878179560309)
          ·
            refine ⟨2662519871063988579333779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28400211958015878179560309 2662519871063988579333779)
            ·
              refine ⟨3993779806595982869000669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662519871063988579333779 3993779806595982869000669)
              ·
                refine ⟨1497667427473493575875251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3993779806595982869000669 1497667427473493575875251)
                ·
                  refine ⟨2246501141210240363812877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497667427473493575875251 2246501141210240363812877)
                  ·
                    refine ⟨842437927953840136429829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246501141210240363812877 842437927953840136429829)
                    ·
                      rfl

theorem cell22_2460963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 3].length) (baseStart_2460963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460963 prefixEnd_2460963 := by exact prefixLift 2460963
  have htrace : WordTrace (prefixWord ++ tailWord_2460963) baseStart_2460963 baseEnd_2460963 := by
    simpa [prefixWord, tailWord_2460963, baseEnd_2460963] using wordTrace_append hprefix tailTrace_2460963
  have hstable : (prefixWord ++ tailWord_2460963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460963).length < 2 ^ (prefixWord ++ tailWord_2460963).sum := by decide
  have hdescent : baseEnd_2460963 < baseStart_2460963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460972 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_2460972 : Nat := 118140960795 + 2460972 * 2 ^ 59
def prefixEnd_2460972 : Nat := 4983230072969 + 3 ^ 40 * 2460972 * 2
def baseEnd_2460972 : Nat := 842441008837767112954801

theorem tailTrace_2460972 : CollatzResearch.WordTrace tailWord_2460972 prefixEnd_2460972 842441008837767112954801 := by
  unfold tailWord_2460972
  simp only [CollatzResearch.WordTrace]
  refine ⟨44879511420163109700436585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59839348560217479600582113 44879511420163109700436585)
  ·
    refine ⟨33659633565122332275327439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44879511420163109700436585 33659633565122332275327439)
    ·
      refine ⟨50489450347683498412991159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33659633565122332275327439 50489450347683498412991159)
      ·
        refine ⟨75734175521525247619486739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50489450347683498412991159 75734175521525247619486739)
        ·
          refine ⟨113601263282287871429230109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75734175521525247619486739 113601263282287871429230109)
          ·
            refine ⟨42600473730857951785961291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113601263282287871429230109 42600473730857951785961291)
            ·
              refine ⟨63900710596286927678941937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42600473730857951785961291 63900710596286927678941937)
              ·
                refine ⟨47925532947215195759206453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63900710596286927678941937 47925532947215195759206453)
                ·
                  refine ⟨4493018713801424602425605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47925532947215195759206453 4493018713801424602425605)
                  ·
                    refine ⟨842441008837767112954801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493018713801424602425605 842441008837767112954801)
                    ·
                      rfl

theorem cell22_2460972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_2460972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460972 prefixEnd_2460972 := by exact prefixLift 2460972
  have htrace : WordTrace (prefixWord ++ tailWord_2460972) baseStart_2460972 baseEnd_2460972 := by
    simpa [prefixWord, tailWord_2460972, baseEnd_2460972] using wordTrace_append hprefix tailTrace_2460972
  have hstable : (prefixWord ++ tailWord_2460972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460972).length < 2 ^ (prefixWord ++ tailWord_2460972).sum := by decide
  have hdescent : baseEnd_2460972 < baseStart_2460972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460980 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_2460980 : Nat := 118140960795 + 2460980 * 2 ^ 59
def prefixEnd_2460980 : Nat := 4983230072969 + 3 ^ 40 * 2460980 * 2
def baseEnd_2460980 : Nat := 842443747401257758754777

theorem tailTrace_2460980 : CollatzResearch.WordTrace tailWord_2460980 prefixEnd_2460980 842443747401257758754777 := by
  unfold tailWord_2460980
  simp only [CollatzResearch.WordTrace]
  refine ⟨44879657312148618383582197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59839543082864824511442929 44879657312148618383582197)
  ·
    refine ⟨4207467873013932973460831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44879657312148618383582197 4207467873013932973460831)
    ·
      refine ⟨6311201809520899460191247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207467873013932973460831 6311201809520899460191247)
      ·
        refine ⟨9466802714281349190286871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6311201809520899460191247 9466802714281349190286871)
        ·
          refine ⟨14200204071422023785430307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9466802714281349190286871 14200204071422023785430307)
          ·
            refine ⟨21300306107133035678145461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14200204071422023785430307 21300306107133035678145461)
            ·
              refine ⟨1996903697543722094826137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21300306107133035678145461 1996903697543722094826137)
              ·
                refine ⟨1497677773157791571119603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996903697543722094826137 1497677773157791571119603)
                ·
                  refine ⟨2246516659736687356679405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497677773157791571119603 2246516659736687356679405)
                  ·
                    refine ⟨842443747401257758754777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246516659736687356679405 842443747401257758754777)
                    ·
                      rfl

theorem cell22_2460980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_2460980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460980 prefixEnd_2460980 := by exact prefixLift 2460980
  have htrace : WordTrace (prefixWord ++ tailWord_2460980) baseStart_2460980 baseEnd_2460980 := by
    simpa [prefixWord, tailWord_2460980, baseEnd_2460980] using wordTrace_append hprefix tailTrace_2460980
  have hstable : (prefixWord ++ tailWord_2460980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460980).length < 2 ^ (prefixWord ++ tailWord_2460980).sum := by decide
  have hdescent : baseEnd_2460980 < baseStart_2460980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460993 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 5]
def baseStart_2460993 : Nat := 118140960795 + 2460993 * 2 ^ 59
def prefixEnd_2460993 : Nat := 4983230072969 + 3 ^ 40 * 2460993 * 2
def baseEnd_2460993 : Nat := 280816065855643352726579

theorem tailTrace_2460993 : CollatzResearch.WordTrace tailWord_2460993 prefixEnd_2460993 280816065855643352726579 := by
  unfold tailWord_2460993
  simp only [CollatzResearch.WordTrace]
  refine ⟨89759788773250139987387633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59839859182166759991591755 89759788773250139987387633)
  ·
    refine ⟨67319841579937604990540725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89759788773250139987387633 67319841579937604990540725)
    ·
      refine ⟨6311235148119150467863193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67319841579937604990540725 6311235148119150467863193)
      ·
        refine ⟨4733426361089362850897395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6311235148119150467863193 4733426361089362850897395)
        ·
          refine ⟨7100139541634044276346093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4733426361089362850897395 7100139541634044276346093)
          ·
            refine ⟨2662552328112766603629785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7100139541634044276346093 2662552328112766603629785)
            ·
              refine ⟨1996914246084574952722339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2662552328112766603629785 1996914246084574952722339)
              ·
                refine ⟨2995371369126862429083509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996914246084574952722339 2995371369126862429083509)
                ·
                  refine ⟨280816065855643352726579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2995371369126862429083509 280816065855643352726579)
                  ·
                    rfl

theorem cell22_2460993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_2460993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460993 prefixEnd_2460993 := by exact prefixLift 2460993
  have htrace : WordTrace (prefixWord ++ tailWord_2460993) baseStart_2460993 baseEnd_2460993 := by
    simpa [prefixWord, tailWord_2460993, baseEnd_2460993] using wordTrace_append hprefix tailTrace_2460993
  have hstable : (prefixWord ++ tailWord_2460993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460993).length < 2 ^ (prefixWord ++ tailWord_2460993).sum := by decide
  have hdescent : baseEnd_2460993 < baseStart_2460993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461002 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2461002 : Nat := 118140960795 + 2461002 * 2 ^ 59
def prefixEnd_2461002 : Nat := 4983230072969 + 3 ^ 40 * 2461002 * 2
def baseEnd_2461002 : Nat := 842451278450857034704709

theorem tailTrace_2461002 : CollatzResearch.WordTrace tailWord_2461002 prefixEnd_2461002 842451278450857034704709 := by
  unfold tailWord_2461002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22440029257554383631116315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59840078020145023016310173 22440029257554383631116315)
  ·
    refine ⟨33660043886331575446674473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22440029257554383631116315 33660043886331575446674473)
    ·
      refine ⟨25245032914748681585005855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33660043886331575446674473 25245032914748681585005855)
      ·
        refine ⟨37867549372123022377508783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25245032914748681585005855 37867549372123022377508783)
        ·
          refine ⟨56801324058184533566263175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37867549372123022377508783 56801324058184533566263175)
          ·
            refine ⟨85201986087276800349394763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56801324058184533566263175 85201986087276800349394763)
            ·
              refine ⟨127802979130915200524092145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85201986087276800349394763 127802979130915200524092145)
              ·
                refine ⟨95852234348186400393069109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127802979130915200524092145 95852234348186400393069109)
                ·
                  refine ⟨8986146970142475036850229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95852234348186400393069109 8986146970142475036850229)
                  ·
                    refine ⟨842451278450857034704709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8986146970142475036850229 842451278450857034704709)
                    ·
                      rfl

theorem cell22_2461002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2461002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461002 prefixEnd_2461002 := by exact prefixLift 2461002
  have htrace : WordTrace (prefixWord ++ tailWord_2461002) baseStart_2461002 baseEnd_2461002 := by
    simpa [prefixWord, tailWord_2461002, baseEnd_2461002] using wordTrace_append hprefix tailTrace_2461002
  have hstable : (prefixWord ++ tailWord_2461002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461002).length < 2 ^ (prefixWord ++ tailWord_2461002).sum := by decide
  have hdescent : baseEnd_2461002 < baseStart_2461002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461017 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_2461017 : Nat := 118140960795 + 2461017 * 2 ^ 59
def prefixEnd_2461017 : Nat := 4983230072969 + 3 ^ 40 * 2461017 * 2
def baseEnd_2461017 : Nat := 842456413257401995579663

theorem tailTrace_2461017 : CollatzResearch.WordTrace tailWord_2461017 prefixEnd_2461017 842456413257401995579663 := by
  unfold tailWord_2461017
  simp only [CollatzResearch.WordTrace]
  refine ⟨89760664125163192086261305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59840442750108794724174203 89760664125163192086261305)
  ·
    refine ⟨67320498093872394064695979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89760664125163192086261305 67320498093872394064695979)
    ·
      refine ⟨100980747140808591097043969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67320498093872394064695979 100980747140808591097043969)
      ·
        refine ⟨75735560355606443322782977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100980747140808591097043969 75735560355606443322782977)
        ·
          refine ⟨56801670266704832492087233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75735560355606443322782977 56801670266704832492087233)
          ·
            refine ⟨42601252700028624369065425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56801670266704832492087233 42601252700028624369065425)
            ·
              refine ⟨31950939525021468276799069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42601252700028624369065425 31950939525021468276799069)
              ·
                refine ⟨11981602321883050603799651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31950939525021468276799069 11981602321883050603799651)
                ·
                  refine ⟨17972403482824575905699477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11981602321883050603799651 17972403482824575905699477)
                  ·
                    refine ⟨842456413257401995579663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17972403482824575905699477 842456413257401995579663)
                    ·
                      rfl

theorem cell22_2461017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_2461017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461017 prefixEnd_2461017 := by exact prefixLift 2461017
  have htrace : WordTrace (prefixWord ++ tailWord_2461017) baseStart_2461017 baseEnd_2461017 := by
    simpa [prefixWord, tailWord_2461017, baseEnd_2461017] using wordTrace_append hprefix tailTrace_2461017
  have hstable : (prefixWord ++ tailWord_2461017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461017).length < 2 ^ (prefixWord ++ tailWord_2461017).sum := by decide
  have hdescent : baseEnd_2461017 < baseStart_2461017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461032 : List Nat := [2, 1, 4, 2, 13]
def baseStart_2461032 : Nat := 118140960795 + 2461032 * 2 ^ 59
def prefixEnd_2461032 : Nat := 4983230072969 + 3 ^ 40 * 2461032 * 2
def baseEnd_2461032 : Nat := 3466919950880440150019

theorem tailTrace_2461032 : CollatzResearch.WordTrace tailWord_2461032 prefixEnd_2461032 3466919950880440150019 := by
  unfold tailWord_2461032
  simp only [CollatzResearch.WordTrace]
  refine ⟨44880605610054424824028675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59840807480072566432038233 44880605610054424824028675)
  ·
    refine ⟨67320908415081637236043013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44880605610054424824028675 67320908415081637236043013)
    ·
      refine ⟨12622670327827806981758065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67320908415081637236043013 12622670327827806981758065)
      ·
        refine ⟨9467002745870855236318549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12622670327827806981758065 9467002745870855236318549)
        ·
          refine ⟨3466919950880440150019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9467002745870855236318549 3466919950880440150019)
          ·
            rfl

theorem cell22_2461032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 13].length) (baseStart_2461032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461032 prefixEnd_2461032 := by exact prefixLift 2461032
  have htrace : WordTrace (prefixWord ++ tailWord_2461032) baseStart_2461032 baseEnd_2461032 := by
    simpa [prefixWord, tailWord_2461032, baseEnd_2461032] using wordTrace_append hprefix tailTrace_2461032
  have hstable : (prefixWord ++ tailWord_2461032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461032).length < 2 ^ (prefixWord ++ tailWord_2461032).sum := by decide
  have hdescent : baseEnd_2461032 < baseStart_2461032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461036 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_2461036 : Nat := 118140960795 + 2461036 * 2 ^ 59
def prefixEnd_2461036 : Nat := 4983230072969 + 3 ^ 40 * 2461036 * 2
def baseEnd_2461036 : Nat := 842462917345692279354605

theorem tailTrace_2461036 : CollatzResearch.WordTrace tailWord_2461036 prefixEnd_2461036 842462917345692279354605 := by
  unfold tailWord_2461036
  simp only [CollatzResearch.WordTrace]
  refine ⟨44880678556047179165601481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59840904741396238887468641 44880678556047179165601481)
  ·
    refine ⟨33660508917035384374201111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44880678556047179165601481 33660508917035384374201111)
    ·
      refine ⟨50490763375553076561301667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33660508917035384374201111 50490763375553076561301667)
      ·
        refine ⟨75736145063329614841952501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50490763375553076561301667 75736145063329614841952501)
        ·
          refine ⟨7100263599687151391433047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75736145063329614841952501 7100263599687151391433047)
          ·
            refine ⟨10650395399530727087149571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7100263599687151391433047 10650395399530727087149571)
            ·
              refine ⟨15975593099296090630724357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10650395399530727087149571 15975593099296090630724357)
              ·
                refine ⟨2995423706118016993260817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15975593099296090630724357 2995423706118016993260817)
                ·
                  refine ⟨2246567779588512744945613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2995423706118016993260817 2246567779588512744945613)
                  ·
                    refine ⟨842462917345692279354605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246567779588512744945613 842462917345692279354605)
                    ·
                      rfl

theorem cell22_2461036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_2461036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461036 prefixEnd_2461036 := by exact prefixLift 2461036
  have htrace : WordTrace (prefixWord ++ tailWord_2461036) baseStart_2461036 baseEnd_2461036 := by
    simpa [prefixWord, tailWord_2461036, baseEnd_2461036] using wordTrace_append hprefix tailTrace_2461036
  have hstable : (prefixWord ++ tailWord_2461036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461036).length < 2 ^ (prefixWord ++ tailWord_2461036).sum := by decide
  have hdescent : baseEnd_2461036 < baseStart_2461036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461111 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 5]
def baseStart_2461111 : Nat := 118140960795 + 2461111 * 2 ^ 59
def prefixEnd_2461111 : Nat := 4983230072969 + 3 ^ 40 * 2461111 * 2
def baseEnd_2461111 : Nat := 280829530459472361243125

theorem tailTrace_2461111 : CollatzResearch.WordTrace tailWord_2461111 prefixEnd_2461111 280829530459472361243125 := by
  unfold tailWord_2461111
  simp only [CollatzResearch.WordTrace]
  refine ⟨89764092586822646140183187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59842728391215097426788791 89764092586822646140183187)
  ·
    refine ⟨134646138880233969210274781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89764092586822646140183187 134646138880233969210274781)
    ·
      refine ⟨50492302080087738453853043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134646138880233969210274781 50492302080087738453853043)
      ·
        refine ⟨75738453120131607680779565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50492302080087738453853043 75738453120131607680779565)
        ·
          refine ⟨28401919920049352880292337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75738453120131607680779565 28401919920049352880292337)
          ·
            refine ⟨21301439940037014660219253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28401919920049352880292337 21301439940037014660219253)
            ·
              refine ⟨1997009994378470124395555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21301439940037014660219253 1997009994378470124395555)
              ·
                refine ⟨2995514991567705186593333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997009994378470124395555 2995514991567705186593333)
                ·
                  refine ⟨280829530459472361243125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2995514991567705186593333 280829530459472361243125)
                  ·
                    rfl

theorem cell22_2461111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 5].length) (baseStart_2461111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461111 prefixEnd_2461111 := by exact prefixLift 2461111
  have htrace : WordTrace (prefixWord ++ tailWord_2461111) baseStart_2461111 baseEnd_2461111 := by
    simpa [prefixWord, tailWord_2461111, baseEnd_2461111] using wordTrace_append hprefix tailTrace_2461111
  have hstable : (prefixWord ++ tailWord_2461111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461111).length < 2 ^ (prefixWord ++ tailWord_2461111).sum := by decide
  have hdescent : baseEnd_2461111 < baseStart_2461111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461141 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2461141 : Nat := 118140960795 + 2461141 * 2 ^ 59
def prefixEnd_2461141 : Nat := 4983230072969 + 3 ^ 40 * 2461141 * 2
def baseEnd_2461141 : Nat := 842498860991507005479283

theorem tailTrace_2461141 : CollatzResearch.WordTrace tailWord_2461141 prefixEnd_2461141 842498860991507005479283 := by
  unfold tailWord_2461141
  simp only [CollatzResearch.WordTrace]
  refine ⟨89765186776713961263775277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59843457851142640842516851 89765186776713961263775277)
  ·
    refine ⟨33661945041267735473915729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89765186776713961263775277 33661945041267735473915729)
    ·
      refine ⟨25246458780950801605436797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33661945041267735473915729 25246458780950801605436797)
      ·
        refine ⟨9467422042856550602038799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25246458780950801605436797 9467422042856550602038799)
        ·
          refine ⟨14201133064284825903058199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9467422042856550602038799 14201133064284825903058199)
          ·
            refine ⟨21301699596427238854587299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14201133064284825903058199 21301699596427238854587299)
            ·
              refine ⟨31952549394640858281880949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21301699596427238854587299 31952549394640858281880949)
              ·
                refine ⟨2995551505747580463926339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31952549394640858281880949 2995551505747580463926339)
                ·
                  refine ⟨4493327258621370695889509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995551505747580463926339 4493327258621370695889509)
                  ·
                    refine ⟨842498860991507005479283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493327258621370695889509 842498860991507005479283)
                    ·
                      rfl

theorem cell22_2461141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2461141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461141 prefixEnd_2461141 := by exact prefixLift 2461141
  have htrace : WordTrace (prefixWord ++ tailWord_2461141) baseStart_2461141 baseEnd_2461141 := by
    simpa [prefixWord, tailWord_2461141, baseEnd_2461141] using wordTrace_append hprefix tailTrace_2461141
  have hstable : (prefixWord ++ tailWord_2461141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461141).length < 2 ^ (prefixWord ++ tailWord_2461141).sum := by decide
  have hdescent : baseEnd_2461141 < baseStart_2461141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461156 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 4]
def baseStart_2461156 : Nat := 118140960795 + 2461156 * 2 ^ 59
def prefixEnd_2461156 : Nat := 4983230072969 + 3 ^ 40 * 2461156 * 2
def baseEnd_2461156 : Nat := 280834665266017322118079

theorem tailTrace_2461156 : CollatzResearch.WordTrace tailWord_2461156 prefixEnd_2461156 280834665266017322118079 := by
  unfold tailWord_2461156
  simp only [CollatzResearch.WordTrace]
  refine ⟨44882866935829809412785661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59843822581106412550380881 44882866935829809412785661)
  ·
    refine ⟨16831075100936178529794623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44882866935829809412785661 16831075100936178529794623)
    ·
      refine ⟨25246612651404267794691935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16831075100936178529794623 25246612651404267794691935)
      ·
        refine ⟨37869918977106401692037903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25246612651404267794691935 37869918977106401692037903)
        ·
          refine ⟨56804878465659602538056855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37869918977106401692037903 56804878465659602538056855)
          ·
            refine ⟨85207317698489403807085283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56804878465659602538056855 85207317698489403807085283)
            ·
              refine ⟨127810976547734105710627925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85207317698489403807085283 127810976547734105710627925)
              ·
                refine ⟨1497784881418759051296421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 127810976547734105710627925 1497784881418759051296421)
                ·
                  refine ⟨280834665266017322118079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497784881418759051296421 280834665266017322118079)
                  ·
                    rfl

theorem cell22_2461156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_2461156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461156 prefixEnd_2461156 := by exact prefixLift 2461156
  have htrace : WordTrace (prefixWord ++ tailWord_2461156) baseStart_2461156 baseEnd_2461156 := by
    simpa [prefixWord, tailWord_2461156, baseEnd_2461156] using wordTrace_append hprefix tailTrace_2461156
  have hstable : (prefixWord ++ tailWord_2461156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461156).length < 2 ^ (prefixWord ++ tailWord_2461156).sum := by decide
  have hdescent : baseEnd_2461156 < baseStart_2461156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461188 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2461188 : Nat := 118140960795 + 2461188 * 2 ^ 59
def prefixEnd_2461188 : Nat := 4983230072969 + 3 ^ 40 * 2461188 * 2
def baseEnd_2461188 : Nat := 842514950052014549554139

theorem tailTrace_2461188 : CollatzResearch.WordTrace tailWord_2461188 prefixEnd_2461188 842514950052014549554139 := by
  unfold tailWord_2461188
  simp only [CollatzResearch.WordTrace]
  refine ⟨44883450503771844145368109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59844600671695792193824145 44883450503771844145368109)
  ·
    refine ⟨16831293938914441554513041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44883450503771844145368109 16831293938914441554513041)
    ·
      refine ⟨12623470454185831165884781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16831293938914441554513041 12623470454185831165884781)
      ·
        refine ⟨4733801420319686687206793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12623470454185831165884781 4733801420319686687206793)
        ·
          refine ⟨3550351065239765015405095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4733801420319686687206793 3550351065239765015405095)
          ·
            refine ⟨5325526597859647523107643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550351065239765015405095 5325526597859647523107643)
            ·
              refine ⟨7988289896789471284661465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5325526597859647523107643 7988289896789471284661465)
              ·
                refine ⟨5991217422592103463496099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7988289896789471284661465 5991217422592103463496099)
                ·
                  refine ⟨8986826133888155195244149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991217422592103463496099 8986826133888155195244149)
                  ·
                    refine ⟨842514950052014549554139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8986826133888155195244149 842514950052014549554139)
                    ·
                      rfl

theorem cell22_2461188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2461188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461188 prefixEnd_2461188 := by exact prefixLift 2461188
  have htrace : WordTrace (prefixWord ++ tailWord_2461188) baseStart_2461188 baseEnd_2461188 := by
    simpa [prefixWord, tailWord_2461188, baseEnd_2461188] using wordTrace_append hprefix tailTrace_2461188
  have hstable : (prefixWord ++ tailWord_2461188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461188).length < 2 ^ (prefixWord ++ tailWord_2461188).sum := by decide
  have hdescent : baseEnd_2461188 < baseStart_2461188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461321 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_2461321 : Nat := 118140960795 + 2461321 * 2 ^ 59
def prefixEnd_2461321 : Nat := 4983230072969 + 3 ^ 40 * 2461321 * 2
def baseEnd_2461321 : Nat := 842560478670046535978731

theorem tailTrace_2461321 : CollatzResearch.WordTrace tailWord_2461321 prefixEnd_2461321 842560478670046535978731 := by
  unfold tailWord_2461321
  simp only [CollatzResearch.WordTrace]
  refine ⟨89771751916061852005327817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59847834610707901336885211 89771751916061852005327817)
  ·
    refine ⟨67328813937046389003995863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89771751916061852005327817 67328813937046389003995863)
    ·
      refine ⟨100993220905569583505993795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67328813937046389003995863 100993220905569583505993795)
      ·
        refine ⟨151489831358354375258990693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100993220905569583505993795 151489831358354375258990693)
        ·
          refine ⟨28404343379691445361060755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151489831358354375258990693 28404343379691445361060755)
          ·
            refine ⟨42606515069537168041591133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28404343379691445361060755 42606515069537168041591133)
            ·
              refine ⟨15977443151076438015596675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42606515069537168041591133 15977443151076438015596675)
              ·
                refine ⟨23966164726614657023395013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15977443151076438015596675 23966164726614657023395013)
                ·
                  refine ⟨4493655886240248191886565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23966164726614657023395013 4493655886240248191886565)
                  ·
                    refine ⟨842560478670046535978731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493655886240248191886565 842560478670046535978731)
                    ·
                      rfl

theorem cell22_2461321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_2461321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461321 prefixEnd_2461321 := by exact prefixLift 2461321
  have htrace : WordTrace (prefixWord ++ tailWord_2461321) baseStart_2461321 baseEnd_2461321 := by
    simpa [prefixWord, tailWord_2461321, baseEnd_2461321] using wordTrace_append hprefix tailTrace_2461321
  have hstable : (prefixWord ++ tailWord_2461321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461321).length < 2 ^ (prefixWord ++ tailWord_2461321).sum := by decide
  have hdescent : baseEnd_2461321 < baseStart_2461321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461323 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 2, 3]
def baseStart_2461323 : Nat := 118140960795 + 2461323 * 2 ^ 59
def prefixEnd_2461323 : Nat := 4983230072969 + 3 ^ 40 * 2461323 * 2
def baseEnd_2461323 : Nat := 842561163310919197428725

theorem tailTrace_2461323 : CollatzResearch.WordTrace tailWord_2461323 prefixEnd_2461323 842561163310919197428725 := by
  unfold tailWord_2461323
  simp only [CollatzResearch.WordTrace]
  refine ⟨89771824862054606346900623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59847883241369737564600415 89771824862054606346900623)
  ·
    refine ⟨134657737293081909520350935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89771824862054606346900623 134657737293081909520350935)
    ·
      refine ⟨201986605939622864280526403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134657737293081909520350935 201986605939622864280526403)
      ·
        refine ⟨302979908909434296420789605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201986605939622864280526403 302979908909434296420789605)
        ·
          refine ⟨56808732920518930578898051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302979908909434296420789605 56808732920518930578898051)
          ·
            refine ⟨85213099380778395868347077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56808732920518930578898051 85213099380778395868347077)
            ·
              refine ⟨15977456133895949225315077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85213099380778395868347077 15977456133895949225315077)
              ·
                refine ⟨2995773025105490479746577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15977456133895949225315077 2995773025105490479746577)
                ·
                  refine ⟨2246829768829117859809933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2995773025105490479746577 2246829768829117859809933)
                  ·
                    refine ⟨842561163310919197428725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246829768829117859809933 842561163310919197428725)
                    ·
                      rfl

theorem cell22_2461323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 3].length) (baseStart_2461323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461323 prefixEnd_2461323 := by exact prefixLift 2461323
  have htrace : WordTrace (prefixWord ++ tailWord_2461323) baseStart_2461323 baseEnd_2461323 := by
    simpa [prefixWord, tailWord_2461323, baseEnd_2461323] using wordTrace_append hprefix tailTrace_2461323
  have hstable : (prefixWord ++ tailWord_2461323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461323).length < 2 ^ (prefixWord ++ tailWord_2461323).sum := by decide
  have hdescent : baseEnd_2461323 < baseStart_2461323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461336 : List Nat := [2, 1, 2, 4, 1, 2, 1, 9]
def baseStart_2461336 : Nat := 118140960795 + 2461336 * 2 ^ 59
def prefixEnd_2461336 : Nat := 4983230072969 + 3 ^ 40 * 2461336 * 2
def baseEnd_2461336 : Nat := 93618401497399055205965

theorem tailTrace_2461336 : CollatzResearch.WordTrace tailWord_2461336 prefixEnd_2461336 93618401497399055205965 := by
  unfold tailWord_2461336
  simp only [CollatzResearch.WordTrace]
  refine ⟨44886149505503754783561931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59848199340671673044749241 44886149505503754783561931)
  ·
    refine ⟨67329224258255632175342897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44886149505503754783561931 67329224258255632175342897)
    ·
      refine ⟨50496918193691724131507173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67329224258255632175342897 50496918193691724131507173)
      ·
        refine ⟨9468172161317198274657595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50496918193691724131507173 9468172161317198274657595)
        ·
          refine ⟨14202258241975797411986393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9468172161317198274657595 14202258241975797411986393)
          ·
            refine ⟨10651693681481848058989795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14202258241975797411986393 10651693681481848058989795)
            ·
              refine ⟨15977540522222772088484693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10651693681481848058989795 15977540522222772088484693)
              ·
                refine ⟨93618401497399055205965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15977540522222772088484693 93618401497399055205965)
                ·
                  rfl

theorem cell22_2461336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_2461336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461336 prefixEnd_2461336 := by exact prefixLift 2461336
  have htrace : WordTrace (prefixWord ++ tailWord_2461336) baseStart_2461336 baseEnd_2461336 := by
    simpa [prefixWord, tailWord_2461336, baseEnd_2461336] using wordTrace_append hprefix tailTrace_2461336
  have hstable : (prefixWord ++ tailWord_2461336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461336).length < 2 ^ (prefixWord ++ tailWord_2461336).sum := by decide
  have hdescent : baseEnd_2461336 < baseStart_2461336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461470 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2461470 : Nat := 118140960795 + 2461470 * 2 ^ 59
def prefixEnd_2461470 : Nat := 4983230072969 + 3 ^ 40 * 2461470 * 2
def baseEnd_2461470 : Nat := 842611484415059814003275

theorem tailTrace_2461470 : CollatzResearch.WordTrace tailWord_2461470 prefixEnd_2461470 842611484415059814003275 := by
  unfold tailWord_2461470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222148299065256306562733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59851457595014700301667909 11222148299065256306562733)
  ·
    refine ⟨4208305612149471114961025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11222148299065256306562733 4208305612149471114961025)
    ·
      refine ⟨3156229209112103336220769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4208305612149471114961025 3156229209112103336220769)
      ·
        refine ⟨2367171906834077502165577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3156229209112103336220769 2367171906834077502165577)
        ·
          refine ⟨1775378930125558126624183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2367171906834077502165577 1775378930125558126624183)
          ·
            refine ⟨2663068395188337189936275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775378930125558126624183 2663068395188337189936275)
            ·
              refine ⟨3994602592782505784904413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663068395188337189936275 3994602592782505784904413)
              ·
                refine ⟨1497975972293439669339155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3994602592782505784904413 1497975972293439669339155)
                ·
                  refine ⟨2246963958440159504008733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497975972293439669339155 2246963958440159504008733)
                  ·
                    refine ⟨842611484415059814003275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246963958440159504008733 842611484415059814003275)
                    ·
                      rfl

theorem cell22_2461470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2461470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461470 prefixEnd_2461470 := by exact prefixLift 2461470
  have htrace : WordTrace (prefixWord ++ tailWord_2461470) baseStart_2461470 baseEnd_2461470 := by
    simpa [prefixWord, tailWord_2461470, baseEnd_2461470] using wordTrace_append hprefix tailTrace_2461470
  have hstable : (prefixWord ++ tailWord_2461470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461470).length < 2 ^ (prefixWord ++ tailWord_2461470).sum := by decide
  have hdescent : baseEnd_2461470 < baseStart_2461470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461473 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2461473 : Nat := 118140960795 + 2461473 * 2 ^ 59
def prefixEnd_2461473 : Nat := 4983230072969 + 3 ^ 40 * 2461473 * 2
def baseEnd_2461473 : Nat := 842612511376368806178265

theorem tailTrace_2461473 : CollatzResearch.WordTrace tailWord_2461473 prefixEnd_2461473 842612511376368806178265 := by
  unfold tailWord_2461473
  simp only [CollatzResearch.WordTrace]
  refine ⟨89777295811511181964861073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59851530541007454643240715 89777295811511181964861073)
  ·
    refine ⟨67332971858633386473645805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89777295811511181964861073 67332971858633386473645805)
    ·
      refine ⟨25249864446987519927617177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67332971858633386473645805 25249864446987519927617177)
      ·
        refine ⟨18937398335240639945712883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25249864446987519927617177 18937398335240639945712883)
        ·
          refine ⟨28406097502860959918569325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18937398335240639945712883 28406097502860959918569325)
          ·
            refine ⟨10652286563572859969463497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28406097502860959918569325 10652286563572859969463497)
            ·
              refine ⟨7989214922679644977097623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10652286563572859969463497 7989214922679644977097623)
              ·
                refine ⟨11983822384019467465646435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7989214922679644977097623 11983822384019467465646435)
                ·
                  refine ⟨17975733576029201198469653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11983822384019467465646435 17975733576029201198469653)
                  ·
                    refine ⟨842612511376368806178265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17975733576029201198469653 842612511376368806178265)
                    ·
                      rfl

theorem cell22_2461473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2461473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461473 prefixEnd_2461473 := by exact prefixLift 2461473
  have htrace : WordTrace (prefixWord ++ tailWord_2461473) baseStart_2461473 baseEnd_2461473 := by
    simpa [prefixWord, tailWord_2461473, baseEnd_2461473] using wordTrace_append hprefix tailTrace_2461473
  have hstable : (prefixWord ++ tailWord_2461473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461473).length < 2 ^ (prefixWord ++ tailWord_2461473).sum := by decide
  have hdescent : baseEnd_2461473 < baseStart_2461473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461477 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 4]
def baseStart_2461477 : Nat := 118140960795 + 2461477 * 2 ^ 59
def prefixEnd_2461477 : Nat := 4983230072969 + 3 ^ 40 * 2461477 * 2
def baseEnd_2461477 : Nat := 280871293552704709692751

theorem tailTrace_2461477 : CollatzResearch.WordTrace tailWord_2461477 prefixEnd_2461477 280871293552704709692751 := by
  unfold tailWord_2461477
  simp only [CollatzResearch.WordTrace]
  refine ⟨89777441703496690648006685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59851627802331127098671123 89777441703496690648006685)
  ·
    refine ⟨33666540638811258993002507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89777441703496690648006685 33666540638811258993002507)
    ·
      refine ⟨50499810958216888489503761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33666540638811258993002507 50499810958216888489503761)
      ·
        refine ⟨37874858218662666367127821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50499810958216888489503761 37874858218662666367127821)
        ·
          refine ⟨14203071831998499887672933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37874858218662666367127821 14203071831998499887672933)
          ·
            refine ⟨2663075968499718728938675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14203071831998499887672933 2663075968499718728938675)
            ·
              refine ⟨3994613952749578093408013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663075968499718728938675 3994613952749578093408013)
              ·
                refine ⟨1497980232281091785028005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3994613952749578093408013 1497980232281091785028005)
                ·
                  refine ⟨280871293552704709692751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497980232281091785028005 280871293552704709692751)
                  ·
                    rfl

theorem cell22_2461477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_2461477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461477 prefixEnd_2461477 := by exact prefixLift 2461477
  have htrace : WordTrace (prefixWord ++ tailWord_2461477) baseStart_2461477 baseEnd_2461477 := by
    simpa [prefixWord, tailWord_2461477, baseEnd_2461477] using wordTrace_append hprefix tailTrace_2461477
  have hstable : (prefixWord ++ tailWord_2461477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461477).length < 2 ^ (prefixWord ++ tailWord_2461477).sum := by decide
  have hdescent : baseEnd_2461477 < baseStart_2461477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461490 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2461490 : Nat := 118140960795 + 2461490 * 2 ^ 59
def prefixEnd_2461490 : Nat := 4983230072969 + 3 ^ 40 * 2461490 * 2
def baseEnd_2461490 : Nat := 842618330823786428503213

theorem tailTrace_2461490 : CollatzResearch.WordTrace tailWord_2461490 prefixEnd_2461490 842618330823786428503213 := by
  unfold tailWord_2461490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22444478963112398467057481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59851943901633062578819949 22444478963112398467057481)
  ·
    refine ⟨16833359222334298850293111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22444478963112398467057481 16833359222334298850293111)
    ·
      refine ⟨25250038833501448275439667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16833359222334298850293111 25250038833501448275439667)
      ·
        refine ⟨37875058250252172413159501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25250038833501448275439667 37875058250252172413159501)
        ·
          refine ⟨14203146843844564654934813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37875058250252172413159501 14203146843844564654934813)
          ·
            refine ⟨5326180066441711745600555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14203146843844564654934813 5326180066441711745600555)
            ·
              refine ⟨7989270099662567618400833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326180066441711745600555 7989270099662567618400833)
              ·
                refine ⟨5991952574746925713800625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7989270099662567618400833 5991952574746925713800625)
                ·
                  refine ⟨4493964431060194285350469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5991952574746925713800625 4493964431060194285350469)
                  ·
                    refine ⟨842618330823786428503213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4493964431060194285350469 842618330823786428503213)
                    ·
                      rfl

theorem cell22_2461490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2461490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461490 prefixEnd_2461490 := by exact prefixLift 2461490
  have htrace : WordTrace (prefixWord ++ tailWord_2461490) baseStart_2461490 baseEnd_2461490 := by
    simpa [prefixWord, tailWord_2461490, baseEnd_2461490] using wordTrace_append hprefix tailTrace_2461490
  have hstable : (prefixWord ++ tailWord_2461490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461490).length < 2 ^ (prefixWord ++ tailWord_2461490).sum := by decide
  have hdescent : baseEnd_2461490 < baseStart_2461490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461492 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2461492 : Nat := 118140960795 + 2461492 * 2 ^ 59
def prefixEnd_2461492 : Nat := 4983230072969 + 3 ^ 40 * 2461492 * 2
def baseEnd_2461492 : Nat := 842619015464659089953207

theorem tailTrace_2461492 : CollatzResearch.WordTrace tailWord_2461492 prefixEnd_2461492 842619015464659089953207 := by
  unfold tailWord_2461492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44888994399221174104901365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59851992532294898806535153 44888994399221174104901365)
  ·
    refine ⟨4208343224926985072334503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44888994399221174104901365 4208343224926985072334503)
    ·
      refine ⟨6312514837390477608501755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208343224926985072334503 6312514837390477608501755)
      ·
        refine ⟨9468772256085716412752633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6312514837390477608501755 9468772256085716412752633)
        ·
          refine ⟨7101579192064287309564475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9468772256085716412752633 7101579192064287309564475)
          ·
            refine ⟨10652368788096430964346713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101579192064287309564475 10652368788096430964346713)
            ·
              refine ⟨7989276591072323223260035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10652368788096430964346713 7989276591072323223260035)
              ·
                refine ⟨11983914886608484834890053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7989276591072323223260035 11983914886608484834890053)
                ·
                  refine ⟨2246984041239090906541885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11983914886608484834890053 2246984041239090906541885)
                  ·
                    refine ⟨842619015464659089953207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246984041239090906541885 842619015464659089953207)
                    ·
                      rfl

theorem cell22_2461492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2461492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461492 prefixEnd_2461492 := by exact prefixLift 2461492
  have htrace : WordTrace (prefixWord ++ tailWord_2461492) baseStart_2461492 baseEnd_2461492 := by
    simpa [prefixWord, tailWord_2461492, baseEnd_2461492] using wordTrace_append hprefix tailTrace_2461492
  have hstable : (prefixWord ++ tailWord_2461492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461492).length < 2 ^ (prefixWord ++ tailWord_2461492).sum := by decide
  have hdescent : baseEnd_2461492 < baseStart_2461492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461537 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 1, 3]
def baseStart_2461537 : Nat := 118140960795 + 2461537 * 2 ^ 59
def prefixEnd_2461537 : Nat := 4983230072969 + 3 ^ 40 * 2461537 * 2
def baseEnd_2461537 : Nat := 842634419884293972578069

theorem tailTrace_2461537 : CollatzResearch.WordTrace tailWord_2461537 prefixEnd_2461537 842634419884293972578069 := by
  unfold tailWord_2461537
  simp only [CollatzResearch.WordTrace]
  refine ⟨89779630083279320895190865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59853086722186213930127243 89779630083279320895190865)
  ·
    refine ⟨67334722562459490671393149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89779630083279320895190865 67334722562459490671393149)
    ·
      refine ⟨25250520960922309001772431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67334722562459490671393149 25250520960922309001772431)
      ·
        refine ⟨37875781441383463502658647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25250520960922309001772431 37875781441383463502658647)
        ·
          refine ⟨56813672162075195253987971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37875781441383463502658647 56813672162075195253987971)
          ·
            refine ⟨85220508243112792880981957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56813672162075195253987971 85220508243112792880981957)
            ·
              refine ⟨15978845295583648665184117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85220508243112792880981957 15978845295583648665184117)
              ·
                refine ⟨1498016746460967062361011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15978845295583648665184117 1498016746460967062361011)
                ·
                  refine ⟨2247025119691450593541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498016746460967062361011 2247025119691450593541517)
                  ·
                    refine ⟨842634419884293972578069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247025119691450593541517 842634419884293972578069)
                    ·
                      rfl

theorem cell22_2461537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_2461537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461537 prefixEnd_2461537 := by exact prefixLift 2461537
  have htrace : WordTrace (prefixWord ++ tailWord_2461537) baseStart_2461537 baseEnd_2461537 := by
    simpa [prefixWord, tailWord_2461537, baseEnd_2461537] using wordTrace_append hprefix tailTrace_2461537
  have hstable : (prefixWord ++ tailWord_2461537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461537).length < 2 ^ (prefixWord ++ tailWord_2461537).sum := by decide
  have hdescent : baseEnd_2461537 < baseStart_2461537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461580 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_2461580 : Nat := 118140960795 + 2461580 * 2 ^ 59
def prefixEnd_2461580 : Nat := 4983230072969 + 3 ^ 40 * 2461580 * 2
def baseEnd_2461580 : Nat := 842649139663056193752937

theorem tailTrace_2461580 : CollatzResearch.WordTrace tailWord_2461580 prefixEnd_2461580 842649139663056193752937 := by
  unfold tailWord_2461580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44890599211061769619503097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59854132281415692826004129 44890599211061769619503097)
  ·
    refine ⟨33667949408296327214627323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44890599211061769619503097 33667949408296327214627323)
    ·
      refine ⟨50501924112444490821940985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33667949408296327214627323 50501924112444490821940985)
      ·
        refine ⟨37876443084333368116455739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50501924112444490821940985 37876443084333368116455739)
        ·
          refine ⟨56814664626500052174683609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37876443084333368116455739 56814664626500052174683609)
          ·
            refine ⟨42610998469875039131012707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56814664626500052174683609 42610998469875039131012707)
            ·
              refine ⟨63916497704812558696519061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42610998469875039131012707 63916497704812558696519061)
              ·
                refine ⟨2996085829913088688899331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63916497704812558696519061 2996085829913088688899331)
                ·
                  refine ⟨4494128744869633033348997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996085829913088688899331 4494128744869633033348997)
                  ·
                    refine ⟨842649139663056193752937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494128744869633033348997 842649139663056193752937)
                    ·
                      rfl

theorem cell22_2461580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_2461580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461580 prefixEnd_2461580 := by exact prefixLift 2461580
  have htrace : WordTrace (prefixWord ++ tailWord_2461580) baseStart_2461580 baseEnd_2461580 := by
    simpa [prefixWord, tailWord_2461580, baseEnd_2461580] using wordTrace_append hprefix tailTrace_2461580
  have hstable : (prefixWord ++ tailWord_2461580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461580).length < 2 ^ (prefixWord ++ tailWord_2461580).sum := by decide
  have hdescent : baseEnd_2461580 < baseStart_2461580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461597 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2461597 : Nat := 118140960795 + 2461597 * 2 ^ 59
def prefixEnd_2461597 : Nat := 4983230072969 + 3 ^ 40 * 2461597 * 2
def baseEnd_2461597 : Nat := 842654959110473816077885

theorem tailTrace_2461597 : CollatzResearch.WordTrace tailWord_2461597 prefixEnd_2461597 842654959110473816077885 := by
  unfold tailWord_2461597
  simp only [CollatzResearch.WordTrace]
  refine ⟨89781818463061951142375045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59854545642041300761583363 89781818463061951142375045)
  ·
    refine ⟨16834090961824115839195321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89781818463061951142375045 16834090961824115839195321)
    ·
      refine ⟨12625568221368086879396491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16834090961824115839195321 12625568221368086879396491)
      ·
        refine ⟨18938352332052130319094737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12625568221368086879396491 18938352332052130319094737)
        ·
          refine ⟨14203764249039097739321053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18938352332052130319094737 14203764249039097739321053)
          ·
            refine ⟨5326411593389661652245395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14203764249039097739321053 5326411593389661652245395)
            ·
              refine ⟨7989617390084492478368093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326411593389661652245395 7989617390084492478368093)
              ·
                refine ⟨2996106521281684679388035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7989617390084492478368093 2996106521281684679388035)
                ·
                  refine ⟨4494159781922527019082053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996106521281684679388035 4494159781922527019082053)
                  ·
                    refine ⟨842654959110473816077885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494159781922527019082053 842654959110473816077885)
                    ·
                      rfl

theorem cell22_2461597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2461597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461597 prefixEnd_2461597 := by exact prefixLift 2461597
  have htrace : WordTrace (prefixWord ++ tailWord_2461597) baseStart_2461597 baseEnd_2461597 := by
    simpa [prefixWord, tailWord_2461597, baseEnd_2461597] using wordTrace_append hprefix tailTrace_2461597
  have hstable : (prefixWord ++ tailWord_2461597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461597).length < 2 ^ (prefixWord ++ tailWord_2461597).sum := by decide
  have hdescent : baseEnd_2461597 < baseStart_2461597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461623 : List Nat := [1, 1, 3, 1, 3, 1, 1, 11]
def baseStart_2461623 : Nat := 118140960795 + 2461623 * 2 ^ 59
def prefixEnd_2461623 : Nat := 4983230072969 + 3 ^ 40 * 2461623 * 2
def baseEnd_2461623 : Nat := 93629317715757601658645

theorem tailTrace_2461623 : CollatzResearch.WordTrace tailWord_2461623 prefixEnd_2461623 93629317715757601658645 := by
  unfold tailWord_2461623
  simp only [CollatzResearch.WordTrace]
  refine ⟨89782766760967757582821523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59855177840645171721881015 89782766760967757582821523)
  ·
    refine ⟨134674150141451636374232285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89782766760967757582821523 134674150141451636374232285)
    ·
      refine ⟨50502806303044363640337107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134674150141451636374232285 50502806303044363640337107)
      ·
        refine ⟨75754209454566545460505661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50502806303044363640337107 75754209454566545460505661)
        ·
          refine ⟨28407828545462454547689623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75754209454566545460505661 28407828545462454547689623)
          ·
            refine ⟨42611742818193681821534435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28407828545462454547689623 42611742818193681821534435)
            ·
              refine ⟨63917614227290522732301653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42611742818193681821534435 63917614227290522732301653)
              ·
                refine ⟨93629317715757601658645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63917614227290522732301653 93629317715757601658645)
                ·
                  rfl

theorem cell22_2461623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 11].length) (baseStart_2461623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461623 prefixEnd_2461623 := by exact prefixLift 2461623
  have htrace : WordTrace (prefixWord ++ tailWord_2461623) baseStart_2461623 baseEnd_2461623 := by
    simpa [prefixWord, tailWord_2461623, baseEnd_2461623] using wordTrace_append hprefix tailTrace_2461623
  have hstable : (prefixWord ++ tailWord_2461623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461623).length < 2 ^ (prefixWord ++ tailWord_2461623).sum := by decide
  have hdescent : baseEnd_2461623 < baseStart_2461623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461640 : List Nat := [2, 1, 3, 1, 4, 2, 1, 8]
def baseStart_2461640 : Nat := 118140960795 + 2461640 * 2 ^ 59
def prefixEnd_2461640 : Nat := 4983230072969 + 3 ^ 40 * 2461640 * 2
def baseEnd_2461640 : Nat := 93629964321026226361417

theorem tailTrace_2461640 : CollatzResearch.WordTrace tailWord_2461640 prefixEnd_2461640 93629964321026226361417 := by
  unfold tailWord_2461640
  simp only [CollatzResearch.WordTrace]
  refine ⟨44891693400953084743095187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59855591201270779657460249 44891693400953084743095187)
  ·
    refine ⟨67337540101429627114642781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44891693400953084743095187 67337540101429627114642781)
    ·
      refine ⟨25251577538036110167991043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67337540101429627114642781 25251577538036110167991043)
      ·
        refine ⟨37877366307054165251986565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25251577538036110167991043 37877366307054165251986565)
        ·
          refine ⟨7102006182572655984747481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37877366307054165251986565 7102006182572655984747481)
          ·
            refine ⟨5326504636929491988560611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7102006182572655984747481 5326504636929491988560611)
            ·
              refine ⟨7989756955394237982840917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326504636929491988560611 7989756955394237982840917)
              ·
                refine ⟨93629964321026226361417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7989756955394237982840917 93629964321026226361417)
                ·
                  rfl

theorem cell22_2461640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_2461640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461640 prefixEnd_2461640 := by exact prefixLift 2461640
  have htrace : WordTrace (prefixWord ++ tailWord_2461640) baseStart_2461640 baseEnd_2461640 := by
    simpa [prefixWord, tailWord_2461640, baseEnd_2461640] using wordTrace_append hprefix tailTrace_2461640
  have hstable : (prefixWord ++ tailWord_2461640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461640).length < 2 ^ (prefixWord ++ tailWord_2461640).sum := by decide
  have hdescent : baseEnd_2461640 < baseStart_2461640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461657 : List Nat := [1, 2, 1, 2, 7, 1, 8]
def baseStart_2461657 : Nat := 118140960795 + 2461657 * 2 ^ 59
def prefixEnd_2461657 : Nat := 4983230072969 + 3 ^ 40 * 2461657 * 2
def baseEnd_2461657 : Nat := 31210203642098283688063

theorem tailTrace_2461657 : CollatzResearch.WordTrace tailWord_2461657 prefixEnd_2461657 31210203642098283688063 := by
  unfold tailWord_2461657
  simp only [CollatzResearch.WordTrace]
  refine ⟨89784006842844581389559225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59856004561896387593039483 89784006842844581389559225)
  ·
    refine ⟨67338005132133436042169419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89784006842844581389559225 67338005132133436042169419)
    ·
      refine ⟨101007007698200154063254129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67338005132133436042169419 101007007698200154063254129)
      ·
        refine ⟨75755255773650115547440597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101007007698200154063254129 75755255773650115547440597)
        ·
          refine ⟨1775513807194924583143139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 75755255773650115547440597 1775513807194924583143139)
          ·
            refine ⟨2663270710792386874714709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775513807194924583143139 2663270710792386874714709)
            ·
              refine ⟨31210203642098283688063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2663270710792386874714709 31210203642098283688063)
              ·
                rfl

theorem cell22_2461657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 8].length) (baseStart_2461657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461657 prefixEnd_2461657 := by exact prefixLift 2461657
  have htrace : WordTrace (prefixWord ++ tailWord_2461657) baseStart_2461657 baseEnd_2461657 := by
    simpa [prefixWord, tailWord_2461657, baseEnd_2461657] using wordTrace_append hprefix tailTrace_2461657
  have hstable : (prefixWord ++ tailWord_2461657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461657).length < 2 ^ (prefixWord ++ tailWord_2461657).sum := by decide
  have hdescent : baseEnd_2461657 < baseStart_2461657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461719 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 5]
def baseStart_2461719 : Nat := 118140960795 + 2461719 * 2 ^ 59
def prefixEnd_2461719 : Nat := 4983230072969 + 3 ^ 40 * 2461719 * 2
def baseEnd_2461719 : Nat := 280898907401235388175837

theorem tailTrace_2461719 : CollatzResearch.WordTrace tailWord_2461719 prefixEnd_2461719 280898907401235388175837 := by
  unfold tailWord_2461719
  simp only [CollatzResearch.WordTrace]
  refine ⟨89786268168619965978316211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59857512112413310652210807 89786268168619965978316211)
  ·
    refine ⟨134679402252929948967474317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89786268168619965978316211 134679402252929948967474317)
    ·
      refine ⟨50504775844848730862802869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134679402252929948967474317 50504775844848730862802869)
      ·
        refine ⟨4734822735454568518387769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50504775844848730862802869 4734822735454568518387769)
        ·
          refine ⟨3551117051590926388790827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4734822735454568518387769 3551117051590926388790827)
          ·
            refine ⟨5326675577386389583186241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551117051590926388790827 5326675577386389583186241)
            ·
              refine ⟨3995006683039792187389681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326675577386389583186241 3995006683039792187389681)
              ·
                refine ⟨2996255012279844140542261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995006683039792187389681 2996255012279844140542261)
                ·
                  refine ⟨280898907401235388175837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2996255012279844140542261 280898907401235388175837)
                  ·
                    rfl

theorem cell22_2461719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 5].length) (baseStart_2461719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461719 prefixEnd_2461719 := by exact prefixLift 2461719
  have htrace : WordTrace (prefixWord ++ tailWord_2461719) baseStart_2461719 baseEnd_2461719 := by
    simpa [prefixWord, tailWord_2461719, baseEnd_2461719] using wordTrace_append hprefix tailTrace_2461719
  have hstable : (prefixWord ++ tailWord_2461719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461719).length < 2 ^ (prefixWord ++ tailWord_2461719).sum := by decide
  have hdescent : baseEnd_2461719 < baseStart_2461719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461766 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2461766 : Nat := 118140960795 + 2461766 * 2 ^ 59
def prefixEnd_2461766 : Nat := 4983230072969 + 3 ^ 40 * 2461766 * 2
def baseEnd_2461766 : Nat := 842712811264213708602367

theorem tailTrace_2461766 : CollatzResearch.WordTrace tailWord_2461766 prefixEnd_2461766 842712811264213708602367 := by
  unfold tailWord_2461766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805874449982802906414911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59858654932966462003518101 2805874449982802906414911)
  ·
    refine ⟨4208811674974204359622367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805874449982802906414911 4208811674974204359622367)
    ·
      refine ⟨6313217512461306539433551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208811674974204359622367 6313217512461306539433551)
      ·
        refine ⟨9469826268691959809150327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6313217512461306539433551 9469826268691959809150327)
        ·
          refine ⟨14204739403037939713725491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9469826268691959809150327 14204739403037939713725491)
          ·
            refine ⟨21307109104556909570588237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14204739403037939713725491 21307109104556909570588237)
            ·
              refine ⟨7990165914208841088970589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21307109104556909570588237 7990165914208841088970589)
              ·
                refine ⟨2996312217828315408363971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7990165914208841088970589 2996312217828315408363971)
                ·
                  refine ⟨4494468326742473112545957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996312217828315408363971 4494468326742473112545957)
                  ·
                    refine ⟨842712811264213708602367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494468326742473112545957 842712811264213708602367)
                    ·
                      rfl

theorem cell22_2461766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2461766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461766 prefixEnd_2461766 := by exact prefixLift 2461766
  have htrace : WordTrace (prefixWord ++ tailWord_2461766) baseStart_2461766 baseEnd_2461766 := by
    simpa [prefixWord, tailWord_2461766, baseEnd_2461766] using wordTrace_append hprefix tailTrace_2461766
  have hstable : (prefixWord ++ tailWord_2461766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461766).length < 2 ^ (prefixWord ++ tailWord_2461766).sum := by decide
  have hdescent : baseEnd_2461766 < baseStart_2461766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461852 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2461852 : Nat := 118140960795 + 2461852 * 2 ^ 59
def prefixEnd_2461852 : Nat := 4983230072969 + 3 ^ 40 * 2461852 * 2
def baseEnd_2461852 : Nat := 842742250821738150952103

theorem tailTrace_2461852 : CollatzResearch.WordTrace tailWord_2461852 prefixEnd_2461852 842742250821738150952103 := by
  unfold tailWord_2461852
  simp only [CollatzResearch.WordTrace]
  refine ⟨44895559538569064846453905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59860746051425419795271873 44895559538569064846453905)
  ·
    refine ⟨33671669653926798634840429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44895559538569064846453905 33671669653926798634840429)
    ·
      refine ⟨12626876120222549488065161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33671669653926798634840429 12626876120222549488065161)
      ·
        refine ⟨9470157090166912116048871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12626876120222549488065161 9470157090166912116048871)
        ·
          refine ⟨14205235635250368174073307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9470157090166912116048871 14205235635250368174073307)
          ·
            refine ⟨21307853452875552261109961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14205235635250368174073307 21307853452875552261109961)
            ·
              refine ⟨15980890089656664195832471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21307853452875552261109961 15980890089656664195832471)
              ·
                refine ⟨23971335134484996293748707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15980890089656664195832471 23971335134484996293748707)
                ·
                  refine ⟨35957002701727494440623061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23971335134484996293748707 35957002701727494440623061)
                  ·
                    refine ⟨842742250821738150952103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35957002701727494440623061 842742250821738150952103)
                    ·
                      rfl

theorem cell22_2461852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2461852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461852 prefixEnd_2461852 := by exact prefixLift 2461852
  have htrace : WordTrace (prefixWord ++ tailWord_2461852) baseStart_2461852 baseEnd_2461852 := by
    simpa [prefixWord, tailWord_2461852, baseEnd_2461852] using wordTrace_append hprefix tailTrace_2461852
  have hstable : (prefixWord ++ tailWord_2461852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461852).length < 2 ^ (prefixWord ++ tailWord_2461852).sum := by decide
  have hdescent : baseEnd_2461852 < baseStart_2461852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461899 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 4]
def baseStart_2461899 : Nat := 118140960795 + 2461899 * 2 ^ 59
def prefixEnd_2461899 : Nat := 4983230072969 + 3 ^ 40 * 2461899 * 2
def baseEnd_2461899 : Nat := 280919446627415231675653

theorem tailTrace_2461899 : CollatzResearch.WordTrace tailWord_2461899 prefixEnd_2461899 280919446627415231675653 := by
  unfold tailWord_2461899
  simp only [CollatzResearch.WordTrace]
  refine ⟨89792833307967856719868751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59861888871978571146579167 89792833307967856719868751)
  ·
    refine ⟨134689249961951785079803127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89792833307967856719868751 134689249961951785079803127)
    ·
      refine ⟨202033874942927677619704691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134689249961951785079803127 202033874942927677619704691)
      ·
        refine ⟨303050812414391516429557037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202033874942927677619704691 303050812414391516429557037)
        ·
          refine ⟨113644054655396818661083889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303050812414391516429557037 113644054655396818661083889)
          ·
            refine ⟨85233040991547613995812917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113644054655396818661083889 85233040991547613995812917)
            ·
              refine ⟨7990597592957588812107461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85233040991547613995812917 7990597592957588812107461)
              ·
                refine ⟨1498237048679547902270149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7990597592957588812107461 1498237048679547902270149)
                ·
                  refine ⟨280919446627415231675653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498237048679547902270149 280919446627415231675653)
                  ·
                    rfl

theorem cell22_2461899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 4].length) (baseStart_2461899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461899 prefixEnd_2461899 := by exact prefixLift 2461899
  have htrace : WordTrace (prefixWord ++ tailWord_2461899) baseStart_2461899 baseEnd_2461899 := by
    simpa [prefixWord, tailWord_2461899, baseEnd_2461899] using wordTrace_append hprefix tailTrace_2461899
  have hstable : (prefixWord ++ tailWord_2461899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461899).length < 2 ^ (prefixWord ++ tailWord_2461899).sum := by decide
  have hdescent : baseEnd_2461899 < baseStart_2461899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461933 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2461933 : Nat := 118140960795 + 2461933 * 2 ^ 59
def prefixEnd_2461933 : Nat := 4983230072969 + 3 ^ 40 * 2461933 * 2
def baseEnd_2461933 : Nat := 280923326259026979892285

theorem tailTrace_2461933 : CollatzResearch.WordTrace tailWord_2461933 prefixEnd_2461933 280923326259026979892285 := by
  unfold tailWord_2461933
  simp only [CollatzResearch.WordTrace]
  refine ⟨89794073389844680526606453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59862715593229787017737635 89794073389844680526606453)
  ·
    refine ⟨8418194380297938799369355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89794073389844680526606453 8418194380297938799369355)
    ·
      refine ⟨12627291570446908199054033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418194380297938799369355 12627291570446908199054033)
      ·
        refine ⟨9470468677835181149290525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12627291570446908199054033 9470468677835181149290525)
        ·
          refine ⟨3551425754188192930983947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9470468677835181149290525 3551425754188192930983947)
          ·
            refine ⟨5327138631282289396475921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551425754188192930983947 5327138631282289396475921)
            ·
              refine ⟨3995353973461717047356941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5327138631282289396475921 3995353973461717047356941)
              ·
                refine ⟨1498257740048143892758853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3995353973461717047356941 1498257740048143892758853)
                ·
                  refine ⟨280923326259026979892285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498257740048143892758853 280923326259026979892285)
                  ·
                    rfl

theorem cell22_2461933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2461933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461933 prefixEnd_2461933 := by exact prefixLift 2461933
  have htrace : WordTrace (prefixWord ++ tailWord_2461933) baseStart_2461933 baseEnd_2461933 := by
    simpa [prefixWord, tailWord_2461933, baseEnd_2461933] using wordTrace_append hprefix tailTrace_2461933
  have hstable : (prefixWord ++ tailWord_2461933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461933).length < 2 ^ (prefixWord ++ tailWord_2461933).sum := by decide
  have hdescent : baseEnd_2461933 < baseStart_2461933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461948 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_2461948 : Nat := 118140960795 + 2461948 * 2 ^ 59
def prefixEnd_2461948 : Nat := 4983230072969 + 3 ^ 40 * 2461948 * 2
def baseEnd_2461948 : Nat := 842775113583625900551809

theorem tailTrace_2461948 : CollatzResearch.WordTrace tailWord_2461948 prefixEnd_2461948 842775113583625900551809 := by
  unfold tailWord_2461948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44897310242395169044201249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59863080323193558725601665 44897310242395169044201249)
  ·
    refine ⟨33672982681796376783150937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44897310242395169044201249 33672982681796376783150937)
    ·
      refine ⟨25254737011347282587363203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33672982681796376783150937 25254737011347282587363203)
      ·
        refine ⟨37882105517020923881044805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25254737011347282587363203 37882105517020923881044805)
        ·
          refine ⟨7102894784441423227695901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37882105517020923881044805 7102894784441423227695901)
          ·
            refine ⟨2663585544165533710385963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7102894784441423227695901 2663585544165533710385963)
            ·
              refine ⟨3995378316248300565578945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663585544165533710385963 3995378316248300565578945)
              ·
                refine ⟨2996533737186225424184209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995378316248300565578945 2996533737186225424184209)
                ·
                  refine ⟨2247400302889669068138157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996533737186225424184209 2247400302889669068138157)
                  ·
                    refine ⟨842775113583625900551809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247400302889669068138157 842775113583625900551809)
                    ·
                      rfl

theorem cell22_2461948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_2461948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461948 prefixEnd_2461948 := by exact prefixLift 2461948
  have htrace : WordTrace (prefixWord ++ tailWord_2461948) baseStart_2461948 baseEnd_2461948 := by
    simpa [prefixWord, tailWord_2461948, baseEnd_2461948] using wordTrace_append hprefix tailTrace_2461948
  have hstable : (prefixWord ++ tailWord_2461948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461948).length < 2 ^ (prefixWord ++ tailWord_2461948).sum := by decide
  have hdescent : baseEnd_2461948 < baseStart_2461948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461957 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_2461957 : Nat := 118140960795 + 2461957 * 2 ^ 59
def prefixEnd_2461957 : Nat := 4983230072969 + 3 ^ 40 * 2461957 * 2
def baseEnd_2461957 : Nat := 842778194467552877076781

theorem tailTrace_2461957 : CollatzResearch.WordTrace tailWord_2461957 prefixEnd_2461957 842778194467552877076781 := by
  unfold tailWord_2461957
  simp only [CollatzResearch.WordTrace]
  refine ⟨89794948741757732625480125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59863299161171821750320083 89794948741757732625480125)
  ·
    refine ⟨33673105778159149734555047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89794948741757732625480125 33673105778159149734555047)
    ·
      refine ⟨50509658667238724601832571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33673105778159149734555047 50509658667238724601832571)
      ·
        refine ⟨75764488000858086902748857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50509658667238724601832571 75764488000858086902748857)
        ·
          refine ⟨56823366000643565177061643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75764488000858086902748857 56823366000643565177061643)
          ·
            refine ⟨85235049000965347765592465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56823366000643565177061643 85235049000965347765592465)
            ·
              refine ⟨63926286750724010824194349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85235049000965347765592465 63926286750724010824194349)
              ·
                refine ⟨23972357531521504059072881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63926286750724010824194349 23972357531521504059072881)
                ·
                  refine ⟨17979268148641128044304661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23972357531521504059072881 17979268148641128044304661)
                  ·
                    refine ⟨842778194467552877076781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17979268148641128044304661 842778194467552877076781)
                    ·
                      rfl

theorem cell22_2461957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_2461957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461957 prefixEnd_2461957 := by exact prefixLift 2461957
  have htrace : WordTrace (prefixWord ++ tailWord_2461957) baseStart_2461957 baseEnd_2461957 := by
    simpa [prefixWord, tailWord_2461957, baseEnd_2461957] using wordTrace_append hprefix tailTrace_2461957
  have hstable : (prefixWord ++ tailWord_2461957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461957).length < 2 ^ (prefixWord ++ tailWord_2461957).sum := by decide
  have hdescent : baseEnd_2461957 < baseStart_2461957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2461978 : List Nat := [3, 1, 1, 3, 5, 1, 2, 6]
def baseStart_2461978 : Nat := 118140960795 + 2461978 * 2 ^ 59
def prefixEnd_2461978 : Nat := 4983230072969 + 3 ^ 40 * 2461978 * 2
def baseEnd_2461978 : Nat := 93642820355190646922413

theorem tailTrace_2461978 : CollatzResearch.WordTrace tailWord_2461978 prefixEnd_2461978 93642820355190646922413 := by
  unfold tailWord_2461978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22448928668670413302998647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59863809783121102141329725 22448928668670413302998647)
  ·
    refine ⟨33673393003005619954497971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22448928668670413302998647 33673393003005619954497971)
    ·
      refine ⟨50510089504508429931746957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33673393003005619954497971 50510089504508429931746957)
      ·
        refine ⟨18941283564190661224405109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50510089504508429931746957 18941283564190661224405109)
        ·
          refine ⟨1775745334142874489787979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18941283564190661224405109 1775745334142874489787979)
          ·
            refine ⟨2663618001214311734681969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775745334142874489787979 2663618001214311734681969)
            ·
              refine ⟨1997713500910733801011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663618001214311734681969 1997713500910733801011477)
              ·
                refine ⟨93642820355190646922413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1997713500910733801011477 93642820355190646922413)
                ·
                  rfl

theorem cell22_2461978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_2461978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2461978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2461978 prefixEnd_2461978 := by exact prefixLift 2461978
  have htrace : WordTrace (prefixWord ++ tailWord_2461978) baseStart_2461978 baseEnd_2461978 := by
    simpa [prefixWord, tailWord_2461978, baseEnd_2461978] using wordTrace_append hprefix tailTrace_2461978
  have hstable : (prefixWord ++ tailWord_2461978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2461978).length < 2 ^ (prefixWord ++ tailWord_2461978).sum := by decide
  have hdescent : baseEnd_2461978 < baseStart_2461978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2461978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462010 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_2462010 : Nat := 118140960795 + 2462010 * 2 ^ 59
def prefixEnd_2462010 : Nat := 4983230072969 + 3 ^ 40 * 2462010 * 2
def baseEnd_2462010 : Nat := 842796337450678405501619

theorem tailTrace_2462010 : CollatzResearch.WordTrace tailWord_2462010 prefixEnd_2462010 842796337450678405501619 := by
  unfold tailWord_2462010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22449220452641430669289871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59864587873710481784772989 22449220452641430669289871)
  ·
    refine ⟨33673830678962146003934807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22449220452641430669289871 33673830678962146003934807)
    ·
      refine ⟨50510746018443219005902211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33673830678962146003934807 50510746018443219005902211)
      ·
        refine ⟨75766119027664828508853317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50510746018443219005902211 75766119027664828508853317)
        ·
          refine ⟨14206147317687155345409997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75766119027664828508853317 14206147317687155345409997)
          ·
            refine ⟨5327305244132683254528749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14206147317687155345409997 5327305244132683254528749)
            ·
              refine ⟨1997739466549756220448281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5327305244132683254528749 1997739466549756220448281)
              ·
                refine ⟨1498304599912317165336211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997739466549756220448281 1498304599912317165336211)
                ·
                  refine ⟨2247456899868475748004317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498304599912317165336211 2247456899868475748004317)
                  ·
                    refine ⟨842796337450678405501619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247456899868475748004317 842796337450678405501619)
                    ·
                      rfl

theorem cell22_2462010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_2462010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462010 prefixEnd_2462010 := by exact prefixLift 2462010
  have htrace : WordTrace (prefixWord ++ tailWord_2462010) baseStart_2462010 baseEnd_2462010 := by
    simpa [prefixWord, tailWord_2462010, baseEnd_2462010] using wordTrace_append hprefix tailTrace_2462010
  have hstable : (prefixWord ++ tailWord_2462010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462010).length < 2 ^ (prefixWord ++ tailWord_2462010).sum := by decide
  have hdescent : baseEnd_2462010 < baseStart_2462010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462034 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_2462034 : Nat := 118140960795 + 2462034 * 2 ^ 59
def prefixEnd_2462034 : Nat := 4983230072969 + 3 ^ 40 * 2462034 * 2
def baseEnd_2462034 : Nat := 280934851047050114300515

theorem tailTrace_2462034 : CollatzResearch.WordTrace tailWord_2462034 prefixEnd_2462034 280934851047050114300515 := by
  unfold tailWord_2462034
  simp only [CollatzResearch.WordTrace]
  refine ⟨22449439290619693694008289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59865171441652516517355437 22449439290619693694008289)
  ·
    refine ⟨16837079467964770270506217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22449439290619693694008289 16837079467964770270506217)
    ·
      refine ⟨12627809600973577702879663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16837079467964770270506217 12627809600973577702879663)
      ·
        refine ⟨18941714401460366554319495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12627809600973577702879663 18941714401460366554319495)
        ·
          refine ⟨28412571602190549831479243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18941714401460366554319495 28412571602190549831479243)
          ·
            refine ⟨42618857403285824747218865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28412571602190549831479243 42618857403285824747218865)
            ·
              refine ⟨31964143052464368560414149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42618857403285824747218865 31964143052464368560414149)
              ·
                refine ⟨5993276822337069105077653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31964143052464368560414149 5993276822337069105077653)
                ·
                  refine ⟨280934851047050114300515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5993276822337069105077653 280934851047050114300515)
                  ·
                    rfl

theorem cell22_2462034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_2462034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462034 prefixEnd_2462034 := by exact prefixLift 2462034
  have htrace : WordTrace (prefixWord ++ tailWord_2462034) baseStart_2462034 baseEnd_2462034 := by
    simpa [prefixWord, tailWord_2462034, baseEnd_2462034] using wordTrace_append hprefix tailTrace_2462034
  have hstable : (prefixWord ++ tailWord_2462034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462034).length < 2 ^ (prefixWord ++ tailWord_2462034).sum := by decide
  have hdescent : baseEnd_2462034 < baseStart_2462034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462036 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2462036 : Nat := 118140960795 + 2462036 * 2 ^ 59
def prefixEnd_2462036 : Nat := 4983230072969 + 3 ^ 40 * 2462036 * 2
def baseEnd_2462036 : Nat := 842805237782023004351539

theorem tailTrace_2462036 : CollatzResearch.WordTrace tailWord_2462036 prefixEnd_2462036 842805237782023004351539 := by
  unfold tailWord_2462036
  simp only [CollatzResearch.WordTrace]
  refine ⟨44898915054235764558802981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59865220072314352745070641 44898915054235764558802981)
  ·
    refine ⟨8418546572669205854775559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44898915054235764558802981 8418546572669205854775559)
    ·
      refine ⟨12627819859003808782163339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418546572669205854775559 12627819859003808782163339)
      ·
        refine ⟨18941729788505713173245009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12627819859003808782163339 18941729788505713173245009)
        ·
          refine ⟨14206297341379284879933757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18941729788505713173245009 14206297341379284879933757)
          ·
            refine ⟨5327361503017231829975159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14206297341379284879933757 5327361503017231829975159)
            ·
              refine ⟨7991042254525847744962739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327361503017231829975159 7991042254525847744962739)
              ·
                refine ⟨11986563381788771617444109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7991042254525847744962739 11986563381788771617444109)
                ·
                  refine ⟨4494961268170789356541541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11986563381788771617444109 4494961268170789356541541)
                  ·
                    refine ⟨842805237782023004351539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494961268170789356541541 842805237782023004351539)
                    ·
                      rfl

theorem cell22_2462036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2462036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462036 prefixEnd_2462036 := by exact prefixLift 2462036
  have htrace : WordTrace (prefixWord ++ tailWord_2462036) baseStart_2462036 baseEnd_2462036 := by
    simpa [prefixWord, tailWord_2462036, baseEnd_2462036] using wordTrace_append hprefix tailTrace_2462036
  have hstable : (prefixWord ++ tailWord_2462036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462036).length < 2 ^ (prefixWord ++ tailWord_2462036).sum := by decide
  have hdescent : baseEnd_2462036 < baseStart_2462036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462051 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 4]
def baseStart_2462051 : Nat := 118140960795 + 2462051 * 2 ^ 59
def prefixEnd_2462051 : Nat := 4983230072969 + 3 ^ 40 * 2462051 * 2
def baseEnd_2462051 : Nat := 280936790862855988408831

theorem tailTrace_2462051 : CollatzResearch.WordTrace tailWord_2462051 prefixEnd_2462051 280936790862855988408831 := by
  unfold tailWord_2462051
  simp only [CollatzResearch.WordTrace]
  refine ⟨89798377203417186679402007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59865584802278124452934671 89798377203417186679402007)
  ·
    refine ⟨134697565805125780019103011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89798377203417186679402007 134697565805125780019103011)
    ·
      refine ⟨202046348707688670028654517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134697565805125780019103011 202046348707688670028654517)
      ·
        refine ⟨18941845191345812815186361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202046348707688670028654517 18941845191345812815186361)
        ·
          refine ⟨14206383893509359611389771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18941845191345812815186361 14206383893509359611389771)
          ·
            refine ⟨21309575840264039417084657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14206383893509359611389771 21309575840264039417084657)
            ·
              refine ⟨15982181880198029562813493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21309575840264039417084657 15982181880198029562813493)
              ·
                refine ⟨1498329551268565271513765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15982181880198029562813493 1498329551268565271513765)
                ·
                  refine ⟨280936790862855988408831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498329551268565271513765 280936790862855988408831)
                  ·
                    rfl

theorem cell22_2462051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 4].length) (baseStart_2462051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462051 prefixEnd_2462051 := by exact prefixLift 2462051
  have htrace : WordTrace (prefixWord ++ tailWord_2462051) baseStart_2462051 baseEnd_2462051 := by
    simpa [prefixWord, tailWord_2462051, baseEnd_2462051] using wordTrace_append hprefix tailTrace_2462051
  have hstable : (prefixWord ++ tailWord_2462051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462051).length < 2 ^ (prefixWord ++ tailWord_2462051).sum := by decide
  have hdescent : baseEnd_2462051 < baseStart_2462051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462053 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_2462053 : Nat := 118140960795 + 2462053 * 2 ^ 59
def prefixEnd_2462053 : Nat := 4983230072969 + 3 ^ 40 * 2462053 * 2
def baseEnd_2462053 : Nat := 842811057229440626676487

theorem tailTrace_2462053 : CollatzResearch.WordTrace tailWord_2462053 prefixEnd_2462053 842811057229440626676487 := by
  unfold tailWord_2462053
  simp only [CollatzResearch.WordTrace]
  refine ⟨89798450149409941020974813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59865633432939960680649875 89798450149409941020974813)
  ·
    refine ⟨33674418806028727882865555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89798450149409941020974813 33674418806028727882865555)
    ·
      refine ⟨50511628209043091824298333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33674418806028727882865555 50511628209043091824298333)
      ·
        refine ⟨18941860578391159434111875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50511628209043091824298333 18941860578391159434111875)
        ·
          refine ⟨28412790867586739151167813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18941860578391159434111875 28412790867586739151167813)
          ·
            refine ⟨5327398287672513590843965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28412790867586739151167813 5327398287672513590843965)
            ·
              refine ⟨1997774357877192596566487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5327398287672513590843965 1997774357877192596566487)
              ·
                refine ⟨2996661536815788894849731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997774357877192596566487 2996661536815788894849731)
                ·
                  refine ⟨4494992305223683342274597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996661536815788894849731 4494992305223683342274597)
                  ·
                    refine ⟨842811057229440626676487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494992305223683342274597 842811057229440626676487)
                    ·
                      rfl

theorem cell22_2462053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_2462053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462053 prefixEnd_2462053 := by exact prefixLift 2462053
  have htrace : WordTrace (prefixWord ++ tailWord_2462053) baseStart_2462053 baseEnd_2462053 := by
    simpa [prefixWord, tailWord_2462053, baseEnd_2462053] using wordTrace_append hprefix tailTrace_2462053
  have hstable : (prefixWord ++ tailWord_2462053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462053).length < 2 ^ (prefixWord ++ tailWord_2462053).sum := by decide
  have hdescent : baseEnd_2462053 < baseStart_2462053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462111 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 5, 3]
def baseStart_2462111 : Nat := 118140960795 + 2462111 * 2 ^ 59
def prefixEnd_2462111 : Nat := 4983230072969 + 3 ^ 40 * 2462111 * 2
def baseEnd_2462111 : Nat := 842830911814747808726309

theorem tailTrace_2462111 : CollatzResearch.WordTrace tailWord_2462111 prefixEnd_2462111 842830911814747808726309 := by
  unfold tailWord_2462111
  simp only [CollatzResearch.WordTrace]
  refine ⟨89800565583199816926586187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59867043722133211284390791 89800565583199816926586187)
  ·
    refine ⟨134700848374799725389879281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89800565583199816926586187 134700848374799725389879281)
    ·
      refine ⟨101025636281099794042409461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134700848374799725389879281 101025636281099794042409461)
      ·
        refine ⟨9471153401353105691475887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101025636281099794042409461 9471153401353105691475887)
        ·
          refine ⟨14206730102029658537213831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9471153401353105691475887 14206730102029658537213831)
          ·
            refine ⟨21310095153044487805820747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14206730102029658537213831 21310095153044487805820747)
            ·
              refine ⟨31965142729566731708731121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21310095153044487805820747 31965142729566731708731121)
              ·
                refine ⟨23973857047175048781548341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31965142729566731708731121 23973857047175048781548341)
                ·
                  refine ⟨2247549098172660823270157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23973857047175048781548341 2247549098172660823270157)
                  ·
                    refine ⟨842830911814747808726309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247549098172660823270157 842830911814747808726309)
                    ·
                      rfl

theorem cell22_2462111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_2462111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462111 prefixEnd_2462111 := by exact prefixLift 2462111
  have htrace : WordTrace (prefixWord ++ tailWord_2462111) baseStart_2462111 baseEnd_2462111 := by
    simpa [prefixWord, tailWord_2462111, baseEnd_2462111] using wordTrace_append hprefix tailTrace_2462111
  have hstable : (prefixWord ++ tailWord_2462111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462111).length < 2 ^ (prefixWord ++ tailWord_2462111).sum := by decide
  have hdescent : baseEnd_2462111 < baseStart_2462111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462231 : List Nat := [1, 1, 3, 6, 11]
def baseStart_2462231 : Nat := 118140960795 + 2462231 * 2 ^ 59
def prefixEnd_2462231 : Nat := 4983230072969 + 3 ^ 40 * 2462231 * 2
def baseEnd_2462231 : Nat := 3468609013444886813687

theorem tailTrace_2462231 : CollatzResearch.WordTrace tailWord_2462231 prefixEnd_2462231 3468609013444886813687 := by
  unfold tailWord_2462231
  simp only [CollatzResearch.WordTrace]
  refine ⟨89804942342765077420954547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59869961561843384947303031 89804942342765077420954547)
  ·
    refine ⟨134707413514147616131431821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89804942342765077420954547 134707413514147616131431821)
    ·
      refine ⟨50515280067805356049286933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134707413514147616131431821 50515280067805356049286933)
      ·
        refine ⟨2367903753178376064810325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50515280067805356049286933 2367903753178376064810325)
        ·
          refine ⟨3468609013444886813687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2367903753178376064810325 3468609013444886813687)
          ·
            rfl

theorem cell22_2462231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 11].length) (baseStart_2462231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462231 prefixEnd_2462231 := by exact prefixLift 2462231
  have htrace : WordTrace (prefixWord ++ tailWord_2462231) baseStart_2462231 baseEnd_2462231 := by
    simpa [prefixWord, tailWord_2462231, baseEnd_2462231] using wordTrace_append hprefix tailTrace_2462231
  have hstable : (prefixWord ++ tailWord_2462231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462231).length < 2 ^ (prefixWord ++ tailWord_2462231).sum := by decide
  have hdescent : baseEnd_2462231 < baseStart_2462231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462237 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 4]
def baseStart_2462237 : Nat := 118140960795 + 2462237 * 2 ^ 59
def prefixEnd_2462237 : Nat := 4983230072969 + 3 ^ 40 * 2462237 * 2
def baseEnd_2462237 : Nat := 280958014729908493358641

theorem tailTrace_2462237 : CollatzResearch.WordTrace tailWord_2462237 prefixEnd_2462237 280958014729908493358641 := by
  unfold tailWord_2462237
  simp only [CollatzResearch.WordTrace]
  refine ⟨89805161180743340445672965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59870107453828893630448643 89805161180743340445672965)
  ·
    refine ⟨16838467721389376333563681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89805161180743340445672965 16838467721389376333563681)
    ·
      refine ⟨12628850791042032250172761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16838467721389376333563681 12628850791042032250172761)
      ·
        refine ⟨9471638093281524187629571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12628850791042032250172761 9471638093281524187629571)
        ·
          refine ⟨14207457139922286281444357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9471638093281524187629571 14207457139922286281444357)
          ·
            refine ⟨2663898213735428677770817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14207457139922286281444357 2663898213735428677770817)
            ·
              refine ⟨1997923660301571508328113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663898213735428677770817 1997923660301571508328113)
              ·
                refine ⟨1498442745226178631246085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997923660301571508328113 1498442745226178631246085)
                ·
                  refine ⟨280958014729908493358641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498442745226178631246085 280958014729908493358641)
                  ·
                    rfl

theorem cell22_2462237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_2462237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462237 prefixEnd_2462237 := by exact prefixLift 2462237
  have htrace : WordTrace (prefixWord ++ tailWord_2462237) baseStart_2462237 baseEnd_2462237 := by
    simpa [prefixWord, tailWord_2462237, baseEnd_2462237] using wordTrace_append hprefix tailTrace_2462237
  have hstable : (prefixWord ++ tailWord_2462237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462237).length < 2 ^ (prefixWord ++ tailWord_2462237).sum := by decide
  have hdescent : baseEnd_2462237 < baseStart_2462237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462248 : List Nat := [2, 1, 5, 2, 1, 1, 3, 7]
def baseStart_2462248 : Nat := 118140960795 + 2462248 * 2 ^ 59
def prefixEnd_2462248 : Nat := 4983230072969 + 3 ^ 40 * 2462248 * 2
def baseEnd_2462248 : Nat := 93653089968280568672321

theorem tailTrace_2462248 : CollatzResearch.WordTrace tailWord_2462248 prefixEnd_2462248 93653089968280568672321 := by
  unfold tailWord_2462248
  simp only [CollatzResearch.WordTrace]
  refine ⟨44902781191851744662161699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59870374922468992882882265 44902781191851744662161699)
  ·
    refine ⟨67354171787777616993242549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44902781191851744662161699 67354171787777616993242549)
    ·
      refine ⟨6314453605104151593116489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67354171787777616993242549 6314453605104151593116489)
      ·
        refine ⟨4735840203828113694837367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6314453605104151593116489 4735840203828113694837367)
        ·
          refine ⟨7103760305742170542256051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735840203828113694837367 7103760305742170542256051)
          ·
            refine ⟨10655640458613255813384077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7103760305742170542256051 10655640458613255813384077)
            ·
              refine ⟨3995865171979970930019029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10655640458613255813384077 3995865171979970930019029)
              ·
                refine ⟨93653089968280568672321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3995865171979970930019029 93653089968280568672321)
                ·
                  rfl

theorem cell22_2462248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_2462248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462248 prefixEnd_2462248 := by exact prefixLift 2462248
  have htrace : WordTrace (prefixWord ++ tailWord_2462248) baseStart_2462248 baseEnd_2462248 := by
    simpa [prefixWord, tailWord_2462248, baseEnd_2462248] using wordTrace_append hprefix tailTrace_2462248
  have hstable : (prefixWord ++ tailWord_2462248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462248).length < 2 ^ (prefixWord ++ tailWord_2462248).sum := by decide
  have hdescent : baseEnd_2462248 < baseStart_2462248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462261 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2462261 : Nat := 118140960795 + 2462261 * 2 ^ 59
def prefixEnd_2462261 : Nat := 4983230072969 + 3 ^ 40 * 2462261 * 2
def baseEnd_2462261 : Nat := 842882259880197417475849

theorem tailTrace_2462261 : CollatzResearch.WordTrace tailWord_2462261 prefixEnd_2462261 842882259880197417475849 := by
  unfold tailWord_2462261
  simp only [CollatzResearch.WordTrace]
  refine ⟨89806036532656392544546637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59870691021770928363031091 89806036532656392544546637)
  ·
    refine ⟨33677263699746147204204989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89806036532656392544546637 33677263699746147204204989)
    ·
      refine ⟨12628973887404805201576871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33677263699746147204204989 12628973887404805201576871)
      ·
        refine ⟨18943460831107207802365307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12628973887404805201576871 18943460831107207802365307)
        ·
          refine ⟨28415191246660811703547961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18943460831107207802365307 28415191246660811703547961)
          ·
            refine ⟨21311393434995608777660971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28415191246660811703547961 21311393434995608777660971)
            ·
              refine ⟨31967090152493413166491457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21311393434995608777660971 31967090152493413166491457)
              ·
                refine ⟨23975317614370059874868593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31967090152493413166491457 23975317614370059874868593)
                ·
                  refine ⟨17981488210777544906151445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23975317614370059874868593 17981488210777544906151445)
                  ·
                    refine ⟨842882259880197417475849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17981488210777544906151445 842882259880197417475849)
                    ·
                      rfl

theorem cell22_2462261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2462261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462261 prefixEnd_2462261 := by exact prefixLift 2462261
  have htrace : WordTrace (prefixWord ++ tailWord_2462261) baseStart_2462261 baseEnd_2462261 := by
    simpa [prefixWord, tailWord_2462261, baseEnd_2462261] using wordTrace_append hprefix tailTrace_2462261
  have hstable : (prefixWord ++ tailWord_2462261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462261).length < 2 ^ (prefixWord ++ tailWord_2462261).sum := by decide
  have hdescent : baseEnd_2462261 < baseStart_2462261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462263 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 3, 3]
def baseStart_2462263 : Nat := 118140960795 + 2462263 * 2 ^ 59
def prefixEnd_2462263 : Nat := 4983230072969 + 3 ^ 40 * 2462263 * 2
def baseEnd_2462263 : Nat := 842882944521070078925843

theorem tailTrace_2462263 : CollatzResearch.WordTrace tailWord_2462263 prefixEnd_2462263 842882944521070078925843 := by
  unfold tailWord_2462263
  simp only [CollatzResearch.WordTrace]
  refine ⟨89806109478649146886119443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59870739652432764590746295 89806109478649146886119443)
  ·
    refine ⟨134709164217973720329179165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89806109478649146886119443 134709164217973720329179165)
    ·
      refine ⟨50515936581740145123442187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134709164217973720329179165 50515936581740145123442187)
      ·
        refine ⟨75773904872610217685163281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50515936581740145123442187 75773904872610217685163281)
        ·
          refine ⟨56830428654457663263872461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75773904872610217685163281 56830428654457663263872461)
          ·
            refine ⟨21311410745421623723952173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56830428654457663263872461 21311410745421623723952173)
            ·
              refine ⟨7991779029533108896482065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21311410745421623723952173 7991779029533108896482065)
              ·
                refine ⟨5993834272149831672361549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7991779029533108896482065 5993834272149831672361549)
                ·
                  refine ⟨2247687852056186877135581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5993834272149831672361549 2247687852056186877135581)
                  ·
                    refine ⟨842882944521070078925843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247687852056186877135581 842882944521070078925843)
                    ·
                      rfl

theorem cell22_2462263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_2462263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462263 prefixEnd_2462263 := by exact prefixLift 2462263
  have htrace : WordTrace (prefixWord ++ tailWord_2462263) baseStart_2462263 baseEnd_2462263 := by
    simpa [prefixWord, tailWord_2462263, baseEnd_2462263] using wordTrace_append hprefix tailTrace_2462263
  have hstable : (prefixWord ++ tailWord_2462263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462263).length < 2 ^ (prefixWord ++ tailWord_2462263).sum := by decide
  have hdescent : baseEnd_2462263 < baseStart_2462263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462293 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 5]
def baseStart_2462293 : Nat := 118140960795 + 2462293 * 2 ^ 59
def prefixEnd_2462293 : Nat := 4983230072969 + 3 ^ 40 * 2462293 * 2
def baseEnd_2462293 : Nat := 280964404711386666891917

theorem tailTrace_2462293 : CollatzResearch.WordTrace tailWord_2462293 prefixEnd_2462293 280964404711386666891917 := by
  unfold tailWord_2462293
  simp only [CollatzResearch.WordTrace]
  refine ⟨89807203668540462009711533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59871469112360308006474355 89807203668540462009711533)
  ·
    refine ⟨33677701375702673253641825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89807203668540462009711533 33677701375702673253641825)
    ·
      refine ⟨25258276031777004940231369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33677701375702673253641825 25258276031777004940231369)
      ·
        refine ⟨18943707023832753705173527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25258276031777004940231369 18943707023832753705173527)
        ·
          refine ⟨28415560535749130557760291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18943707023832753705173527 28415560535749130557760291)
          ·
            refine ⟨42623340803623695836640437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28415560535749130557760291 42623340803623695836640437)
            ·
              refine ⟨3995938200339721484685041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42623340803623695836640437 3995938200339721484685041)
              ·
                refine ⟨2996953650254791113513781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995938200339721484685041 2996953650254791113513781)
                ·
                  refine ⟨280964404711386666891917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2996953650254791113513781 280964404711386666891917)
                  ·
                    rfl

theorem cell22_2462293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_2462293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462293 prefixEnd_2462293 := by exact prefixLift 2462293
  have htrace : WordTrace (prefixWord ++ tailWord_2462293) baseStart_2462293 baseEnd_2462293 := by
    simpa [prefixWord, tailWord_2462293, baseEnd_2462293] using wordTrace_append hprefix tailTrace_2462293
  have hstable : (prefixWord ++ tailWord_2462293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462293).length < 2 ^ (prefixWord ++ tailWord_2462293).sum := by decide
  have hdescent : baseEnd_2462293 < baseStart_2462293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462340 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2462340 : Nat := 118140960795 + 2462340 * 2 ^ 59
def prefixEnd_2462340 : Nat := 4983230072969 + 3 ^ 40 * 2462340 * 2
def baseEnd_2462340 : Nat := 842909303194667544750607

theorem tailTrace_2462340 : CollatzResearch.WordTrace tailWord_2462340 prefixEnd_2462340 842909303194667544750607 := by
  unfold tailWord_2462340
  simp only [CollatzResearch.WordTrace]
  refine ⟨44904458949685094518336237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59872611932913459357781649 44904458949685094518336237)
  ·
    refine ⟨16839172106131910444376089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44904458949685094518336237 16839172106131910444376089)
    ·
      refine ⟨12629379079598932833282067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16839172106131910444376089 12629379079598932833282067)
      ·
        refine ⟨18944068619398399249923101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12629379079598932833282067 18944068619398399249923101)
        ·
          refine ⟨7104025732274399718721163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18944068619398399249923101 7104025732274399718721163)
          ·
            refine ⟨10656038598411599578081745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104025732274399718721163 10656038598411599578081745)
            ·
              refine ⟨7992028948808699683561309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10656038598411599578081745 7992028948808699683561309)
              ·
                refine ⟨2997010855803262381335491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7992028948808699683561309 2997010855803262381335491)
                ·
                  refine ⟨4495516283704893572003237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997010855803262381335491 4495516283704893572003237)
                  ·
                    refine ⟨842909303194667544750607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4495516283704893572003237 842909303194667544750607)
                    ·
                      rfl

theorem cell22_2462340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2462340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462340 prefixEnd_2462340 := by exact prefixLift 2462340
  have htrace : WordTrace (prefixWord ++ tailWord_2462340) baseStart_2462340 baseEnd_2462340 := by
    simpa [prefixWord, tailWord_2462340, baseEnd_2462340] using wordTrace_append hprefix tailTrace_2462340
  have hstable : (prefixWord ++ tailWord_2462340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462340).length < 2 ^ (prefixWord ++ tailWord_2462340).sum := by decide
  have hdescent : baseEnd_2462340 < baseStart_2462340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462406 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2462406 : Nat := 118140960795 + 2462406 * 2 ^ 59
def prefixEnd_2462406 : Nat := 4983230072969 + 3 ^ 40 * 2462406 * 2
def baseEnd_2462406 : Nat := 280977298781155124200135

theorem tailTrace_2462406 : CollatzResearch.WordTrace tailWord_2462406 prefixEnd_2462406 280977298781155124200135 := by
  unfold tailWord_2462406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806603909910346322142971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59874216744754054872383381 2806603909910346322142971)
  ·
    refine ⟨4209905864865519483214457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2806603909910346322142971 4209905864865519483214457)
    ·
      refine ⟨3157429398649139612410843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4209905864865519483214457 3157429398649139612410843)
      ·
        refine ⟨4736144097973709418616265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3157429398649139612410843 4736144097973709418616265)
        ·
          refine ⟨3552108073480282063962199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4736144097973709418616265 3552108073480282063962199)
          ·
            refine ⟨5328162110220423095943299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552108073480282063962199 5328162110220423095943299)
            ·
              refine ⟨7992243165330634643914949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328162110220423095943299 7992243165330634643914949)
              ·
                refine ⟨1498545593499493995734053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7992243165330634643914949 1498545593499493995734053)
                ·
                  refine ⟨280977298781155124200135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498545593499493995734053 280977298781155124200135)
                  ·
                    rfl

theorem cell22_2462406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2462406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462406 prefixEnd_2462406 := by exact prefixLift 2462406
  have htrace : WordTrace (prefixWord ++ tailWord_2462406) baseStart_2462406 baseEnd_2462406 := by
    simpa [prefixWord, tailWord_2462406, baseEnd_2462406] using wordTrace_append hprefix tailTrace_2462406
  have hstable : (prefixWord ++ tailWord_2462406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462406).length < 2 ^ (prefixWord ++ tailWord_2462406).sum := by decide
  have hdescent : baseEnd_2462406 < baseStart_2462406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462462 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2462462 : Nat := 118140960795 + 2462462 * 2 ^ 59
def prefixEnd_2462462 : Nat := 4983230072969 + 3 ^ 40 * 2462462 * 2
def baseEnd_2462462 : Nat := 280983688762633297733411

theorem tailTrace_2462462 : CollatzResearch.WordTrace tailWord_2462462 prefixEnd_2462462 280983688762633297733411 := by
  unfold tailWord_2462462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226670950616025484076705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59875578403285469248409093 11226670950616025484076705)
  ·
    refine ⟨8420003212962019113057529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11226670950616025484076705 8420003212962019113057529)
    ·
      refine ⟨6315002409721514334793147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8420003212962019113057529 6315002409721514334793147)
      ·
        refine ⟨9472503614582271502189721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315002409721514334793147 9472503614582271502189721)
        ·
          refine ⟨7104377710936703626642291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472503614582271502189721 7104377710936703626642291)
          ·
            refine ⟨10656566566405055439963437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104377710936703626642291 10656566566405055439963437)
            ·
              refine ⟨3996212462401895789986289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10656566566405055439963437 3996212462401895789986289)
              ·
                refine ⟨2997159346801421842489717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996212462401895789986289 2997159346801421842489717)
                ·
                  refine ⟨280983688762633297733411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2997159346801421842489717 280983688762633297733411)
                  ·
                    rfl

theorem cell22_2462462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2462462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462462 prefixEnd_2462462 := by exact prefixLift 2462462
  have htrace : WordTrace (prefixWord ++ tailWord_2462462) baseStart_2462462 baseEnd_2462462 := by
    simpa [prefixWord, tailWord_2462462, baseEnd_2462462] using wordTrace_append hprefix tailTrace_2462462
  have hstable : (prefixWord ++ tailWord_2462462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462462).length < 2 ^ (prefixWord ++ tailWord_2462462).sum := by decide
  have hdescent : baseEnd_2462462 < baseStart_2462462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462473 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 6]
def baseStart_2462473 : Nat := 118140960795 + 2462473 * 2 ^ 59
def prefixEnd_2462473 : Nat := 4983230072969 + 3 ^ 40 * 2462473 * 2
def baseEnd_2462473 : Nat := 280984943937566510391733

theorem tailTrace_2462473 : CollatzResearch.WordTrace tailWord_2462473 prefixEnd_2462473 280984943937566510391733 := by
  unfold tailWord_2462473
  simp only [CollatzResearch.WordTrace]
  refine ⟨89813768807888352751264073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59875845871925568500842715 89813768807888352751264073)
  ·
    refine ⟨67360326605916264563448055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89813768807888352751264073 67360326605916264563448055)
    ·
      refine ⟨101040489908874396845172083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67360326605916264563448055 101040489908874396845172083)
      ·
        refine ⟨151560734863311595267758125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101040489908874396845172083 151560734863311595267758125)
        ·
          refine ⟨56835275573741848225409297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151560734863311595267758125 56835275573741848225409297)
          ·
            refine ⟨42626456680306386169056973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56835275573741848225409297 42626456680306386169056973)
            ·
              refine ⟨15984921255114894813396365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42626456680306386169056973 15984921255114894813396365)
              ·
                refine ⟨5994345470668085555023637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15984921255114894813396365 5994345470668085555023637)
                ·
                  refine ⟨280984943937566510391733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5994345470668085555023637 280984943937566510391733)
                  ·
                    rfl

theorem cell22_2462473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_2462473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462473 prefixEnd_2462473 := by exact prefixLift 2462473
  have htrace : WordTrace (prefixWord ++ tailWord_2462473) baseStart_2462473 baseEnd_2462473 := by
    simpa [prefixWord, tailWord_2462473, baseEnd_2462473] using wordTrace_append hprefix tailTrace_2462473
  have hstable : (prefixWord ++ tailWord_2462473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462473).length < 2 ^ (prefixWord ++ tailWord_2462473).sum := by decide
  have hdescent : baseEnd_2462473 < baseStart_2462473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462492 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2462492 : Nat := 118140960795 + 2462492 * 2 ^ 59
def prefixEnd_2462492 : Nat := 4983230072969 + 3 ^ 40 * 2462492 * 2
def baseEnd_2462492 : Nat := 842961335900989814950141

theorem tailTrace_2462492 : CollatzResearch.WordTrace tailWord_2462492 prefixEnd_2462492 842961335900989814950141 := by
  unfold tailWord_2462492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44907230897409759498102865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59876307863213012664137153 44907230897409759498102865)
  ·
    refine ⟨33680423173057319623577149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44907230897409759498102865 33680423173057319623577149)
    ·
      refine ⟨12630158689896494858841431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33680423173057319623577149 12630158689896494858841431)
      ·
        refine ⟨18945238034844742288262147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12630158689896494858841431 18945238034844742288262147)
        ·
          refine ⟨28417857052267113432393221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18945238034844742288262147 28417857052267113432393221)
          ·
            refine ⟨5328348197300083768573729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28417857052267113432393221 5328348197300083768573729)
            ·
              refine ⟨3996261147975062826430297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5328348197300083768573729 3996261147975062826430297)
              ·
                refine ⟨2997195860981297119822723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996261147975062826430297 2997195860981297119822723)
                ·
                  refine ⟨4495793791471945679734085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997195860981297119822723 4495793791471945679734085)
                  ·
                    refine ⟨842961335900989814950141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4495793791471945679734085 842961335900989814950141)
                    ·
                      rfl

theorem cell22_2462492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2462492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462492 prefixEnd_2462492 := by exact prefixLift 2462492
  have htrace : WordTrace (prefixWord ++ tailWord_2462492) baseStart_2462492 baseEnd_2462492 := by
    simpa [prefixWord, tailWord_2462492, baseEnd_2462492] using wordTrace_append hprefix tailTrace_2462492
  have hstable : (prefixWord ++ tailWord_2462492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462492).length < 2 ^ (prefixWord ++ tailWord_2462492).sum := by decide
  have hdescent : baseEnd_2462492 < baseStart_2462492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462520 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_2462520 : Nat := 118140960795 + 2462520 * 2 ^ 59
def prefixEnd_2462520 : Nat := 4983230072969 + 3 ^ 40 * 2462520 * 2
def baseEnd_2462520 : Nat := 842970920873207075250055

theorem tailTrace_2462520 : CollatzResearch.WordTrace tailWord_2462520 prefixEnd_2462520 842970920873207075250055 := by
  unfold tailWord_2462520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44907741519359039889112507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59876988692478719852150009 44907741519359039889112507)
  ·
    refine ⟨67361612279038559833668761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44907741519359039889112507 67361612279038559833668761)
    ·
      refine ⟨50521209209278919875251571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67361612279038559833668761 50521209209278919875251571)
      ·
        refine ⟨75781813813918379812877357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50521209209278919875251571 75781813813918379812877357)
        ·
          refine ⟨28418180180219392429829009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75781813813918379812877357 28418180180219392429829009)
          ·
            refine ⟨21313635135164544322371757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28418180180219392429829009 21313635135164544322371757)
            ·
              refine ⟨7992613175686704120889409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21313635135164544322371757 7992613175686704120889409)
              ·
                refine ⟨5994459881765028090667057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7992613175686704120889409 5994459881765028090667057)
                ·
                  refine ⟨4495844911323771068000293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994459881765028090667057 4495844911323771068000293)
                  ·
                    refine ⟨842970920873207075250055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4495844911323771068000293 842970920873207075250055)
                    ·
                      rfl

theorem cell22_2462520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_2462520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462520 prefixEnd_2462520 := by exact prefixLift 2462520
  have htrace : WordTrace (prefixWord ++ tailWord_2462520) baseStart_2462520 baseEnd_2462520 := by
    simpa [prefixWord, tailWord_2462520, baseEnd_2462520] using wordTrace_append hprefix tailTrace_2462520
  have hstable : (prefixWord ++ tailWord_2462520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462520).length < 2 ^ (prefixWord ++ tailWord_2462520).sum := by decide
  have hdescent : baseEnd_2462520 < baseStart_2462520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462533 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_2462533 : Nat := 118140960795 + 2462533 * 2 ^ 59
def prefixEnd_2462533 : Nat := 4983230072969 + 3 ^ 40 * 2462533 * 2
def baseEnd_2462533 : Nat := 842975371038879374675015

theorem tailTrace_2462533 : CollatzResearch.WordTrace tailWord_2462533 prefixEnd_2462533 842975371038879374675015 := by
  unfold tailWord_2462533
  simp only [CollatzResearch.WordTrace]
  refine ⟨89815957187670982998448253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59877304791780655332298835 89815957187670982998448253)
  ·
    refine ⟨33680983945376618624418095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89815957187670982998448253 33680983945376618624418095)
    ·
      refine ⟨50521475918064927936627143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33680983945376618624418095 50521475918064927936627143)
      ·
        refine ⟨75782213877097391904940715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50521475918064927936627143 75782213877097391904940715)
        ·
          refine ⟨113673320815646087857411073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75782213877097391904940715 113673320815646087857411073)
          ·
            refine ⟨85254990611734565893058305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113673320815646087857411073 85254990611734565893058305)
            ·
              refine ⟨63941242958800924419793729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85254990611734565893058305 63941242958800924419793729)
              ·
                refine ⟨47955932219100693314845297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63941242958800924419793729 47955932219100693314845297)
                ·
                  refine ⟨35966949164325519986133973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47955932219100693314845297 35966949164325519986133973)
                  ·
                    refine ⟨842975371038879374675015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35966949164325519986133973 842975371038879374675015)
                    ·
                      rfl

theorem cell22_2462533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_2462533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462533 prefixEnd_2462533 := by exact prefixLift 2462533
  have htrace : WordTrace (prefixWord ++ tailWord_2462533) baseStart_2462533 baseEnd_2462533 := by
    simpa [prefixWord, tailWord_2462533, baseEnd_2462533] using wordTrace_append hprefix tailTrace_2462533
  have hstable : (prefixWord ++ tailWord_2462533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462533).length < 2 ^ (prefixWord ++ tailWord_2462533).sum := by decide
  have hdescent : baseEnd_2462533 < baseStart_2462533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462582 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2462582 : Nat := 118140960795 + 2462582 * 2 ^ 59
def prefixEnd_2462582 : Nat := 4983230072969 + 3 ^ 40 * 2462582 * 2
def baseEnd_2462582 : Nat := 842992144740259580199865

theorem tailTrace_2462582 : CollatzResearch.WordTrace tailWord_2462582 prefixEnd_2462582 842992144740259580199865 := by
  unfold tailWord_2462582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613609022780841522936375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59878496242995642911321333 5613609022780841522936375)
  ·
    refine ⟨8420413534171262284404563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613609022780841522936375 8420413534171262284404563)
    ·
      refine ⟨12630620301256893426606845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8420413534171262284404563 12630620301256893426606845)
      ·
        refine ⟨4736482612971335034977567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12630620301256893426606845 4736482612971335034977567)
        ·
          refine ⟨7104723919457002552466351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736482612971335034977567 7104723919457002552466351)
          ·
            refine ⟨10657085879185503828699527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104723919457002552466351 10657085879185503828699527)
            ·
              refine ⟨15985628818778255743049291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657085879185503828699527 15985628818778255743049291)
              ·
                refine ⟨23978443228167383614573937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15985628818778255743049291 23978443228167383614573937)
                ·
                  refine ⟨17983832421125537710930453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23978443228167383614573937 17983832421125537710930453)
                  ·
                    refine ⟨842992144740259580199865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17983832421125537710930453 842992144740259580199865)
                    ·
                      rfl

theorem cell22_2462582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2462582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462582 prefixEnd_2462582 := by exact prefixLift 2462582
  have htrace : WordTrace (prefixWord ++ tailWord_2462582) baseStart_2462582 baseEnd_2462582 := by
    simpa [prefixWord, tailWord_2462582, baseEnd_2462582] using wordTrace_append hprefix tailTrace_2462582
  have hstable : (prefixWord ++ tailWord_2462582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462582).length < 2 ^ (prefixWord ++ tailWord_2462582).sum := by decide
  have hdescent : baseEnd_2462582 < baseStart_2462582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462595 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 2, 5]
def baseStart_2462595 : Nat := 118140960795 + 2462595 * 2 ^ 59
def prefixEnd_2462595 : Nat := 4983230072969 + 3 ^ 40 * 2462595 * 2
def baseEnd_2462595 : Nat := 842996594905931879624825

theorem tailTrace_2462595 : CollatzResearch.WordTrace tailWord_2462595 prefixEnd_2462595 842996594905931879624825 := by
  unfold tailWord_2462595
  simp only [CollatzResearch.WordTrace]
  refine ⟨89818218513446367587205239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59878812342297578391470159 89818218513446367587205239)
  ·
    refine ⟨134727327770169551380807859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89818218513446367587205239 134727327770169551380807859)
    ·
      refine ⟨202090991655254327071211789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134727327770169551380807859 202090991655254327071211789)
      ·
        refine ⟨75784121870720372651704421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202090991655254327071211789 75784121870720372651704421)
        ·
          refine ⟨14209522850760069872194579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75784121870720372651704421 14209522850760069872194579)
          ·
            refine ⟨21314284276140104808291869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209522850760069872194579 21314284276140104808291869)
            ·
              refine ⟨7992856603552539303109451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21314284276140104808291869 7992856603552539303109451)
              ·
                refine ⟨11989284905328808954664177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7992856603552539303109451 11989284905328808954664177)
                ·
                  refine ⟨8991963678996606715998133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11989284905328808954664177 8991963678996606715998133)
                  ·
                    refine ⟨842996594905931879624825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8991963678996606715998133 842996594905931879624825)
                    ·
                      rfl

theorem cell22_2462595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_2462595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462595 prefixEnd_2462595 := by exact prefixLift 2462595
  have htrace : WordTrace (prefixWord ++ tailWord_2462595) baseStart_2462595 baseEnd_2462595 := by
    simpa [prefixWord, tailWord_2462595, baseEnd_2462595] using wordTrace_append hprefix tailTrace_2462595
  have hstable : (prefixWord ++ tailWord_2462595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462595).length < 2 ^ (prefixWord ++ tailWord_2462595).sum := by decide
  have hdescent : baseEnd_2462595 < baseStart_2462595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462631 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 5]
def baseStart_2462631 : Nat := 118140960795 + 2462631 * 2 ^ 59
def prefixEnd_2462631 : Nat := 4983230072969 + 3 ^ 40 * 2462631 * 2
def baseEnd_2462631 : Nat := 281002972813879928574905

theorem tailTrace_2462631 : CollatzResearch.WordTrace tailWord_2462631 prefixEnd_2462631 281002972813879928574905 := by
  unfold tailWord_2462631
  simp only [CollatzResearch.WordTrace]
  refine ⟨89819531541315945735515747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59879687694210630490343831 89819531541315945735515747)
  ·
    refine ⟨134729297311973918603273621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89819531541315945735515747 134729297311973918603273621)
    ·
      refine ⟨6315435811498777434528451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134729297311973918603273621 6315435811498777434528451)
      ·
        refine ⟨9473153717248166151792677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315435811498777434528451 9473153717248166151792677)
        ·
          refine ⟨1776216321984031153461127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9473153717248166151792677 1776216321984031153461127)
          ·
            refine ⟨2664324482976046730191691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776216321984031153461127 2664324482976046730191691)
            ·
              refine ⟨3996486724464070095287537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664324482976046730191691 3996486724464070095287537)
              ·
                refine ⟨2997365043348052571465653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996486724464070095287537 2997365043348052571465653)
                ·
                  refine ⟨281002972813879928574905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2997365043348052571465653 281002972813879928574905)
                  ·
                    rfl

theorem cell22_2462631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 5].length) (baseStart_2462631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462631 prefixEnd_2462631 := by exact prefixLift 2462631
  have htrace : WordTrace (prefixWord ++ tailWord_2462631) baseStart_2462631 baseEnd_2462631 := by
    simpa [prefixWord, tailWord_2462631, baseEnd_2462631] using wordTrace_append hprefix tailTrace_2462631
  have hstable : (prefixWord ++ tailWord_2462631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462631).length < 2 ^ (prefixWord ++ tailWord_2462631).sum := by decide
  have hdescent : baseEnd_2462631 < baseStart_2462631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462655 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 6, 4]
def baseStart_2462655 : Nat := 118140960795 + 2462655 * 2 ^ 59
def prefixEnd_2462655 : Nat := 4983230072969 + 3 ^ 40 * 2462655 * 2
def baseEnd_2462655 : Nat := 843017134132111723124641

theorem tailTrace_2462655 : CollatzResearch.WordTrace tailWord_2462655 prefixEnd_2462655 843017134132111723124641 := by
  unfold tailWord_2462655
  simp only [CollatzResearch.WordTrace]
  refine ⟨89820406893228997834389419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59880271262152665222926279 89820406893228997834389419)
  ·
    refine ⟨134730610339843496751584129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89820406893228997834389419 134730610339843496751584129)
    ·
      refine ⟨101047957754882622563688097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134730610339843496751584129 101047957754882622563688097)
      ·
        refine ⟨75785968316161966922766073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101047957754882622563688097 75785968316161966922766073)
        ·
          refine ⟨56839476237121475192074555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75785968316161966922766073 56839476237121475192074555)
          ·
            refine ⟨85259214355682212788111833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56839476237121475192074555 85259214355682212788111833)
            ·
              refine ⟨63944410766761659591083875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85259214355682212788111833 63944410766761659591083875)
              ·
                refine ⟨95916616150142489386625813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63944410766761659591083875 95916616150142489386625813)
                ·
                  refine ⟨4496091382037929189998085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95916616150142489386625813 4496091382037929189998085)
                  ·
                    refine ⟨843017134132111723124641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4496091382037929189998085 843017134132111723124641)
                    ·
                      rfl

theorem cell22_2462655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_2462655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462655 prefixEnd_2462655 := by exact prefixLift 2462655
  have htrace : WordTrace (prefixWord ++ tailWord_2462655) baseStart_2462655 baseEnd_2462655 := by
    simpa [prefixWord, tailWord_2462655, baseEnd_2462655] using wordTrace_append hprefix tailTrace_2462655
  have hstable : (prefixWord ++ tailWord_2462655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462655).length < 2 ^ (prefixWord ++ tailWord_2462655).sum := by decide
  have hdescent : baseEnd_2462655 < baseStart_2462655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462669 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2462669 : Nat := 118140960795 + 2462669 * 2 ^ 59
def prefixEnd_2462669 : Nat := 4983230072969 + 3 ^ 40 * 2462669 * 2
def baseEnd_2462669 : Nat := 843021926618220353274599

theorem tailTrace_2462669 : CollatzResearch.WordTrace tailWord_2462669 prefixEnd_2462669 843021926618220353274599 := by
  unfold tailWord_2462669
  simp only [CollatzResearch.WordTrace]
  refine ⟨89820917515178278225399061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59880611676785518816932707 89820917515178278225399061)
  ·
    refine ⟨4210355508523981791815581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89820917515178278225399061 4210355508523981791815581)
    ·
      refine ⟨1578883315696493171930843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4210355508523981791815581 1578883315696493171930843)
      ·
        refine ⟨2368324973544739757896265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578883315696493171930843 2368324973544739757896265)
        ·
          refine ⟨1776243730158554818422199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2368324973544739757896265 1776243730158554818422199)
          ·
            refine ⟨2664365595237832227633299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776243730158554818422199 2664365595237832227633299)
            ·
              refine ⟨3996548392856748341449949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664365595237832227633299 3996548392856748341449949)
              ·
                refine ⟨1498705647321280628043731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3996548392856748341449949 1498705647321280628043731)
                ·
                  refine ⟨2248058470981920942065597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498705647321280628043731 2248058470981920942065597)
                  ·
                    refine ⟨843021926618220353274599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248058470981920942065597 843021926618220353274599)
                    ·
                      rfl

theorem cell22_2462669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2462669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462669 prefixEnd_2462669 := by exact prefixLift 2462669
  have htrace : WordTrace (prefixWord ++ tailWord_2462669) baseStart_2462669 baseEnd_2462669 := by
    simpa [prefixWord, tailWord_2462669, baseEnd_2462669] using wordTrace_append hprefix tailTrace_2462669
  have hstable : (prefixWord ++ tailWord_2462669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462669).length < 2 ^ (prefixWord ++ tailWord_2462669).sum := by decide
  have hdescent : baseEnd_2462669 < baseStart_2462669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462674 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2462674 : Nat := 118140960795 + 2462674 * 2 ^ 59
def prefixEnd_2462674 : Nat := 4983230072969 + 3 ^ 40 * 2462674 * 2
def baseEnd_2462674 : Nat := 843023638220402006899583

theorem tailTrace_2462674 : CollatzResearch.WordTrace tailWord_2462674 prefixEnd_2462674 843023638220402006899583 := by
  unfold tailWord_2462674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22455274970040041019832769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59880733253440109386220717 22455274970040041019832769)
  ·
    refine ⟨16841456227530030764874577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22455274970040041019832769 16841456227530030764874577)
    ·
      refine ⟨12631092170647523073655933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16841456227530030764874577 12631092170647523073655933)
      ·
        refine ⟨4736659563992821152620975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12631092170647523073655933 4736659563992821152620975)
        ·
          refine ⟨7104989345989231728931463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736659563992821152620975 7104989345989231728931463)
          ·
            refine ⟨10657484018983847593397195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104989345989231728931463 10657484018983847593397195)
            ·
              refine ⟨15986226028475771390095793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657484018983847593397195 15986226028475771390095793)
              ·
                refine ⟨11989669521356828542571845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15986226028475771390095793 11989669521356828542571845)
                ·
                  refine ⟨2248063035254405351732221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11989669521356828542571845 2248063035254405351732221)
                  ·
                    refine ⟨843023638220402006899583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248063035254405351732221 843023638220402006899583)
                    ·
                      rfl

theorem cell22_2462674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2462674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462674 prefixEnd_2462674 := by exact prefixLift 2462674
  have htrace : WordTrace (prefixWord ++ tailWord_2462674) baseStart_2462674 baseEnd_2462674 := by
    simpa [prefixWord, tailWord_2462674, baseEnd_2462674] using wordTrace_append hprefix tailTrace_2462674
  have hstable : (prefixWord ++ tailWord_2462674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462674).length < 2 ^ (prefixWord ++ tailWord_2462674).sum := by decide
  have hdescent : baseEnd_2462674 < baseStart_2462674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462676 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 4]
def baseStart_2462676 : Nat := 118140960795 + 2462676 * 2 ^ 59
def prefixEnd_2462676 : Nat := 4983230072969 + 3 ^ 40 * 2462676 * 2
def baseEnd_2462676 : Nat := 281008107620424889449859

theorem tailTrace_2462676 : CollatzResearch.WordTrace tailWord_2462676 prefixEnd_2462676 281008107620424889449859 := by
  unfold tailWord_2462676
  simp only [CollatzResearch.WordTrace]
  refine ⟨44910586413076459210451941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59880781884101945613935921 44910586413076459210451941)
  ·
    refine ⟨8420734952451836101959739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44910586413076459210451941 8420734952451836101959739)
    ·
      refine ⟨12631102428677754152939609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8420734952451836101959739 12631102428677754152939609)
      ·
        refine ⟨9473326821508315614704707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12631102428677754152939609 9473326821508315614704707)
        ·
          refine ⟨14209990232262473422057061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473326821508315614704707 14209990232262473422057061)
          ·
            refine ⟨2664373168549213766635699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14209990232262473422057061 2664373168549213766635699)
            ·
              refine ⟨3996559752823820649953549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664373168549213766635699 3996559752823820649953549)
              ·
                refine ⟨1498709907308932743732581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3996559752823820649953549 1498709907308932743732581)
                ·
                  refine ⟨281008107620424889449859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498709907308932743732581 281008107620424889449859)
                  ·
                    rfl

theorem cell22_2462676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_2462676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462676 prefixEnd_2462676 := by exact prefixLift 2462676
  have htrace : WordTrace (prefixWord ++ tailWord_2462676) baseStart_2462676 baseEnd_2462676 := by
    simpa [prefixWord, tailWord_2462676, baseEnd_2462676] using wordTrace_append hprefix tailTrace_2462676
  have hstable : (prefixWord ++ tailWord_2462676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462676).length < 2 ^ (prefixWord ++ tailWord_2462676).sum := by decide
  have hdescent : baseEnd_2462676 < baseStart_2462676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462687 : List Nat := [1, 1, 2, 3, 5, 2, 8]
def baseStart_2462687 : Nat := 118140960795 + 2462687 * 2 ^ 59
def prefixEnd_2462687 : Nat := 4983230072969 + 3 ^ 40 * 2462687 * 2
def baseEnd_2462687 : Nat := 31223262532817566900909

theorem tailTrace_2462687 : CollatzResearch.WordTrace tailWord_2462687 prefixEnd_2462687 31223262532817566900909 := by
  unfold tailWord_2462687
  simp only [CollatzResearch.WordTrace]
  refine ⟨89821574029113067299554315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59881049352742044866369543 89821574029113067299554315)
  ·
    refine ⟨134732361043669600949331473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89821574029113067299554315 134732361043669600949331473)
    ·
      refine ⟨101049270782752200711998605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134732361043669600949331473 101049270782752200711998605)
      ·
        refine ⟨37893476543532075266999477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101049270782752200711998605 37893476543532075266999477)
        ·
          refine ⟨3552513425956132056281201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37893476543532075266999477 3552513425956132056281201)
          ·
            refine ⟨2664385069467099042210901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552513425956132056281201 2664385069467099042210901)
            ·
              refine ⟨31223262532817566900909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2664385069467099042210901 31223262532817566900909)
              ·
                rfl

theorem cell22_2462687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 8].length) (baseStart_2462687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462687 prefixEnd_2462687 := by exact prefixLift 2462687
  have htrace : WordTrace (prefixWord ++ tailWord_2462687) baseStart_2462687 baseEnd_2462687 := by
    simpa [prefixWord, tailWord_2462687, baseEnd_2462687] using wordTrace_append hprefix tailTrace_2462687
  have hstable : (prefixWord ++ tailWord_2462687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462687).length < 2 ^ (prefixWord ++ tailWord_2462687).sum := by decide
  have hdescent : baseEnd_2462687 < baseStart_2462687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462693 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 4]
def baseStart_2462693 : Nat := 118140960795 + 2462693 * 2 ^ 59
def prefixEnd_2462693 : Nat := 4983230072969 + 3 ^ 40 * 2462693 * 2
def baseEnd_2462693 : Nat := 281010047436230763558175

theorem tailTrace_2462693 : CollatzResearch.WordTrace tailWord_2462693 prefixEnd_2462693 281010047436230763558175 := by
  unfold tailWord_2462693
  simp only [CollatzResearch.WordTrace]
  refine ⟨89821792867091330324272733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59881195244727553549515155 89821792867091330324272733)
  ·
    refine ⟨33683172325159248871602275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89821792867091330324272733 33683172325159248871602275)
    ·
      refine ⟨50524758487738873307403413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33683172325159248871602275 50524758487738873307403413)
      ·
        refine ⟨2368348054112759686284535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50524758487738873307403413 2368348054112759686284535)
        ·
          refine ⟨3552522081169139529426803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368348054112759686284535 3552522081169139529426803)
          ·
            refine ⟨5328783121753709294140205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552522081169139529426803 5328783121753709294140205)
            ·
              refine ⟨1998293670657640985302577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5328783121753709294140205 1998293670657640985302577)
              ·
                refine ⟨1498720252993230738976933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998293670657640985302577 1498720252993230738976933)
                ·
                  refine ⟨281010047436230763558175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498720252993230738976933 281010047436230763558175)
                  ·
                    rfl

theorem cell22_2462693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_2462693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462693 prefixEnd_2462693 := by exact prefixLift 2462693
  have htrace : WordTrace (prefixWord ++ tailWord_2462693) baseStart_2462693 baseEnd_2462693 := by
    simpa [prefixWord, tailWord_2462693, baseEnd_2462693] using wordTrace_append hprefix tailTrace_2462693
  have hstable : (prefixWord ++ tailWord_2462693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462693).length < 2 ^ (prefixWord ++ tailWord_2462693).sum := by decide
  have hdescent : baseEnd_2462693 < baseStart_2462693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462753 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 1, 3]
def baseStart_2462753 : Nat := 118140960795 + 2462753 * 2 ^ 59
def prefixEnd_2462753 : Nat := 4983230072969 + 3 ^ 40 * 2462753 * 2
def baseEnd_2462753 : Nat := 843050681534872134174341

theorem tailTrace_2462753 : CollatzResearch.WordTrace tailWord_2462753 prefixEnd_2462753 843050681534872134174341 := by
  unfold tailWord_2462753
  simp only [CollatzResearch.WordTrace]
  refine ⟨89823981246873960571456913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59882654164582640380971275 89823981246873960571456913)
  ·
    refine ⟨67367985935155470428592685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89823981246873960571456913 67367985935155470428592685)
    ·
      refine ⟨25262994725683301410722257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67367985935155470428592685 25262994725683301410722257)
      ·
        refine ⟨18947246044262476058041693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25262994725683301410722257 18947246044262476058041693)
        ·
          refine ⟨7105217266598428521765635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18947246044262476058041693 7105217266598428521765635)
          ·
            refine ⟨10657825899897642782648453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105217266598428521765635 10657825899897642782648453)
            ·
              refine ⟨1998342356230808021746585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10657825899897642782648453 1998342356230808021746585)
              ·
                refine ⟨1498756767173106016309939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998342356230808021746585 1498756767173106016309939)
                ·
                  refine ⟨2248135150759659024464909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498756767173106016309939 2248135150759659024464909)
                  ·
                    refine ⟨843050681534872134174341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248135150759659024464909 843050681534872134174341)
                    ·
                      rfl

theorem cell22_2462753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_2462753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462753 prefixEnd_2462753 := by exact prefixLift 2462753
  have htrace : WordTrace (prefixWord ++ tailWord_2462753) baseStart_2462753 baseEnd_2462753 := by
    simpa [prefixWord, tailWord_2462753, baseEnd_2462753] using wordTrace_append hprefix tailTrace_2462753
  have hstable : (prefixWord ++ tailWord_2462753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462753).length < 2 ^ (prefixWord ++ tailWord_2462753).sum := by decide
  have hdescent : baseEnd_2462753 < baseStart_2462753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462777 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 8]
def baseStart_2462777 : Nat := 118140960795 + 2462777 * 2 ^ 59
def prefixEnd_2462777 : Nat := 4983230072969 + 3 ^ 40 * 2462777 * 2
def baseEnd_2462777 : Nat := 281019632408448023858089

theorem tailTrace_2462777 : CollatzResearch.WordTrace tailWord_2462777 prefixEnd_2462777 281019632408448023858089 := by
  unfold tailWord_2462777
  simp only [CollatzResearch.WordTrace]
  refine ⟨89824856598787012670330585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59883237732524675113553723 89824856598787012670330585)
  ·
    refine ⟨67368642449090259502747939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89824856598787012670330585 67368642449090259502747939)
    ·
      refine ⟨101052963673635389254121909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67368642449090259502747939 101052963673635389254121909)
      ·
        refine ⟨9473715344403317742573929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101052963673635389254121909 9473715344403317742573929)
        ·
          refine ⟨7105286508302488306930447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9473715344403317742573929 7105286508302488306930447)
          ·
            refine ⟨10657929762453732460395671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105286508302488306930447 10657929762453732460395671)
            ·
              refine ⟨15986894643680598690593507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657929762453732460395671 15986894643680598690593507)
              ·
                refine ⟨23980341965520898035890261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15986894643680598690593507 23980341965520898035890261)
                ·
                  refine ⟨281019632408448023858089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23980341965520898035890261 281019632408448023858089)
                  ·
                    rfl

theorem cell22_2462777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_2462777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462777 prefixEnd_2462777 := by exact prefixLift 2462777
  have htrace : WordTrace (prefixWord ++ tailWord_2462777) baseStart_2462777 baseEnd_2462777 := by
    simpa [prefixWord, tailWord_2462777, baseEnd_2462777] using wordTrace_append hprefix tailTrace_2462777
  have hstable : (prefixWord ++ tailWord_2462777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462777).length < 2 ^ (prefixWord ++ tailWord_2462777).sum := by decide
  have hdescent : baseEnd_2462777 < baseStart_2462777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462792 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_2462792 : Nat := 118140960795 + 2462792 * 2 ^ 59
def prefixEnd_2462792 : Nat := 4983230072969 + 3 ^ 40 * 2462792 * 2
def baseEnd_2462792 : Nat := 843064032031889032449221

theorem tailTrace_2462792 : CollatzResearch.WordTrace tailWord_2462792 prefixEnd_2462792 843064032031889032449221 := by
  unfold tailWord_2462792
  simp only [CollatzResearch.WordTrace]
  refine ⟨44912701846866335116063315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59883602462488446821417753 44912701846866335116063315)
  ·
    refine ⟨67369052770299502674094973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44912701846866335116063315 67369052770299502674094973)
    ·
      refine ⟨25263394788862313502785615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67369052770299502674094973 25263394788862313502785615)
      ·
        refine ⟨37895092183293470254178423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25263394788862313502785615 37895092183293470254178423)
        ·
          refine ⟨56842638274940205381267635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37895092183293470254178423 56842638274940205381267635)
          ·
            refine ⟨85263957412410308071901453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56842638274940205381267635 85263957412410308071901453)
            ·
              refine ⟨31973984029653865526963045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85263957412410308071901453 31973984029653865526963045)
              ·
                refine ⟨5995122005560099786305571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31973984029653865526963045 5995122005560099786305571)
                ·
                  refine ⟨8992683008340149679458357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995122005560099786305571 8992683008340149679458357)
                  ·
                    refine ⟨843064032031889032449221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8992683008340149679458357 843064032031889032449221)
                    ·
                      rfl

theorem cell22_2462792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_2462792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462792 prefixEnd_2462792 := by exact prefixLift 2462792
  have htrace : WordTrace (prefixWord ++ tailWord_2462792) baseStart_2462792 baseEnd_2462792 := by
    simpa [prefixWord, tailWord_2462792, baseEnd_2462792] using wordTrace_append hprefix tailTrace_2462792
  have hstable : (prefixWord ++ tailWord_2462792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462792).length < 2 ^ (prefixWord ++ tailWord_2462792).sum := by decide
  have hdescent : baseEnd_2462792 < baseStart_2462792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462794 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_2462794 : Nat := 118140960795 + 2462794 * 2 ^ 59
def prefixEnd_2462794 : Nat := 4983230072969 + 3 ^ 40 * 2462794 * 2
def baseEnd_2462794 : Nat := 281021572224253897966405

theorem tailTrace_2462794 : CollatzResearch.WordTrace tailWord_2462794 prefixEnd_2462794 281021572224253897966405 := by
  unfold tailWord_2462794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22456369159931356143424859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59883651093150283049132957 22456369159931356143424859)
  ·
    refine ⟨33684553739897034215137289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22456369159931356143424859 33684553739897034215137289)
    ·
      refine ⟨25263415304922775661352967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33684553739897034215137289 25263415304922775661352967)
      ·
        refine ⟨37895122957384163492029451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25263415304922775661352967 37895122957384163492029451)
        ·
          refine ⟨56842684436076245238044177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37895122957384163492029451 56842684436076245238044177)
          ·
            refine ⟨42632013327057183928533133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56842684436076245238044177 42632013327057183928533133)
            ·
              refine ⟨15987004997646443973199925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42632013327057183928533133 15987004997646443973199925)
              ·
                refine ⟨1498781718529354122487493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15987004997646443973199925 1498781718529354122487493)
                ·
                  refine ⟨281021572224253897966405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498781718529354122487493 281021572224253897966405)
                  ·
                    rfl

theorem cell22_2462794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_2462794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462794 prefixEnd_2462794 := by exact prefixLift 2462794
  have htrace : WordTrace (prefixWord ++ tailWord_2462794) baseStart_2462794 baseEnd_2462794 := by
    simpa [prefixWord, tailWord_2462794, baseEnd_2462794] using wordTrace_append hprefix tailTrace_2462794
  have hstable : (prefixWord ++ tailWord_2462794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462794).length < 2 ^ (prefixWord ++ tailWord_2462794).sum := by decide
  have hdescent : baseEnd_2462794 < baseStart_2462794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462807 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 4, 4]
def baseStart_2462807 : Nat := 118140960795 + 2462807 * 2 ^ 59
def prefixEnd_2462807 : Nat := 4983230072969 + 3 ^ 40 * 2462807 * 2
def baseEnd_2462807 : Nat := 843069166838433993324175

theorem tailTrace_2462807 : CollatzResearch.WordTrace tailWord_2462807 prefixEnd_2462807 843069166838433993324175 := by
  unfold tailWord_2462807
  simp only [CollatzResearch.WordTrace]
  refine ⟨89825950788678327793922675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59883967192452218529281783 89825950788678327793922675)
  ·
    refine ⟨134738926183017491690884013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89825950788678327793922675 134738926183017491690884013)
    ·
      refine ⟨50527097318631559384081505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134738926183017491690884013 50527097318631559384081505)
      ·
        refine ⟨37895322988973669538061129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50527097318631559384081505 37895322988973669538061129)
        ·
          refine ⟨28421492241730252153545847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37895322988973669538061129 28421492241730252153545847)
          ·
            refine ⟨42632238362595378230318771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28421492241730252153545847 42632238362595378230318771)
            ·
              refine ⟨63948357543893067345478157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42632238362595378230318771 63948357543893067345478157)
              ·
                refine ⟨23980634078959900254554309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63948357543893067345478157 23980634078959900254554309)
                ·
                  refine ⟨4496368889804981297728933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23980634078959900254554309 4496368889804981297728933)
                  ·
                    refine ⟨843069166838433993324175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4496368889804981297728933 843069166838433993324175)
                    ·
                      rfl

theorem cell22_2462807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_2462807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462807 prefixEnd_2462807 := by exact prefixLift 2462807
  have htrace : WordTrace (prefixWord ++ tailWord_2462807) baseStart_2462807 baseEnd_2462807 := by
    simpa [prefixWord, tailWord_2462807, baseEnd_2462807] using wordTrace_append hprefix tailTrace_2462807
  have hstable : (prefixWord ++ tailWord_2462807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462807).length < 2 ^ (prefixWord ++ tailWord_2462807).sum := by decide
  have hdescent : baseEnd_2462807 < baseStart_2462807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462809 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_2462809 : Nat := 118140960795 + 2462809 * 2 ^ 59
def prefixEnd_2462809 : Nat := 4983230072969 + 3 ^ 40 * 2462809 * 2
def baseEnd_2462809 : Nat := 843069851479306654774169

theorem tailTrace_2462809 : CollatzResearch.WordTrace tailWord_2462809 prefixEnd_2462809 843069851479306654774169 := by
  unfold tailWord_2462809
  simp only [CollatzResearch.WordTrace]
  refine ⟨89826023734671082135495481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59884015823114054756996987 89826023734671082135495481)
  ·
    refine ⟨67369517801003311601621611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89826023734671082135495481 67369517801003311601621611)
    ·
      refine ⟨101054276701504967402432417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67369517801003311601621611 101054276701504967402432417)
      ·
        refine ⟨75790707526128725551824313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101054276701504967402432417 75790707526128725551824313)
        ·
          refine ⟨56843030644596544163868235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75790707526128725551824313 56843030644596544163868235)
          ·
            refine ⟨85264545966894816245802353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56843030644596544163868235 85264545966894816245802353)
            ·
              refine ⟨63948409475171112184351765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85264545966894816245802353 63948409475171112184351765)
              ·
                refine ⟨2997581694148645883641489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63948409475171112184351765 2997581694148645883641489)
                ·
                  refine ⟨2248186270611484412731117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2997581694148645883641489 2248186270611484412731117)
                  ·
                    refine ⟨843069851479306654774169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248186270611484412731117 843069851479306654774169)
                    ·
                      rfl

theorem cell22_2462809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_2462809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462809 prefixEnd_2462809 := by exact prefixLift 2462809
  have htrace : WordTrace (prefixWord ++ tailWord_2462809) baseStart_2462809 baseEnd_2462809 := by
    simpa [prefixWord, tailWord_2462809, baseEnd_2462809] using wordTrace_append hprefix tailTrace_2462809
  have hstable : (prefixWord ++ tailWord_2462809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462809).length < 2 ^ (prefixWord ++ tailWord_2462809).sum := by decide
  have hdescent : baseEnd_2462809 < baseStart_2462809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462826 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2462826 : Nat := 118140960795 + 2462826 * 2 ^ 59
def prefixEnd_2462826 : Nat := 4983230072969 + 3 ^ 40 * 2462826 * 2
def baseEnd_2462826 : Nat := 843075670926724277099117

theorem tailTrace_2462826 : CollatzResearch.WordTrace tailWord_2462826 prefixEnd_2462826 843075670926724277099117 := by
  unfold tailWord_2462826
  simp only [CollatzResearch.WordTrace]
  refine ⟨22456660943902373509716083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59884429183739662692576221 22456660943902373509716083)
  ·
    refine ⟨33684991415853560264574125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22456660943902373509716083 33684991415853560264574125)
    ·
      refine ⟨12631871780945085099215297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33684991415853560264574125 12631871780945085099215297)
      ·
        refine ⟨9473903835708813824411473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12631871780945085099215297 9473903835708813824411473)
        ·
          refine ⟨7105427876781610368308605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9473903835708813824411473 7105427876781610368308605)
          ·
            refine ⟨2664535453793103888115727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7105427876781610368308605 2664535453793103888115727)
            ·
              refine ⟨3996803180689655832173591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664535453793103888115727 3996803180689655832173591)
              ·
                refine ⟨5995204771034483748260387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996803180689655832173591 5995204771034483748260387)
                ·
                  refine ⟨8992807156551725622390581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995204771034483748260387 8992807156551725622390581)
                  ·
                    refine ⟨843075670926724277099117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8992807156551725622390581 843075670926724277099117)
                    ·
                      rfl

theorem cell22_2462826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2462826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462826 prefixEnd_2462826 := by exact prefixLift 2462826
  have htrace : WordTrace (prefixWord ++ tailWord_2462826) baseStart_2462826 baseEnd_2462826 := by
    simpa [prefixWord, tailWord_2462826, baseEnd_2462826] using wordTrace_append hprefix tailTrace_2462826
  have hstable : (prefixWord ++ tailWord_2462826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462826).length < 2 ^ (prefixWord ++ tailWord_2462826).sum := by decide
  have hdescent : baseEnd_2462826 < baseStart_2462826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462856 : List Nat := [2, 1, 3, 4, 3, 1, 8]
def baseStart_2462856 : Nat := 118140960795 + 2462856 * 2 ^ 59
def prefixEnd_2462856 : Nat := 4983230072969 + 3 ^ 40 * 2462856 * 2
def baseEnd_2462856 : Nat := 31225405205178303661075

theorem tailTrace_2462856 : CollatzResearch.WordTrace tailWord_2462856 prefixEnd_2462856 31225405205178303661075 := by
  unfold tailWord_2462856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44913868982750404581228211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59885158643667206108304281 44913868982750404581228211)
  ·
    refine ⟨67370803474125606871842317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44913868982750404581228211 67370803474125606871842317)
    ·
      refine ⟨25264051302797102576940869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67370803474125606871842317 25264051302797102576940869)
      ·
        refine ⟨4737009619274456733176413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25264051302797102576940869 4737009619274456733176413)
        ·
          refine ⟨1776378607227921274941155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4737009619274456733176413 1776378607227921274941155)
          ·
            refine ⟨2664567910841881912411733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776378607227921274941155 2664567910841881912411733)
            ·
              refine ⟨31225405205178303661075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2664567910841881912411733 31225405205178303661075)
              ·
                rfl

theorem cell22_2462856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 8].length) (baseStart_2462856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462856 prefixEnd_2462856 := by exact prefixLift 2462856
  have htrace : WordTrace (prefixWord ++ tailWord_2462856) baseStart_2462856 baseEnd_2462856 := by
    simpa [prefixWord, tailWord_2462856, baseEnd_2462856] using wordTrace_append hprefix tailTrace_2462856
  have hstable : (prefixWord ++ tailWord_2462856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462856).length < 2 ^ (prefixWord ++ tailWord_2462856).sum := by decide
  have hdescent : baseEnd_2462856 < baseStart_2462856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462867 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 7]
def baseStart_2462867 : Nat := 118140960795 + 2462867 * 2 ^ 59
def prefixEnd_2462867 : Nat := 4983230072969 + 3 ^ 40 * 2462867 * 2
def baseEnd_2462867 : Nat := 281029902021537945607997

theorem tailTrace_2462867 : CollatzResearch.WordTrace tailWord_2462867 prefixEnd_2462867 281029902021537945607997 := by
  unfold tailWord_2462867
  simp only [CollatzResearch.WordTrace]
  refine ⟨89828139168460958041106855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59885426112307305360737903 89828139168460958041106855)
  ·
    refine ⟨134742208752691437061660283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89828139168460958041106855 134742208752691437061660283)
    ·
      refine ⟨202113313129037155592490425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134742208752691437061660283 202113313129037155592490425)
      ·
        refine ⟨151584984846777866694367819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202113313129037155592490425 151584984846777866694367819)
        ·
          refine ⟨227377477270166800041551729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151584984846777866694367819 227377477270166800041551729)
          ·
            refine ⟨170533107952625100031163797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227377477270166800041551729 170533107952625100031163797)
            ·
              refine ⟨7993739435279301563960803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170533107952625100031163797 7993739435279301563960803)
              ·
                refine ⟨11990609152918952345941205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993739435279301563960803 11990609152918952345941205)
                ·
                  refine ⟨281029902021537945607997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11990609152918952345941205 281029902021537945607997)
                  ·
                    rfl

theorem cell22_2462867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_2462867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462867 prefixEnd_2462867 := by exact prefixLift 2462867
  have htrace : WordTrace (prefixWord ++ tailWord_2462867) baseStart_2462867 baseEnd_2462867 := by
    simpa [prefixWord, tailWord_2462867, baseEnd_2462867] using wordTrace_append hprefix tailTrace_2462867
  have hstable : (prefixWord ++ tailWord_2462867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462867).length < 2 ^ (prefixWord ++ tailWord_2462867).sum := by decide
  have hdescent : baseEnd_2462867 < baseStart_2462867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462871 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 3, 3]
def baseStart_2462871 : Nat := 118140960795 + 2462871 * 2 ^ 59
def prefixEnd_2462871 : Nat := 4983230072969 + 3 ^ 40 * 2462871 * 2
def baseEnd_2462871 : Nat := 843091075346359159723979

theorem tailTrace_2462871 : CollatzResearch.WordTrace tailWord_2462871 prefixEnd_2462871 843091075346359159723979 := by
  unfold tailWord_2462871
  simp only [CollatzResearch.WordTrace]
  refine ⟨89828285060446466724252467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59885523373630977816168311 89828285060446466724252467)
  ·
    refine ⟨134742427590669700086378701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89828285060446466724252467 134742427590669700086378701)
    ·
      refine ⟨50528410346501137532392013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134742427590669700086378701 50528410346501137532392013)
      ·
        refine ⟨18948153879937926574647005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50528410346501137532392013 18948153879937926574647005)
        ·
          refine ⟨7105557704976722465492627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18948153879937926574647005 7105557704976722465492627)
          ·
            refine ⟨10658336557465083698238941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105557704976722465492627 10658336557465083698238941)
            ·
              refine ⟨3996876209049406386839603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10658336557465083698238941 3996876209049406386839603)
              ·
                refine ⟨5995314313574109580259405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996876209049406386839603 5995314313574109580259405)
                ·
                  refine ⟨2248242867590291092597277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5995314313574109580259405 2248242867590291092597277)
                  ·
                    refine ⟨843091075346359159723979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248242867590291092597277 843091075346359159723979)
                    ·
                      rfl

theorem cell22_2462871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_2462871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462871 prefixEnd_2462871 := by exact prefixLift 2462871
  have htrace : WordTrace (prefixWord ++ tailWord_2462871) baseStart_2462871 baseEnd_2462871 := by
    simpa [prefixWord, tailWord_2462871, baseEnd_2462871] using wordTrace_append hprefix tailTrace_2462871
  have hstable : (prefixWord ++ tailWord_2462871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462871).length < 2 ^ (prefixWord ++ tailWord_2462871).sum := by decide
  have hdescent : baseEnd_2462871 < baseStart_2462871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2462944 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_2462944 : Nat := 118140960795 + 2462944 * 2 ^ 59
def prefixEnd_2462944 : Nat := 4983230072969 + 3 ^ 40 * 2462944 * 2
def baseEnd_2462944 : Nat := 843116064738211302648755

theorem tailTrace_2462944 : CollatzResearch.WordTrace tailWord_2462944 prefixEnd_2462944 843116064738211302648755 := by
  unfold tailWord_2462944
  simp only [CollatzResearch.WordTrace]
  refine ⟨44915473794591000095829943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59887298392788000127773257 44915473794591000095829943)
  ·
    refine ⟨67373210691886500143744915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44915473794591000095829943 67373210691886500143744915)
    ·
      refine ⟨101059816037829750215617373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67373210691886500143744915 101059816037829750215617373)
      ·
        refine ⟨37897431014186156330856515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101059816037829750215617373 37897431014186156330856515)
        ·
          refine ⟨56846146521279234496284773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37897431014186156330856515 56846146521279234496284773)
          ·
            refine ⟨10658652472739856468053395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56846146521279234496284773 10658652472739856468053395)
            ·
              refine ⟨15987978709109784702080093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10658652472739856468053395 15987978709109784702080093)
              ·
                refine ⟨5995492015916169263280035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15987978709109784702080093 5995492015916169263280035)
                ·
                  refine ⟨8993238023874253894920053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995492015916169263280035 8993238023874253894920053)
                  ·
                    refine ⟨843116064738211302648755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8993238023874253894920053 843116064738211302648755)
                    ·
                      rfl

theorem cell22_2462944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_2462944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2462944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2462944 prefixEnd_2462944 := by exact prefixLift 2462944
  have htrace : WordTrace (prefixWord ++ tailWord_2462944) baseStart_2462944 baseEnd_2462944 := by
    simpa [prefixWord, tailWord_2462944, baseEnd_2462944] using wordTrace_append hprefix tailTrace_2462944
  have hstable : (prefixWord ++ tailWord_2462944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2462944).length < 2 ^ (prefixWord ++ tailWord_2462944).sum := by decide
  have hdescent : baseEnd_2462944 < baseStart_2462944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2462944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463004 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2463004 : Nat := 118140960795 + 2463004 * 2 ^ 59
def prefixEnd_2463004 : Nat := 4983230072969 + 3 ^ 40 * 2463004 * 2
def baseEnd_2463004 : Nat := 843136603964391146148571

theorem tailTrace_2463004 : CollatzResearch.WordTrace tailWord_2463004 prefixEnd_2463004 843136603964391146148571 := by
  unfold tailWord_2463004
  simp only [CollatzResearch.WordTrace]
  refine ⟨44916567984482315219422033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59888757312643086959229377 44916567984482315219422033)
  ·
    refine ⟨33687425988361736414566525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44916567984482315219422033 33687425988361736414566525)
    ·
      refine ⟨12632784745635651155462447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33687425988361736414566525 12632784745635651155462447)
      ·
        refine ⟨18949177118453476733193671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12632784745635651155462447 18949177118453476733193671)
        ·
          refine ⟨28423765677680215099790507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18949177118453476733193671 28423765677680215099790507)
          ·
            refine ⟨42635648516520322649685761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28423765677680215099790507 42635648516520322649685761)
            ·
              refine ⟨31976736387390241987264321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42635648516520322649685761 31976736387390241987264321)
              ·
                refine ⟨23982552290542681490448241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31976736387390241987264321 23982552290542681490448241)
                ·
                  refine ⟨17986914217907011117836181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23982552290542681490448241 17986914217907011117836181)
                  ·
                    refine ⟨843136603964391146148571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17986914217907011117836181 843136603964391146148571)
                    ·
                      rfl

theorem cell22_2463004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2463004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463004 prefixEnd_2463004 := by exact prefixLift 2463004
  have htrace : WordTrace (prefixWord ++ tailWord_2463004) baseStart_2463004 baseEnd_2463004 := by
    simpa [prefixWord, tailWord_2463004, baseEnd_2463004] using wordTrace_append hprefix tailTrace_2463004
  have hstable : (prefixWord ++ tailWord_2463004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463004).length < 2 ^ (prefixWord ++ tailWord_2463004).sum := by decide
  have hdescent : baseEnd_2463004 < baseStart_2463004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463008 : List Nat := [2, 1, 1, 5, 3, 2, 2, 6]
def baseStart_2463008 : Nat := 118140960795 + 2463008 * 2 ^ 59
def prefixEnd_2463008 : Nat := 4983230072969 + 3 ^ 40 * 2463008 * 2
def baseEnd_2463008 : Nat := 93681997027348496560951

theorem tailTrace_2463008 : CollatzResearch.WordTrace tailWord_2463008 prefixEnd_2463008 93681997027348496560951 := by
  unfold tailWord_2463008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44916640930475069560994839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59888854573966759414659785 44916640930475069560994839)
  ·
    refine ⟨67374961395712604341492259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44916640930475069560994839 67374961395712604341492259)
    ·
      refine ⟨101062442093568906512238389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67374961395712604341492259 101062442093568906512238389)
      ·
        refine ⟨9474603946272084985522349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101062442093568906512238389 9474603946272084985522349)
        ·
          refine ⟨3552976479852031869570881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9474603946272084985522349 3552976479852031869570881)
          ·
            refine ⟨2664732359889023902178161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552976479852031869570881 2664732359889023902178161)
            ·
              refine ⟨1998549269916767926633621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664732359889023902178161 1998549269916767926633621)
              ·
                refine ⟨93681997027348496560951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1998549269916767926633621 93681997027348496560951)
                ·
                  rfl

theorem cell22_2463008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_2463008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463008 prefixEnd_2463008 := by exact prefixLift 2463008
  have htrace : WordTrace (prefixWord ++ tailWord_2463008) baseStart_2463008 baseEnd_2463008 := by
    simpa [prefixWord, tailWord_2463008, baseEnd_2463008] using wordTrace_append hprefix tailTrace_2463008
  have hstable : (prefixWord ++ tailWord_2463008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463008).length < 2 ^ (prefixWord ++ tailWord_2463008).sum := by decide
  have hdescent : baseEnd_2463008 < baseStart_2463008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463040 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 1, 3]
def baseStart_2463040 : Nat := 118140960795 + 2463040 * 2 ^ 59
def prefixEnd_2463040 : Nat := 4983230072969 + 3 ^ 40 * 2463040 * 2
def baseEnd_2463040 : Nat := 843148927500099052248461

theorem tailTrace_2463040 : CollatzResearch.WordTrace tailWord_2463040 prefixEnd_2463040 843148927500099052248461 := by
  unfold tailWord_2463040
  simp only [CollatzResearch.WordTrace]
  refine ⟨44917224498417104293577287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59889632664556139058103049 44917224498417104293577287)
  ·
    refine ⟨67375836747625656440365931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44917224498417104293577287 67375836747625656440365931)
    ·
      refine ⟨101063755121438484660548897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67375836747625656440365931 101063755121438484660548897)
      ·
        refine ⟨75797816341078863495411673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101063755121438484660548897 75797816341078863495411673)
        ·
          refine ⟨56848362255809147621558755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75797816341078863495411673 56848362255809147621558755)
          ·
            refine ⟨85272543383713721432338133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56848362255809147621558755 85272543383713721432338133)
            ·
              refine ⟨1998575235555790346070425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85272543383713721432338133 1998575235555790346070425)
              ·
                refine ⟨1498931426666842759552819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998575235555790346070425 1498931426666842759552819)
                ·
                  refine ⟨2248397140000264139329229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498931426666842759552819 2248397140000264139329229)
                  ·
                    refine ⟨843148927500099052248461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248397140000264139329229 843148927500099052248461)
                    ·
                      rfl

theorem cell22_2463040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_2463040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463040 prefixEnd_2463040 := by exact prefixLift 2463040
  have htrace : WordTrace (prefixWord ++ tailWord_2463040) baseStart_2463040 baseEnd_2463040 := by
    simpa [prefixWord, tailWord_2463040, baseEnd_2463040] using wordTrace_append hprefix tailTrace_2463040
  have hstable : (prefixWord ++ tailWord_2463040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463040).length < 2 ^ (prefixWord ++ tailWord_2463040).sum := by decide
  have hdescent : baseEnd_2463040 < baseStart_2463040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463046 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2463046 : Nat := 118140960795 + 2463046 * 2 ^ 59
def prefixEnd_2463046 : Nat := 4983230072969 + 3 ^ 40 * 2463046 * 2
def baseEnd_2463046 : Nat := 843150981422717036598443

theorem tailTrace_2463046 : CollatzResearch.WordTrace tailWord_2463046 prefixEnd_2463046 843150981422717036598443 := by
  unfold tailWord_2463046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807333369837889737871031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59889778556541647741248661 2807333369837889737871031)
  ·
    refine ⟨4211000054756834606806547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2807333369837889737871031 4211000054756834606806547)
    ·
      refine ⟨6316500082135251910209821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4211000054756834606806547 6316500082135251910209821)
      ·
        refine ⟨2368687530800719466328683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6316500082135251910209821 2368687530800719466328683)
        ·
          refine ⟨3553031296201079199493025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368687530800719466328683 3553031296201079199493025)
          ·
            refine ⟨2664773472150809399619769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553031296201079199493025 2664773472150809399619769)
            ·
              refine ⟨1998580104113107049714827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664773472150809399619769 1998580104113107049714827)
              ·
                refine ⟨2997870156169660574572241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998580104113107049714827 2997870156169660574572241)
                ·
                  refine ⟨2248402617127245430929181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2997870156169660574572241 2248402617127245430929181)
                  ·
                    refine ⟨843150981422717036598443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248402617127245430929181 843150981422717036598443)
                    ·
                      rfl

theorem cell22_2463046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2463046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463046 prefixEnd_2463046 := by exact prefixLift 2463046
  have htrace : WordTrace (prefixWord ++ tailWord_2463046) baseStart_2463046 baseEnd_2463046 := by
    simpa [prefixWord, tailWord_2463046, baseEnd_2463046] using wordTrace_append hprefix tailTrace_2463046
  have hstable : (prefixWord ++ tailWord_2463046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463046).length < 2 ^ (prefixWord ++ tailWord_2463046).sum := by decide
  have hdescent : baseEnd_2463046 < baseStart_2463046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463064 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_2463064 : Nat := 118140960795 + 2463064 * 2 ^ 59
def prefixEnd_2463064 : Nat := 4983230072969 + 3 ^ 40 * 2463064 * 2
def baseEnd_2463064 : Nat := 281052381063523663216129

theorem tailTrace_2463064 : CollatzResearch.WordTrace tailWord_2463064 prefixEnd_2463064 281052381063523663216129 := by
  unfold tailWord_2463064
  simp only [CollatzResearch.WordTrace]
  refine ⟨44917662174373630343014123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59890216232498173790685497 44917662174373630343014123)
  ·
    refine ⟨67376493261560445514521185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44917662174373630343014123 67376493261560445514521185)
    ·
      refine ⟨50532369946170334135890889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67376493261560445514521185 50532369946170334135890889)
      ·
        refine ⟨37899277459627750601918167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50532369946170334135890889 37899277459627750601918167)
        ·
          refine ⟨56848916189441625902877251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37899277459627750601918167 56848916189441625902877251)
          ·
            refine ⟨85273374284162438854315877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56848916189441625902877251 85273374284162438854315877)
            ·
              refine ⟨15988757678280457285184227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85273374284162438854315877 15988757678280457285184227)
              ·
                refine ⟨23983136517420685927776341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15988757678280457285184227 23983136517420685927776341)
                ·
                  refine ⟨281052381063523663216129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23983136517420685927776341 281052381063523663216129)
                  ·
                    rfl

theorem cell22_2463064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_2463064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463064 prefixEnd_2463064 := by exact prefixLift 2463064
  have htrace : WordTrace (prefixWord ++ tailWord_2463064) baseStart_2463064 baseEnd_2463064 := by
    simpa [prefixWord, tailWord_2463064, baseEnd_2463064] using wordTrace_append hprefix tailTrace_2463064
  have hstable : (prefixWord ++ tailWord_2463064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463064).length < 2 ^ (prefixWord ++ tailWord_2463064).sum := by decide
  have hdescent : baseEnd_2463064 < baseStart_2463064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463113 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_2463113 : Nat := 118140960795 + 2463113 * 2 ^ 59
def prefixEnd_2463113 : Nat := 4983230072969 + 3 ^ 40 * 2463113 * 2
def baseEnd_2463113 : Nat := 843173916891951195173237

theorem tailTrace_2463113 : CollatzResearch.WordTrace tailWord_2463113 prefixEnd_2463113 843173916891951195173237 := by
  unfold tailWord_2463113
  simp only [CollatzResearch.WordTrace]
  refine ⟨89837111525569742054561993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59891407683713161369707995 89837111525569742054561993)
  ·
    refine ⟨67377833644177306540921495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89837111525569742054561993 67377833644177306540921495)
    ·
      refine ⟨101066750466265959811382243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67377833644177306540921495 101066750466265959811382243)
      ·
        refine ⟨151600125699398939717073365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101066750466265959811382243 151600125699398939717073365)
        ·
          refine ⟨3553127946079662649618907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 151600125699398939717073365 3553127946079662649618907)
          ·
            refine ⟨5329691919119493974428361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553127946079662649618907 5329691919119493974428361)
            ·
              refine ⟨3997268939339620480821271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5329691919119493974428361 3997268939339620480821271)
              ·
                refine ⟨5995903409009430721231907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3997268939339620480821271 5995903409009430721231907)
                ·
                  refine ⟨8993855113514146081847861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995903409009430721231907 8993855113514146081847861)
                  ·
                    refine ⟨843173916891951195173237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8993855113514146081847861 843173916891951195173237)
                    ·
                      rfl

theorem cell22_2463113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_2463113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463113 prefixEnd_2463113 := by exact prefixLift 2463113
  have htrace : WordTrace (prefixWord ++ tailWord_2463113) baseStart_2463113 baseEnd_2463113 := by
    simpa [prefixWord, tailWord_2463113, baseEnd_2463113] using wordTrace_append hprefix tailTrace_2463113
  have hstable : (prefixWord ++ tailWord_2463113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463113).length < 2 ^ (prefixWord ++ tailWord_2463113).sum := by decide
  have hdescent : baseEnd_2463113 < baseStart_2463113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463128 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_2463128 : Nat := 118140960795 + 2463128 * 2 ^ 59
def prefixEnd_2463128 : Nat := 4983230072969 + 3 ^ 40 * 2463128 * 2
def baseEnd_2463128 : Nat := 843179051698496156048191

theorem tailTrace_2463128 : CollatzResearch.WordTrace tailWord_2463128 prefixEnd_2463128 843179051698496156048191 := by
  unfold tailWord_2463128
  simp only [CollatzResearch.WordTrace]
  refine ⟨44918829310257699808179019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59891772413676933077572025 44918829310257699808179019)
  ·
    refine ⟨67378243965386549712268529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44918829310257699808179019 67378243965386549712268529)
    ·
      refine ⟨50533682974039912284201397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67378243965386549712268529 50533682974039912284201397)
      ·
        refine ⟨4737532778816241776643881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50533682974039912284201397 4737532778816241776643881)
        ·
          refine ⟨3553149584112181332482911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4737532778816241776643881 3553149584112181332482911)
          ·
            refine ⟨5329724376168271998724367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553149584112181332482911 5329724376168271998724367)
            ·
              refine ⟨7994586564252407998086551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329724376168271998724367 7994586564252407998086551)
              ·
                refine ⟨11991879846378611997129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7994586564252407998086551 11991879846378611997129827)
                ·
                  refine ⟨17987819769567917995694741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11991879846378611997129827 17987819769567917995694741)
                  ·
                    refine ⟨843179051698496156048191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17987819769567917995694741 843179051698496156048191)
                    ·
                      rfl

theorem cell22_2463128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_2463128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463128 prefixEnd_2463128 := by exact prefixLift 2463128
  have htrace : WordTrace (prefixWord ++ tailWord_2463128) baseStart_2463128 baseEnd_2463128 := by
    simpa [prefixWord, tailWord_2463128, baseEnd_2463128] using wordTrace_append hprefix tailTrace_2463128
  have hstable : (prefixWord ++ tailWord_2463128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463128).length < 2 ^ (prefixWord ++ tailWord_2463128).sum := by decide
  have hdescent : baseEnd_2463128 < baseStart_2463128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463132 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 4]
def baseStart_2463132 : Nat := 118140960795 + 2463132 * 2 ^ 59
def prefixEnd_2463132 : Nat := 4983230072969 + 3 ^ 40 * 2463132 * 2
def baseEnd_2463132 : Nat := 281060140326747159649393

theorem tailTrace_2463132 : CollatzResearch.WordTrace tailWord_2463132 prefixEnd_2463132 281060140326747159649393 := by
  unfold tailWord_2463132
  simp only [CollatzResearch.WordTrace]
  refine ⟨44918902256250454149751825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59891869675000605533002433 44918902256250454149751825)
  ·
    refine ⟨33689176692187840612313869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44918902256250454149751825 33689176692187840612313869)
    ·
      refine ⟨12633441259570440229617701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33689176692187840612313869 12633441259570440229617701)
      ·
        refine ⟨2368770236169457543053319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12633441259570440229617701 2368770236169457543053319)
        ·
          refine ⟨3553155354254186314579979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368770236169457543053319 3553155354254186314579979)
          ·
            refine ⟨5329733031381279471869969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553155354254186314579979 5329733031381279471869969)
            ·
              refine ⟨3997299773535959603902477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5329733031381279471869969 3997299773535959603902477)
              ·
                refine ⟨1498987415075984851463429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3997299773535959603902477 1498987415075984851463429)
                ·
                  refine ⟨281060140326747159649393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1498987415075984851463429 281060140326747159649393)
                  ·
                    rfl

theorem cell22_2463132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_2463132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463132 prefixEnd_2463132 := by exact prefixLift 2463132
  have htrace : WordTrace (prefixWord ++ tailWord_2463132) baseStart_2463132 baseEnd_2463132 := by
    simpa [prefixWord, tailWord_2463132, baseEnd_2463132] using wordTrace_append hprefix tailTrace_2463132
  have hstable : (prefixWord ++ tailWord_2463132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463132).length < 2 ^ (prefixWord ++ tailWord_2463132).sum := by decide
  have hdescent : baseEnd_2463132 < baseStart_2463132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463134 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2463134 : Nat := 118140960795 + 2463134 * 2 ^ 59
def prefixEnd_2463134 : Nat := 4983230072969 + 3 ^ 40 * 2463134 * 2
def baseEnd_2463134 : Nat := 843181105621114140398173

theorem tailTrace_2463134 : CollatzResearch.WordTrace tailWord_2463134 prefixEnd_2463134 843181105621114140398173 := by
  unfold tailWord_2463134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229734682311707830134557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59891918305662441760717637 11229734682311707830134557)
  ·
    refine ⟨4211150505866890436300459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11229734682311707830134557 4211150505866890436300459)
    ·
      refine ⟨6316725758800335654450689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4211150505866890436300459 6316725758800335654450689)
      ·
        refine ⟨4737544319100251740838017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6316725758800335654450689 4737544319100251740838017)
        ·
          refine ⟨3553158239325188805628513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4737544319100251740838017 3553158239325188805628513)
          ·
            refine ⟨2664868679493891604221385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553158239325188805628513 2664868679493891604221385)
            ·
              refine ⟨1998651509620418703166039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664868679493891604221385 1998651509620418703166039)
              ·
                refine ⟨2997977264430628054749059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998651509620418703166039 2997977264430628054749059)
                ·
                  refine ⟨4496965896645942082123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997977264430628054749059 4496965896645942082123589)
                  ·
                    refine ⟨843181105621114140398173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4496965896645942082123589 843181105621114140398173)
                    ·
                      rfl

theorem cell22_2463134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2463134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463134 prefixEnd_2463134 := by exact prefixLift 2463134
  have htrace : WordTrace (prefixWord ++ tailWord_2463134) baseStart_2463134 baseEnd_2463134 := by
    simpa [prefixWord, tailWord_2463134, baseEnd_2463134] using wordTrace_append hprefix tailTrace_2463134
  have hstable : (prefixWord ++ tailWord_2463134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463134).length < 2 ^ (prefixWord ++ tailWord_2463134).sum := by decide
  have hdescent : baseEnd_2463134 < baseStart_2463134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463171 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 5]
def baseStart_2463171 : Nat := 118140960795 + 2463171 * 2 ^ 59
def prefixEnd_2463171 : Nat := 4983230072969 + 3 ^ 40 * 2463171 * 2
def baseEnd_2463171 : Nat := 281064590492419459074353

theorem tailTrace_2463171 : CollatzResearch.WordTrace tailWord_2463171 prefixEnd_2463171 281064590492419459074353 := by
  unfold tailWord_2463171
  simp only [CollatzResearch.WordTrace]
  refine ⟨89839226959359617960173367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59892817972906411973448911 89839226959359617960173367)
  ·
    refine ⟨134758840439039426940260051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89839226959359617960173367 134758840439039426940260051)
    ·
      refine ⟨202138260658559140410390077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134758840439039426940260051 202138260658559140410390077)
      ·
        refine ⟨75801847746959677653896279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202138260658559140410390077 75801847746959677653896279)
        ·
          refine ⟨113702771620439516480844419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75801847746959677653896279 113702771620439516480844419)
          ·
            refine ⟨170554157430659274721266629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113702771620439516480844419 170554157430659274721266629)
            ·
              refine ⟨31978904518248614010237493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170554157430659274721266629 31978904518248614010237493)
              ·
                refine ⟨2998022298585807563459765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31978904518248614010237493 2998022298585807563459765)
                ·
                  refine ⟨281064590492419459074353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998022298585807563459765 281064590492419459074353)
                  ·
                    rfl

theorem cell22_2463171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 5].length) (baseStart_2463171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463171 prefixEnd_2463171 := by exact prefixLift 2463171
  have htrace : WordTrace (prefixWord ++ tailWord_2463171) baseStart_2463171 baseEnd_2463171 := by
    simpa [prefixWord, tailWord_2463171, baseEnd_2463171] using wordTrace_append hprefix tailTrace_2463171
  have hstable : (prefixWord ++ tailWord_2463171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463171).length < 2 ^ (prefixWord ++ tailWord_2463171).sum := by decide
  have hdescent : baseEnd_2463171 < baseStart_2463171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463222 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_2463222 : Nat := 118140960795 + 2463222 * 2 ^ 59
def prefixEnd_2463222 : Nat := 4983230072969 + 3 ^ 40 * 2463222 * 2
def baseEnd_2463222 : Nat := 281070409939837081399301

theorem tailTrace_2463222 : CollatzResearch.WordTrace tailWord_2463222 prefixEnd_2463222 281070409939837081399301 := by
  unfold tailWord_2463222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615067942635928354392495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59894058054783235780186613 5615067942635928354392495)
  ·
    refine ⟨8422601913953892531588743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5615067942635928354392495 8422601913953892531588743)
    ·
      refine ⟨12633902870930838797383115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8422601913953892531588743 12633902870930838797383115)
      ·
        refine ⟨18950854306396258196074673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12633902870930838797383115 18950854306396258196074673)
        ·
          refine ⟨14213140729797193647056005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18950854306396258196074673 14213140729797193647056005)
          ·
            refine ⟨2664963886836973808823001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14213140729797193647056005 2664963886836973808823001)
            ·
              refine ⟨1998722915127730356617251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664963886836973808823001 1998722915127730356617251)
              ·
                refine ⟨2998084372691595534925877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998722915127730356617251 2998084372691595534925877)
                ·
                  refine ⟨281070409939837081399301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998084372691595534925877 281070409939837081399301)
                  ·
                    rfl

theorem cell22_2463222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_2463222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463222 prefixEnd_2463222 := by exact prefixLift 2463222
  have htrace : WordTrace (prefixWord ++ tailWord_2463222) baseStart_2463222 baseEnd_2463222 := by
    simpa [prefixWord, tailWord_2463222, baseEnd_2463222] using wordTrace_append hprefix tailTrace_2463222
  have hstable : (prefixWord ++ tailWord_2463222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463222).length < 2 ^ (prefixWord ++ tailWord_2463222).sum := by decide
  have hdescent : baseEnd_2463222 < baseStart_2463222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463263 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 2, 4]
def baseStart_2463263 : Nat := 118140960795 + 2463263 * 2 ^ 59
def prefixEnd_2463263 : Nat := 4983230072969 + 3 ^ 40 * 2463263 * 2
def baseEnd_2463263 : Nat := 843225264957400803922777

theorem tailTrace_2463263 : CollatzResearch.WordTrace tailWord_2463263 prefixEnd_2463263 843225264957400803922777 := by
  unfold tailWord_2463263
  simp only [CollatzResearch.WordTrace]
  refine ⟨89842582475026317672522443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59895054983350878448348295 89842582475026317672522443)
  ·
    refine ⟨134763873712539476508783665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89842582475026317672522443 134763873712539476508783665)
    ·
      refine ⟨101072905284404607381587749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134763873712539476508783665 101072905284404607381587749)
      ·
        refine ⟨18951169740825863884047703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101072905284404607381587749 18951169740825863884047703)
        ·
          refine ⟨28426754611238795826071555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18951169740825863884047703 28426754611238795826071555)
          ·
            refine ⟨42640131916858193739107333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28426754611238795826071555 42640131916858193739107333)
            ·
              refine ⟨7995024734410911326082625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42640131916858193739107333 7995024734410911326082625)
              ·
                refine ⟨5996268550808183494561969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7995024734410911326082625 5996268550808183494561969)
                ·
                  refine ⟨4497201413106137620921477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5996268550808183494561969 4497201413106137620921477)
                  ·
                    refine ⟨843225264957400803922777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4497201413106137620921477 843225264957400803922777)
                    ·
                      rfl

theorem cell22_2463263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_2463263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463263 prefixEnd_2463263 := by exact prefixLift 2463263
  have htrace : WordTrace (prefixWord ++ tailWord_2463263) baseStart_2463263 baseEnd_2463263 := by
    simpa [prefixWord, tailWord_2463263, baseEnd_2463263] using wordTrace_append hprefix tailTrace_2463263
  have hstable : (prefixWord ++ tailWord_2463263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463263).length < 2 ^ (prefixWord ++ tailWord_2463263).sum := by decide
  have hdescent : baseEnd_2463263 < baseStart_2463263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463265 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2463265 : Nat := 118140960795 + 2463265 * 2 ^ 59
def prefixEnd_2463265 : Nat := 4983230072969 + 3 ^ 40 * 2463265 * 2
def baseEnd_2463265 : Nat := 843225949598273465372771

theorem tailTrace_2463265 : CollatzResearch.WordTrace tailWord_2463265 prefixEnd_2463265 843225949598273465372771 := by
  unfold tailWord_2463265
  simp only [CollatzResearch.WordTrace]
  refine ⟨89842655421019072014095249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59895103614012714676063499 89842655421019072014095249)
  ·
    refine ⟨67381991565764304010571437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89842655421019072014095249 67381991565764304010571437)
    ·
      refine ⟨25268246837161614003964289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67381991565764304010571437 25268246837161614003964289)
      ·
        refine ⟨18951185127871210502973217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25268246837161614003964289 18951185127871210502973217)
        ·
          refine ⟨14213388845903407877229913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18951185127871210502973217 14213388845903407877229913)
          ·
            refine ⟨10660041634427555907922435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14213388845903407877229913 10660041634427555907922435)
            ·
              refine ⟨15990062451641333861883653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660041634427555907922435 15990062451641333861883653)
              ·
                refine ⟨2998136709682750099103185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15990062451641333861883653 2998136709682750099103185)
                ·
                  refine ⟨2248602532262062574327389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2998136709682750099103185 2248602532262062574327389)
                  ·
                    refine ⟨843225949598273465372771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248602532262062574327389 843225949598273465372771)
                    ·
                      rfl

theorem cell22_2463265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2463265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463265 prefixEnd_2463265 := by exact prefixLift 2463265
  have htrace : WordTrace (prefixWord ++ tailWord_2463265) baseStart_2463265 baseEnd_2463265 := by
    simpa [prefixWord, tailWord_2463265, baseEnd_2463265] using wordTrace_append hprefix tailTrace_2463265
  have hstable : (prefixWord ++ tailWord_2463265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463265).length < 2 ^ (prefixWord ++ tailWord_2463265).sum := by decide
  have hdescent : baseEnd_2463265 < baseStart_2463265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463276 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2463276 : Nat := 118140960795 + 2463276 * 2 ^ 59
def prefixEnd_2463276 : Nat := 4983230072969 + 3 ^ 40 * 2463276 * 2
def baseEnd_2463276 : Nat := 843229715123073103347737

theorem tailTrace_2463276 : CollatzResearch.WordTrace tailWord_2463276 prefixEnd_2463276 843229715123073103347737 := by
  unfold tailWord_2463276
  simp only [CollatzResearch.WordTrace]
  refine ⟨44921528311989610446372841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59895371082652813928497121 44921528311989610446372841)
  ·
    refine ⟨33691146233992207834779631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44921528311989610446372841 33691146233992207834779631)
    ·
      refine ⟨50536719350988311752169447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33691146233992207834779631 50536719350988311752169447)
      ·
        refine ⟨75805079026482467628254171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50536719350988311752169447 75805079026482467628254171)
        ·
          refine ⟨113707618539723701442381257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75805079026482467628254171 113707618539723701442381257)
          ·
            refine ⟨85280713904792776081785943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113707618539723701442381257 85280713904792776081785943)
            ·
              refine ⟨127921070857189164122678915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85280713904792776081785943 127921070857189164122678915)
              ·
                refine ⟨191881606285783746184018373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127921070857189164122678915 191881606285783746184018373)
                ·
                  refine ⟨35977801178584452409503445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191881606285783746184018373 35977801178584452409503445)
                  ·
                    refine ⟨843229715123073103347737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35977801178584452409503445 843229715123073103347737)
                    ·
                      rfl

theorem cell22_2463276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2463276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463276 prefixEnd_2463276 := by exact prefixLift 2463276
  have htrace : WordTrace (prefixWord ++ tailWord_2463276) baseStart_2463276 baseEnd_2463276 := by
    simpa [prefixWord, tailWord_2463276, baseEnd_2463276] using wordTrace_append hprefix tailTrace_2463276
  have hstable : (prefixWord ++ tailWord_2463276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463276).length < 2 ^ (prefixWord ++ tailWord_2463276).sum := by decide
  have hdescent : baseEnd_2463276 < baseStart_2463276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463391 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 5]
def baseStart_2463391 : Nat := 118140960795 + 2463391 * 2 ^ 59
def prefixEnd_2463391 : Nat := 4983230072969 + 3 ^ 40 * 2463391 * 2
def baseEnd_2463391 : Nat := 281089693991083712240795

theorem tailTrace_2463391 : CollatzResearch.WordTrace tailWord_2463391 prefixEnd_2463391 281089693991083712240795 := by
  unfold tailWord_2463391
  simp only [CollatzResearch.WordTrace]
  refine ⟨89847251018562595533182027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59898167345708397022121351 89847251018562595533182027)
  ·
    refine ⟨134770876527843893299773041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89847251018562595533182027 134770876527843893299773041)
    ·
      refine ⟨101078157395882919974829781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134770876527843893299773041 101078157395882919974829781)
      ·
        refine ⟨2369019313966005936910073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 101078157395882919974829781 2369019313966005936910073)
        ·
          refine ⟨1776764485474504452682555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369019313966005936910073 1776764485474504452682555)
          ·
            refine ⟨2665146728211756679023833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776764485474504452682555 2665146728211756679023833)
            ·
              refine ⟨1998860046158817509267875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665146728211756679023833 1998860046158817509267875)
              ·
                refine ⟨2998290069238226263901813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998860046158817509267875 2998290069238226263901813)
                ·
                  refine ⟨281089693991083712240795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998290069238226263901813 281089693991083712240795)
                  ·
                    rfl

theorem cell22_2463391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 5].length) (baseStart_2463391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463391 prefixEnd_2463391 := by exact prefixLift 2463391
  have htrace : WordTrace (prefixWord ++ tailWord_2463391) baseStart_2463391 baseEnd_2463391 := by
    simpa [prefixWord, tailWord_2463391, baseEnd_2463391] using wordTrace_append hprefix tailTrace_2463391
  have hstable : (prefixWord ++ tailWord_2463391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463391).length < 2 ^ (prefixWord ++ tailWord_2463391).sum := by decide
  have hdescent : baseEnd_2463391 < baseStart_2463391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463415 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2463415 : Nat := 118140960795 + 2463415 * 2 ^ 59
def prefixEnd_2463415 : Nat := 4983230072969 + 3 ^ 40 * 2463415 * 2
def baseEnd_2463415 : Nat := 843277297663723074122311

theorem tailTrace_2463415 : CollatzResearch.WordTrace tailWord_2463415 prefixEnd_2463415 843277297663723074122311 := by
  unfold tailWord_2463415
  simp only [CollatzResearch.WordTrace]
  refine ⟨89848126370475647632055699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59898750913650431754703799 89848126370475647632055699)
  ·
    refine ⟨134772189555713471448083549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89848126370475647632055699 134772189555713471448083549)
    ·
      refine ⟨50539571083392551793031331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134772189555713471448083549 50539571083392551793031331)
      ·
        refine ⟨75809356625088827689546997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50539571083392551793031331 75809356625088827689546997)
        ·
          refine ⟨7107127183602077595895031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75809356625088827689546997 7107127183602077595895031)
          ·
            refine ⟨10660690775403116393842547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7107127183602077595895031 10660690775403116393842547)
            ·
              refine ⟨15991036163104674590763821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10660690775403116393842547 15991036163104674590763821)
              ·
                refine ⟨5996638561164252971536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15991036163104674590763821 5996638561164252971536433)
                ·
                  refine ⟨4497478920873189728652325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5996638561164252971536433 4497478920873189728652325)
                  ·
                    refine ⟨843277297663723074122311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4497478920873189728652325 843277297663723074122311)
                    ·
                      rfl

theorem cell22_2463415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2463415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463415 prefixEnd_2463415 := by exact prefixLift 2463415
  have htrace : WordTrace (prefixWord ++ tailWord_2463415) baseStart_2463415 baseEnd_2463415 := by
    simpa [prefixWord, tailWord_2463415, baseEnd_2463415] using wordTrace_append hprefix tailTrace_2463415
  have hstable : (prefixWord ++ tailWord_2463415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463415).length < 2 ^ (prefixWord ++ tailWord_2463415).sum := by decide
  have hdescent : baseEnd_2463415 < baseStart_2463415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463434 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_2463434 : Nat := 118140960795 + 2463434 * 2 ^ 59
def prefixEnd_2463434 : Nat := 4983230072969 + 3 ^ 40 * 2463434 * 2
def baseEnd_2463434 : Nat := 843283801752013357897253

theorem tailTrace_2463434 : CollatzResearch.WordTrace tailWord_2463434 prefixEnd_2463434 843283801752013357897253 := by
  unfold tailWord_2463434
  simp only [CollatzResearch.WordTrace]
  refine ⟨22462204839351703469249339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59899212904937875917998237 22462204839351703469249339)
  ·
    refine ⟨33693307259027555203874009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22462204839351703469249339 33693307259027555203874009)
    ·
      refine ⟨25269980444270666402905507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33693307259027555203874009 25269980444270666402905507)
      ·
        refine ⟨37904970666405999604358261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25269980444270666402905507 37904970666405999604358261)
        ·
          refine ⟨3553590999975562462908587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37904970666405999604358261 3553590999975562462908587)
          ·
            refine ⟨5330386499963343694362881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553590999975562462908587 5330386499963343694362881)
            ·
              refine ⟨3997789874972507770772161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5330386499963343694362881 3997789874972507770772161)
              ·
                refine ⟨2998342406229380828079121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997789874972507770772161 2998342406229380828079121)
                ·
                  refine ⟨2248756804672035621059341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2998342406229380828079121 2248756804672035621059341)
                  ·
                    refine ⟨843283801752013357897253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248756804672035621059341 843283801752013357897253)
                    ·
                      rfl

theorem cell22_2463434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_2463434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463434 prefixEnd_2463434 := by exact prefixLift 2463434
  have htrace : WordTrace (prefixWord ++ tailWord_2463434) baseStart_2463434 baseEnd_2463434 := by
    simpa [prefixWord, tailWord_2463434, baseEnd_2463434] using wordTrace_append hprefix tailTrace_2463434
  have hstable : (prefixWord ++ tailWord_2463434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463434).length < 2 ^ (prefixWord ++ tailWord_2463434).sum := by decide
  have hdescent : baseEnd_2463434 < baseStart_2463434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463436 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 4]
def baseStart_2463436 : Nat := 118140960795 + 2463436 * 2 ^ 59
def prefixEnd_2463436 : Nat := 4983230072969 + 3 ^ 40 * 2463436 * 2
def baseEnd_2463436 : Nat := 281094828797628673115749

theorem tailTrace_2463436 : CollatzResearch.WordTrace tailWord_2463436 prefixEnd_2463436 281094828797628673115749 := by
  unfold tailWord_2463436
  simp only [CollatzResearch.WordTrace]
  refine ⟨44924446151699784109285081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59899261535599712145713441 44924446151699784109285081)
  ·
    refine ⟨33693334613774838081963811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44924446151699784109285081 33693334613774838081963811)
    ·
      refine ⟨50540001920662257122945717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33693334613774838081963811 50540001920662257122945717)
      ·
        refine ⟨4738125180062086605276161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50540001920662257122945717 4738125180062086605276161)
        ·
          refine ⟨3553593885046564953957121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4738125180062086605276161 3553593885046564953957121)
          ·
            refine ⟨2665195413784923715467841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553593885046564953957121 2665195413784923715467841)
            ·
              refine ⟨1998896560338692786600881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665195413784923715467841 1998896560338692786600881)
              ·
                refine ⟨1499172420254019589950661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998896560338692786600881 1499172420254019589950661)
                ·
                  refine ⟨281094828797628673115749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499172420254019589950661 281094828797628673115749)
                  ·
                    rfl

theorem cell22_2463436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_2463436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463436 prefixEnd_2463436 := by exact prefixLift 2463436
  have htrace : WordTrace (prefixWord ++ tailWord_2463436) baseStart_2463436 baseEnd_2463436 := by
    simpa [prefixWord, tailWord_2463436, baseEnd_2463436] using wordTrace_append hprefix tailTrace_2463436
  have hstable : (prefixWord ++ tailWord_2463436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463436).length < 2 ^ (prefixWord ++ tailWord_2463436).sum := by decide
  have hdescent : baseEnd_2463436 < baseStart_2463436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463492 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_2463492 : Nat := 118140960795 + 2463492 * 2 ^ 59
def prefixEnd_2463492 : Nat := 4983230072969 + 3 ^ 40 * 2463492 * 2
def baseEnd_2463492 : Nat := 281101218779106846649025

theorem tailTrace_2463492 : CollatzResearch.WordTrace tailWord_2463492 prefixEnd_2463492 281101218779106846649025 := by
  unfold tailWord_2463492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44925467395598344891304365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59900623194131126521739153 44925467395598344891304365)
  ·
    refine ⟨16847050273349379334239137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44925467395598344891304365 16847050273349379334239137)
    ·
      refine ⟨12635287705012034500679353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16847050273349379334239137 12635287705012034500679353)
      ·
        refine ⟨9476465778759025875509515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12635287705012034500679353 9476465778759025875509515)
        ·
          refine ⟨14214698668138538813264273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9476465778759025875509515 14214698668138538813264273)
          ·
            refine ⟨10661024001103904109948205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14214698668138538813264273 10661024001103904109948205)
            ·
              refine ⟨3997884000413964041230577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10661024001103904109948205 3997884000413964041230577)
              ·
                refine ⟨2998413000310473030922933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997884000413964041230577 2998413000310473030922933)
                ·
                  refine ⟨281101218779106846649025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998413000310473030922933 281101218779106846649025)
                  ·
                    rfl

theorem cell22_2463492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_2463492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463492 prefixEnd_2463492 := by exact prefixLift 2463492
  have htrace : WordTrace (prefixWord ++ tailWord_2463492) baseStart_2463492 baseEnd_2463492 := by
    simpa [prefixWord, tailWord_2463492, baseEnd_2463492] using wordTrace_append hprefix tailTrace_2463492
  have hstable : (prefixWord ++ tailWord_2463492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463492).length < 2 ^ (prefixWord ++ tailWord_2463492).sum := by decide
  have hdescent : baseEnd_2463492 < baseStart_2463492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463520 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_2463520 : Nat := 118140960795 + 2463520 * 2 ^ 59
def prefixEnd_2463520 : Nat := 4983230072969 + 3 ^ 40 * 2463520 * 2
def baseEnd_2463520 : Nat := 281104413769845933415663

theorem tailTrace_2463520 : CollatzResearch.WordTrace tailWord_2463520 prefixEnd_2463520 281104413769845933415663 := by
  unfold tailWord_2463520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44925978017547625282314007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59901304023396833709752009 44925978017547625282314007)
  ·
    refine ⟨67388967026321437923471011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44925978017547625282314007 67388967026321437923471011)
    ·
      refine ⟨101083450539482156885206517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67388967026321437923471011 101083450539482156885206517)
      ·
        refine ⟨9476573488076452207988111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101083450539482156885206517 9476573488076452207988111)
        ·
          refine ⟨14214860232114678311982167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9476573488076452207988111 14214860232114678311982167)
          ·
            refine ⟨21322290348172017467973251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14214860232114678311982167 21322290348172017467973251)
            ·
              refine ⟨31983435522258026201959877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21322290348172017467973251 31983435522258026201959877)
              ·
                refine ⟨5996894160423379912867477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31983435522258026201959877 5996894160423379912867477)
                ·
                  refine ⟨281104413769845933415663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5996894160423379912867477 281104413769845933415663)
                  ·
                    rfl

theorem cell22_2463520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_2463520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463520 prefixEnd_2463520 := by exact prefixLift 2463520
  have htrace : WordTrace (prefixWord ++ tailWord_2463520) baseStart_2463520 baseEnd_2463520 := by
    simpa [prefixWord, tailWord_2463520, baseEnd_2463520] using wordTrace_append hprefix tailTrace_2463520
  have hstable : (prefixWord ++ tailWord_2463520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463520).length < 2 ^ (prefixWord ++ tailWord_2463520).sum := by decide
  have hdescent : baseEnd_2463520 < baseStart_2463520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463569 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_2463569 : Nat := 118140960795 + 2463569 * 2 ^ 59
def prefixEnd_2463569 : Nat := 4983230072969 + 3 ^ 40 * 2463569 * 2
def baseEnd_2463569 : Nat := 843330015010918005771839

theorem tailTrace_2463569 : CollatzResearch.WordTrace tailWord_2463569 prefixEnd_2463569 843330015010918005771839 := by
  unfold tailWord_2463569
  simp only [CollatzResearch.WordTrace]
  refine ⟨89853743211917731933161761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59902495474611821288774507 89853743211917731933161761)
  ·
    refine ⟨67390307408938298949871321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89853743211917731933161761 67390307408938298949871321)
    ·
      refine ⟨50542730556703724212403491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67390307408938298949871321 50542730556703724212403491)
      ·
        refine ⟨75814095835055586318605237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50542730556703724212403491 75814095835055586318605237)
        ·
          refine ⟨7107571484536461217369241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75814095835055586318605237 7107571484536461217369241)
          ·
            refine ⟨5330678613402345913026931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7107571484536461217369241 5330678613402345913026931)
            ·
              refine ⟨7996017920103518869540397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330678613402345913026931 7996017920103518869540397)
              ·
                refine ⟨2998506720038819576077649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7996017920103518869540397 2998506720038819576077649)
                ·
                  refine ⟨2248880040029114682058237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2998506720038819576077649 2248880040029114682058237)
                  ·
                    refine ⟨843330015010918005771839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2248880040029114682058237 843330015010918005771839)
                    ·
                      rfl

theorem cell22_2463569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_2463569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463569 prefixEnd_2463569 := by exact prefixLift 2463569
  have htrace : WordTrace (prefixWord ++ tailWord_2463569) baseStart_2463569 baseEnd_2463569 := by
    simpa [prefixWord, tailWord_2463569, baseEnd_2463569] using wordTrace_append hprefix tailTrace_2463569
  have hstable : (prefixWord ++ tailWord_2463569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463569).length < 2 ^ (prefixWord ++ tailWord_2463569).sum := by decide
  have hdescent : baseEnd_2463569 < baseStart_2463569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463610 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_2463610 : Nat := 118140960795 + 2463610 * 2 ^ 59
def prefixEnd_2463610 : Nat := 4983230072969 + 3 ^ 40 * 2463610 * 2
def baseEnd_2463610 : Nat := 281114683382935855165571

theorem tailTrace_2463610 : CollatzResearch.WordTrace tailWord_2463610 prefixEnd_2463610 281114683382935855165571 := by
  unfold tailWord_2463610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22463809651192298983851071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59903492403179463956936189 22463809651192298983851071)
  ·
    refine ⟨33695714476788448475776607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22463809651192298983851071 33695714476788448475776607)
    ·
      refine ⟨50543571715182672713664911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33695714476788448475776607 50543571715182672713664911)
      ·
        refine ⟨75815357572774009070497367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50543571715182672713664911 75815357572774009070497367)
        ·
          refine ⟨113723036359161013605746051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75815357572774009070497367 113723036359161013605746051)
          ·
            refine ⟨170584554538741520408619077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113723036359161013605746051 170584554538741520408619077)
            ·
              refine ⟨31984603976014035076616077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170584554538741520408619077 31984603976014035076616077)
              ·
                refine ⟨11994226491005263153731029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31984603976014035076616077 11994226491005263153731029)
                ·
                  refine ⟨281114683382935855165571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11994226491005263153731029 281114683382935855165571)
                  ·
                    rfl

theorem cell22_2463610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_2463610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463610 prefixEnd_2463610 := by exact prefixLift 2463610
  have htrace : WordTrace (prefixWord ++ tailWord_2463610) baseStart_2463610 baseEnd_2463610 := by
    simpa [prefixWord, tailWord_2463610, baseEnd_2463610] using wordTrace_append hprefix tailTrace_2463610
  have hstable : (prefixWord ++ tailWord_2463610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463610).length < 2 ^ (prefixWord ++ tailWord_2463610).sum := by decide
  have hdescent : baseEnd_2463610 < baseStart_2463610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463672 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_2463672 : Nat := 118140960795 + 2463672 * 2 ^ 59
def prefixEnd_2463672 : Nat := 4983230072969 + 3 ^ 40 * 2463672 * 2
def baseEnd_2463672 : Nat := 281121758005286690148841

theorem tailTrace_2463672 : CollatzResearch.WordTrace tailWord_2463672 prefixEnd_2463672 281121758005286690148841 := by
  unfold tailWord_2463672
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928749965272290262080635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59904999953696387016107513 44928749965272290262080635)
  ·
    refine ⟨67393124947908435393120953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44928749965272290262080635 67393124947908435393120953)
    ·
      refine ⟨50544843710931326544840715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67393124947908435393120953 50544843710931326544840715)
      ·
        refine ⟨75817265566396989817261073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50544843710931326544840715 75817265566396989817261073)
        ·
          refine ⟨56862949174797742362945805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75817265566396989817261073 56862949174797742362945805)
          ·
            refine ⟨21323605940549153386104677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56862949174797742362945805 21323605940549153386104677)
            ·
              refine ⟨3998176113852966259894627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21323605940549153386104677 3998176113852966259894627)
              ·
                refine ⟨5997264170779449389841941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998176113852966259894627 5997264170779449389841941)
                ·
                  refine ⟨281121758005286690148841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5997264170779449389841941 281121758005286690148841)
                  ·
                    rfl

theorem cell22_2463672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_2463672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463672 prefixEnd_2463672 := by exact prefixLift 2463672
  have htrace : WordTrace (prefixWord ++ tailWord_2463672) baseStart_2463672 baseEnd_2463672 := by
    simpa [prefixWord, tailWord_2463672, baseEnd_2463672] using wordTrace_append hprefix tailTrace_2463672
  have hstable : (prefixWord ++ tailWord_2463672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463672).length < 2 ^ (prefixWord ++ tailWord_2463672).sum := by decide
  have hdescent : baseEnd_2463672 < baseStart_2463672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463779 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 5]
def baseStart_2463779 : Nat := 118140960795 + 2463779 * 2 ^ 59
def prefixEnd_2463779 : Nat := 4983230072969 + 3 ^ 40 * 2463779 * 2
def baseEnd_2463779 : Nat := 281133967434182486007065

theorem tailTrace_2463779 : CollatzResearch.WordTrace tailWord_2463779 prefixEnd_2463779 281133967434182486007065 := by
  unfold tailWord_2463779
  simp only [CollatzResearch.WordTrace]
  refine ⟨89861402541156937798306391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59907601694104625198870927 89861402541156937798306391)
  ·
    refine ⟨134792103811735406697459587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89861402541156937798306391 134792103811735406697459587)
    ·
      refine ⟨202188155717603110046189381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134792103811735406697459587 202188155717603110046189381)
      ·
        refine ⟨37910279197050583133660509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202188155717603110046189381 37910279197050583133660509)
        ·
          refine ⟨14216354698893968675122691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37910279197050583133660509 14216354698893968675122691)
          ·
            refine ⟨21324532048340953012684037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14216354698893968675122691 21324532048340953012684037)
            ·
              refine ⟨3998349759063928689878257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21324532048340953012684037 3998349759063928689878257)
              ·
                refine ⟨2998762319297946517408693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998349759063928689878257 2998762319297946517408693)
                ·
                  refine ⟨281133967434182486007065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998762319297946517408693 281133967434182486007065)
                  ·
                    rfl

theorem cell22_2463779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 5].length) (baseStart_2463779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463779 prefixEnd_2463779 := by exact prefixLift 2463779
  have htrace : WordTrace (prefixWord ++ tailWord_2463779) baseStart_2463779 baseEnd_2463779 := by
    simpa [prefixWord, tailWord_2463779, baseEnd_2463779] using wordTrace_append hprefix tailTrace_2463779
  have hstable : (prefixWord ++ tailWord_2463779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463779).length < 2 ^ (prefixWord ++ tailWord_2463779).sum := by decide
  have hdescent : baseEnd_2463779 < baseStart_2463779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463794 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2463794 : Nat := 118140960795 + 2463794 * 2 ^ 59
def prefixEnd_2463794 : Nat := 4983230072969 + 3 ^ 40 * 2463794 * 2
def baseEnd_2463794 : Nat := 843407037109092418896149

theorem tailTrace_2463794 : CollatzResearch.WordTrace tailWord_2463794 prefixEnd_2463794 843407037109092418896149 := by
  unfold tailWord_2463794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22465487409025648840025609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59907966424068396906734957 22465487409025648840025609)
  ·
    refine ⟨16849115556769236630019207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22465487409025648840025609 16849115556769236630019207)
    ·
      refine ⟨25273673335153854945028811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16849115556769236630019207 25273673335153854945028811)
      ·
        refine ⟨37910510002730782417543217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25273673335153854945028811 37910510002730782417543217)
        ·
          refine ⟨28432882502048086813157413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37910510002730782417543217 28432882502048086813157413)
          ·
            refine ⟨5331165469134016277467015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28432882502048086813157413 5331165469134016277467015)
            ·
              refine ⟨7996748203701024416200523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331165469134016277467015 7996748203701024416200523)
              ·
                refine ⟨11995122305551536624300785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7996748203701024416200523 11995122305551536624300785)
                ·
                  refine ⟨8996341729163652468225589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11995122305551536624300785 8996341729163652468225589)
                  ·
                    refine ⟨843407037109092418896149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8996341729163652468225589 843407037109092418896149)
                    ·
                      rfl

theorem cell22_2463794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2463794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463794 prefixEnd_2463794 := by exact prefixLift 2463794
  have htrace : WordTrace (prefixWord ++ tailWord_2463794) baseStart_2463794 baseEnd_2463794 := by
    simpa [prefixWord, tailWord_2463794, baseEnd_2463794] using wordTrace_append hprefix tailTrace_2463794
  have hstable : (prefixWord ++ tailWord_2463794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463794).length < 2 ^ (prefixWord ++ tailWord_2463794).sum := by decide
  have hdescent : baseEnd_2463794 < baseStart_2463794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463807 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 8]
def baseStart_2463807 : Nat := 118140960795 + 2463807 * 2 ^ 59
def prefixEnd_2463807 : Nat := 4983230072969 + 3 ^ 40 * 2463807 * 2
def baseEnd_2463807 : Nat := 281137162424921572773703

theorem tailTrace_2463807 : CollatzResearch.WordTrace tailWord_2463807 prefixEnd_2463807 281137162424921572773703 := by
  unfold tailWord_2463807
  simp only [CollatzResearch.WordTrace]
  refine ⟨89862423785055498580325675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59908282523370332386883783 89862423785055498580325675)
  ·
    refine ⟨134793635677583247870488513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89862423785055498580325675 134793635677583247870488513)
    ·
      refine ⟨101095226758187435902866385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134793635677583247870488513 101095226758187435902866385)
      ·
        refine ⟨75821420068640576927149789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101095226758187435902866385 75821420068640576927149789)
        ·
          refine ⟨28433032525740216347681171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75821420068640576927149789 28433032525740216347681171)
          ·
            refine ⟨42649548788610324521521757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28433032525740216347681171 42649548788610324521521757)
            ·
              refine ⟨15993580795728871695570659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42649548788610324521521757 15993580795728871695570659)
              ·
                refine ⟨23990371193593307543355989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15993580795728871695570659 23990371193593307543355989)
                ·
                  refine ⟨281137162424921572773703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23990371193593307543355989 281137162424921572773703)
                  ·
                    rfl

theorem cell22_2463807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_2463807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463807 prefixEnd_2463807 := by exact prefixLift 2463807
  have htrace : WordTrace (prefixWord ++ tailWord_2463807) baseStart_2463807 baseEnd_2463807 := by
    simpa [prefixWord, tailWord_2463807, baseEnd_2463807] using wordTrace_append hprefix tailTrace_2463807
  have hstable : (prefixWord ++ tailWord_2463807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463807).length < 2 ^ (prefixWord ++ tailWord_2463807).sum := by decide
  have hdescent : baseEnd_2463807 < baseStart_2463807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463830 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2463830 : Nat := 118140960795 + 2463830 * 2 ^ 59
def prefixEnd_2463830 : Nat := 4983230072969 + 3 ^ 40 * 2463830 * 2
def baseEnd_2463830 : Nat := 281139786881600108332013

theorem tailTrace_2463830 : CollatzResearch.WordTrace tailWord_2463830 prefixEnd_2463830 281139786881600108332013 := by
  unfold tailWord_2463830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616453916498260844275809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59908841775981449005608629 5616453916498260844275809)
  ·
    refine ⟨4212340437373695633206857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5616453916498260844275809 4212340437373695633206857)
    ·
      refine ⟨3159255328030271724905143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4212340437373695633206857 3159255328030271724905143)
      ·
        refine ⟨4738882992045407587357715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3159255328030271724905143 4738882992045407587357715)
        ·
          refine ⟨7108324488068111381036573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4738882992045407587357715 7108324488068111381036573)
          ·
            refine ⟨2665621683025541767888715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7108324488068111381036573 2665621683025541767888715)
            ·
              refine ⟨3998432524538312651833073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665621683025541767888715 3998432524538312651833073)
              ·
                refine ⟨2998824393403734488874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998432524538312651833073 2998824393403734488874805)
                ·
                  refine ⟨281139786881600108332013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998824393403734488874805 281139786881600108332013)
                  ·
                    rfl

theorem cell22_2463830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2463830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463830 prefixEnd_2463830 := by exact prefixLift 2463830
  have htrace : WordTrace (prefixWord ++ tailWord_2463830) baseStart_2463830 baseEnd_2463830 := by
    simpa [prefixWord, tailWord_2463830, baseEnd_2463830] using wordTrace_append hprefix tailTrace_2463830
  have hstable : (prefixWord ++ tailWord_2463830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463830).length < 2 ^ (prefixWord ++ tailWord_2463830).sum := by decide
  have hdescent : baseEnd_2463830 < baseStart_2463830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463854 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2463854 : Nat := 118140960795 + 2463854 * 2 ^ 59
def prefixEnd_2463854 : Nat := 4983230072969 + 3 ^ 40 * 2463854 * 2
def baseEnd_2463854 : Nat := 843427576335272262395965

theorem tailTrace_2463854 : CollatzResearch.WordTrace tailWord_2463854 prefixEnd_2463854 843427576335272262395965 := by
  unfold tailWord_2463854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11233017251985653200910827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59909425343923483738191077 11233017251985653200910827)
  ·
    refine ⟨16849525877978479801366241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11233017251985653200910827 16849525877978479801366241)
    ·
      refine ⟨12637144408483859851024681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16849525877978479801366241 12637144408483859851024681)
      ·
        refine ⟨9477858306362894888268511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12637144408483859851024681 9477858306362894888268511)
        ·
          refine ⟨14216787459544342332402767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9477858306362894888268511 14216787459544342332402767)
          ·
            refine ⟨21325181189316513498604151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14216787459544342332402767 21325181189316513498604151)
            ·
              refine ⟨31987771783974770247906227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21325181189316513498604151 31987771783974770247906227)
              ·
                refine ⟨47981657675962155371859341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31987771783974770247906227 47981657675962155371859341)
                ·
                  refine ⟨17993121628485808264447253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47981657675962155371859341 17993121628485808264447253)
                  ·
                    refine ⟨843427576335272262395965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17993121628485808264447253 843427576335272262395965)
                    ·
                      rfl

theorem cell22_2463854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2463854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463854 prefixEnd_2463854 := by exact prefixLift 2463854
  have htrace : WordTrace (prefixWord ++ tailWord_2463854) baseStart_2463854 baseEnd_2463854 := by
    simpa [prefixWord, tailWord_2463854, baseEnd_2463854] using wordTrace_append hprefix tailTrace_2463854
  have hstable : (prefixWord ++ tailWord_2463854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463854).length < 2 ^ (prefixWord ++ tailWord_2463854).sum := by decide
  have hdescent : baseEnd_2463854 < baseStart_2463854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463856 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_2463856 : Nat := 118140960795 + 2463856 * 2 ^ 59
def prefixEnd_2463856 : Nat := 4983230072969 + 3 ^ 40 * 2463856 * 2
def baseEnd_2463856 : Nat := 843428260976144923845959

theorem tailTrace_2463856 : CollatzResearch.WordTrace tailWord_2463856 prefixEnd_2463856 843428260976144923845959 := by
  unfold tailWord_2463856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44932105480938989974429711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59909473974585319965906281 44932105480938989974429711)
  ·
    refine ⟨67398158221408484961644567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44932105480938989974429711 67398158221408484961644567)
    ·
      refine ⟨101097237332112727442466851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67398158221408484961644567 101097237332112727442466851)
      ·
        refine ⟨151645855998169091163700277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101097237332112727442466851 151645855998169091163700277)
        ·
          refine ⟨14216798999828352296596901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151645855998169091163700277 14216798999828352296596901)
          ·
            refine ⟨2665649812467816055611919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14216798999828352296596901 2665649812467816055611919)
            ·
              refine ⟨3998474718701724083417879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665649812467816055611919 3998474718701724083417879)
              ·
                refine ⟨5997712078052586125126819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998474718701724083417879 5997712078052586125126819)
                ·
                  refine ⟨8996568117078879187690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5997712078052586125126819 8996568117078879187690229)
                  ·
                    refine ⟨843428260976144923845959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8996568117078879187690229 843428260976144923845959)
                    ·
                      rfl

theorem cell22_2463856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_2463856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463856 prefixEnd_2463856 := by exact prefixLift 2463856
  have htrace : WordTrace (prefixWord ++ tailWord_2463856) baseStart_2463856 baseEnd_2463856 := by
    simpa [prefixWord, tailWord_2463856, baseEnd_2463856] using wordTrace_append hprefix tailTrace_2463856
  have hstable : (prefixWord ++ tailWord_2463856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463856).length < 2 ^ (prefixWord ++ tailWord_2463856).sum := by decide
  have hdescent : baseEnd_2463856 < baseStart_2463856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463869 : List Nat := [1, 4, 1, 1, 3, 3, 1, 8]
def baseStart_2463869 : Nat := 118140960795 + 2463869 * 2 ^ 59
def prefixEnd_2463869 : Nat := 4983230072969 + 3 ^ 40 * 2463869 * 2
def baseEnd_2463869 : Nat := 93714745682424135918991

theorem tailTrace_2463869 : CollatzResearch.WordTrace tailWord_2463869 prefixEnd_2463869 93714745682424135918991 := by
  unfold tailWord_2463869
  simp only [CollatzResearch.WordTrace]
  refine ⟨89864685110830883169082661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59909790073887255446055107 89864685110830883169082661)
  ·
    refine ⟨16849628458280790594202999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89864685110830883169082661 16849628458280790594202999)
    ·
      refine ⟨25274442687421185891304499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16849628458280790594202999 25274442687421185891304499)
      ·
        refine ⟨37911664031131778836956749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25274442687421185891304499 37911664031131778836956749)
        ·
          refine ⟨14216874011674417063858781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37911664031131778836956749 14216874011674417063858781)
          ·
            refine ⟨5331327754377906398947043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14216874011674417063858781 5331327754377906398947043)
            ·
              refine ⟨7996991631566859598420565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331327754377906398947043 7996991631566859598420565)
              ·
                refine ⟨93714745682424135918991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7996991631566859598420565 93714745682424135918991)
                ·
                  rfl

theorem cell22_2463869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 8].length) (baseStart_2463869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463869 prefixEnd_2463869 := by exact prefixLift 2463869
  have htrace : WordTrace (prefixWord ++ tailWord_2463869) baseStart_2463869 baseEnd_2463869 := by
    simpa [prefixWord, tailWord_2463869, baseEnd_2463869] using wordTrace_append hprefix tailTrace_2463869
  have hstable : (prefixWord ++ tailWord_2463869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463869).length < 2 ^ (prefixWord ++ tailWord_2463869).sum := by decide
  have hdescent : baseEnd_2463869 < baseStart_2463869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463886 : List Nat := [4, 1, 1, 3, 3, 2, 8]
def baseStart_2463886 : Nat := 118140960795 + 2463886 * 2 ^ 59
def prefixEnd_2463886 : Nat := 4983230072969 + 3 ^ 40 * 2463886 * 2
def baseEnd_2463886 : Nat := 31238464095897586873921

theorem tailTrace_2463886 : CollatzResearch.WordTrace tailWord_2463886 prefixEnd_2463886 31238464095897586873921 := by
  unfold tailWord_2463886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11233163143971161884056439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59910203434512863381634341 11233163143971161884056439)
  ·
    refine ⟨16849744715956742826084659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11233163143971161884056439 16849744715956742826084659)
    ·
      refine ⟨25274617073935114239126989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16849744715956742826084659 25274617073935114239126989)
      ·
        refine ⟨9477981402725667839672621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25274617073935114239126989 9477981402725667839672621)
        ·
          refine ⟨3554243026022125439877233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9477981402725667839672621 3554243026022125439877233)
          ·
            refine ⟨2665682269516594079907925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3554243026022125439877233 2665682269516594079907925)
            ·
              refine ⟨31238464095897586873921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2665682269516594079907925 31238464095897586873921)
              ·
                rfl

theorem cell22_2463886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 8].length) (baseStart_2463886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463886 prefixEnd_2463886 := by exact prefixLift 2463886
  have htrace : WordTrace (prefixWord ++ tailWord_2463886) baseStart_2463886 baseEnd_2463886 := by
    simpa [prefixWord, tailWord_2463886, baseEnd_2463886] using wordTrace_append hprefix tailTrace_2463886
  have hstable : (prefixWord ++ tailWord_2463886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463886).length < 2 ^ (prefixWord ++ tailWord_2463886).sum := by decide
  have hdescent : baseEnd_2463886 < baseStart_2463886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463892 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2463892 : Nat := 118140960795 + 2463892 * 2 ^ 59
def prefixEnd_2463892 : Nat := 4983230072969 + 3 ^ 40 * 2463892 * 2
def baseEnd_2463892 : Nat := 281146861503950943315283

theorem tailTrace_2463892 : CollatzResearch.WordTrace tailWord_2463892 prefixEnd_2463892 281146861503950943315283 := by
  unfold tailWord_2463892
  simp only [CollatzResearch.WordTrace]
  refine ⟨44932761994873779048584965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59910349326498372064779953 44932761994873779048584965)
  ·
    refine ⟨8424892874038833571609681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44932761994873779048584965 8424892874038833571609681)
    ·
      refine ⟨6318669655529125178707261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8424892874038833571609681 6318669655529125178707261)
      ·
        refine ⟨2369501120823421942015223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6318669655529125178707261 2369501120823421942015223)
        ·
          refine ⟨3554251681235132913022835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369501120823421942015223 3554251681235132913022835)
          ·
            refine ⟨5331377521852699369534253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554251681235132913022835 5331377521852699369534253)
            ·
              refine ⟨1999266570694762263575345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5331377521852699369534253 1999266570694762263575345)
              ·
                refine ⟨1499449928021071697681509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999266570694762263575345 1499449928021071697681509)
                ·
                  refine ⟨281146861503950943315283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499449928021071697681509 281146861503950943315283)
                  ·
                    rfl

theorem cell22_2463892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2463892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463892 prefixEnd_2463892 := by exact prefixLift 2463892
  have htrace : WordTrace (prefixWord ++ tailWord_2463892) baseStart_2463892 baseEnd_2463892 := by
    simpa [prefixWord, tailWord_2463892, baseEnd_2463892] using wordTrace_append hprefix tailTrace_2463892
  have hstable : (prefixWord ++ tailWord_2463892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463892).length < 2 ^ (prefixWord ++ tailWord_2463892).sum := by decide
  have hdescent : baseEnd_2463892 < baseStart_2463892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463959 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 6]
def baseStart_2463959 : Nat := 118140960795 + 2463959 * 2 ^ 59
def prefixEnd_2463959 : Nat := 4983230072969 + 3 ^ 40 * 2463959 * 2
def baseEnd_2463959 : Nat := 281154506660362329506881

theorem tailTrace_2463959 : CollatzResearch.WordTrace tailWord_2463959 prefixEnd_2463959 281154506660362329506881 := by
  unfold tailWord_2463959
  simp only [CollatzResearch.WordTrace]
  refine ⟨89867967680504828539858931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59911978453669885693239287 89867967680504828539858931)
  ·
    refine ⟨134801951520757242809788397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89867967680504828539858931 134801951520757242809788397)
    ·
      refine ⟨50550731820283966053670649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134801951520757242809788397 50550731820283966053670649)
      ·
        refine ⟨37913048865212974540252987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50550731820283966053670649 37913048865212974540252987)
        ·
          refine ⟨56869573297819461810379481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37913048865212974540252987 56869573297819461810379481)
          ·
            refine ⟨42652179973364596357784611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56869573297819461810379481 42652179973364596357784611)
            ·
              refine ⟨63978269960046894536676917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42652179973364596357784611 63978269960046894536676917)
              ·
                refine ⟨5997962808754396362813461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63978269960046894536676917 5997962808754396362813461)
                ·
                  refine ⟨281154506660362329506881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5997962808754396362813461 281154506660362329506881)
                  ·
                    rfl

theorem cell22_2463959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 6].length) (baseStart_2463959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463959 prefixEnd_2463959 := by exact prefixLift 2463959
  have htrace : WordTrace (prefixWord ++ tailWord_2463959) baseStart_2463959 baseEnd_2463959 := by
    simpa [prefixWord, tailWord_2463959, baseEnd_2463959] using wordTrace_append hprefix tailTrace_2463959
  have hstable : (prefixWord ++ tailWord_2463959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463959).length < 2 ^ (prefixWord ++ tailWord_2463959).sum := by decide
  have hdescent : baseEnd_2463959 < baseStart_2463959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2463976 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_2463976 : Nat := 118140960795 + 2463976 * 2 ^ 59
def prefixEnd_2463976 : Nat := 4983230072969 + 3 ^ 40 * 2463976 * 2
def baseEnd_2463976 : Nat := 281156446476168203615197

theorem tailTrace_2463976 : CollatzResearch.WordTrace tailWord_2463976 prefixEnd_2463976 281156446476168203615197 := by
  unfold tailWord_2463976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44934293860721620221613891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59912391814295493628818521 44934293860721620221613891)
  ·
    refine ⟨67401440791082430332420837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44934293860721620221613891 67401440791082430332420837)
    ·
      refine ⟨12637770148327955687328907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67401440791082430332420837 12637770148327955687328907)
      ·
        refine ⟨18956655222491933530993361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12637770148327955687328907 18956655222491933530993361)
        ·
          refine ⟨14217491416868950148245021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18956655222491933530993361 14217491416868950148245021)
          ·
            refine ⟨5331559281325856305591883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14217491416868950148245021 5331559281325856305591883)
            ·
              refine ⟨7997338921988784458387825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331559281325856305591883 7997338921988784458387825)
              ·
                refine ⟨5998004191491588343790869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7997338921988784458387825 5998004191491588343790869)
                ·
                  refine ⟨281156446476168203615197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5998004191491588343790869 281156446476168203615197)
                  ·
                    rfl

theorem cell22_2463976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_2463976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2463976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2463976 prefixEnd_2463976 := by exact prefixLift 2463976
  have htrace : WordTrace (prefixWord ++ tailWord_2463976) baseStart_2463976 baseEnd_2463976 := by
    simpa [prefixWord, tailWord_2463976, baseEnd_2463976] using wordTrace_append hprefix tailTrace_2463976
  have hstable : (prefixWord ++ tailWord_2463976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2463976).length < 2 ^ (prefixWord ++ tailWord_2463976).sum := by decide
  have hdescent : baseEnd_2463976 < baseStart_2463976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2463976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464008 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_2464008 : Nat := 118140960795 + 2464008 * 2 ^ 59
def prefixEnd_2464008 : Nat := 4983230072969 + 3 ^ 40 * 2464008 * 2
def baseEnd_2464008 : Nat := 843480293682467194045493

theorem tailTrace_2464008 : CollatzResearch.WordTrace tailWord_2464008 prefixEnd_2464008 843480293682467194045493 := by
  unfold tailWord_2464008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44934877428663654954196339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59913169904884873272261785 44934877428663654954196339)
  ·
    refine ⟨67402316142995482431294509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44934877428663654954196339 67402316142995482431294509)
    ·
      refine ⟨25275868553623305911735441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67402316142995482431294509 25275868553623305911735441)
      ·
        refine ⟨18956901415217479433801581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25275868553623305911735441 18956901415217479433801581)
        ·
          refine ⟨7108838030706554787675593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18956901415217479433801581 7108838030706554787675593)
          ·
            refine ⟨5331628523029916090756695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7108838030706554787675593 5331628523029916090756695)
            ·
              refine ⟨7997442784544874136135043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331628523029916090756695 7997442784544874136135043)
              ·
                refine ⟨11996164176817311204202565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7997442784544874136135043 11996164176817311204202565)
                ·
                  refine ⟨2249280783153245850787981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11996164176817311204202565 2249280783153245850787981)
                  ·
                    refine ⟨843480293682467194045493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2249280783153245850787981 843480293682467194045493)
                    ·
                      rfl

theorem cell22_2464008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_2464008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464008 prefixEnd_2464008 := by exact prefixLift 2464008
  have htrace : WordTrace (prefixWord ++ tailWord_2464008) baseStart_2464008 baseEnd_2464008 := by
    simpa [prefixWord, tailWord_2464008, baseEnd_2464008] using wordTrace_append hprefix tailTrace_2464008
  have hstable : (prefixWord ++ tailWord_2464008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464008).length < 2 ^ (prefixWord ++ tailWord_2464008).sum := by decide
  have hdescent : baseEnd_2464008 < baseStart_2464008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464177 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_2464177 : Nat := 118140960795 + 2464177 * 2 ^ 59
def prefixEnd_2464177 : Nat := 4983230072969 + 3 ^ 40 * 2464177 * 2
def baseEnd_2464177 : Nat := 843538145836207086569975

theorem tailTrace_2464177 : CollatzResearch.WordTrace tailWord_2464177 prefixEnd_2464177 843538145836207086569975 := by
  unfold tailWord_2464177
  simp only [CollatzResearch.WordTrace]
  refine ⟨89875918793715051771294785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59917279195810034514196523 89875918793715051771294785)
  ·
    refine ⟨67406939095286288828471089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89875918793715051771294785 67406939095286288828471089)
    ·
      refine ⟨50555204321464716621353317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67406939095286288828471089 50555204321464716621353317)
      ·
        refine ⟨9479100810274634366503747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50555204321464716621353317 9479100810274634366503747)
        ·
          refine ⟨14218651215411951549755621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9479100810274634366503747 14218651215411951549755621)
          ·
            refine ⟨2665997102889740915579179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14218651215411951549755621 2665997102889740915579179)
            ·
              refine ⟨3998995654334611373368769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665997102889740915579179 3998995654334611373368769)
              ·
                refine ⟨2999246740750958530026577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998995654334611373368769 2999246740750958530026577)
                ·
                  refine ⟨2249435055563218897519933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999246740750958530026577 2249435055563218897519933)
                  ·
                    refine ⟨843538145836207086569975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2249435055563218897519933 843538145836207086569975)
                    ·
                      rfl

theorem cell22_2464177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_2464177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464177 prefixEnd_2464177 := by exact prefixLift 2464177
  have htrace : WordTrace (prefixWord ++ tailWord_2464177) baseStart_2464177 baseEnd_2464177 := by
    simpa [prefixWord, tailWord_2464177, baseEnd_2464177] using wordTrace_append hprefix tailTrace_2464177
  have hstable : (prefixWord ++ tailWord_2464177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464177).length < 2 ^ (prefixWord ++ tailWord_2464177).sum := by decide
  have hdescent : baseEnd_2464177 < baseStart_2464177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464186 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_2464186 : Nat := 118140960795 + 2464186 * 2 ^ 59
def prefixEnd_2464186 : Nat := 4983230072969 + 3 ^ 40 * 2464186 * 2
def baseEnd_2464186 : Nat := 843541226720134063094947

theorem tailTrace_2464186 : CollatzResearch.WordTrace tailWord_2464186 prefixEnd_2464186 843541226720134063094947 := by
  unfold tailWord_2464186
  simp only [CollatzResearch.WordTrace]
  refine ⟨22469061762670611577093103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59917498033788297538914941 22469061762670611577093103)
  ·
    refine ⟨33703592644005917365639655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22469061762670611577093103 33703592644005917365639655)
    ·
      refine ⟨50555388966008876048459483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33703592644005917365639655 50555388966008876048459483)
      ·
        refine ⟨75833083449013314072689225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50555388966008876048459483 75833083449013314072689225)
        ·
          refine ⟨56874812586759985554516919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75833083449013314072689225 56874812586759985554516919)
          ·
            refine ⟨85312218880139978331775379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56874812586759985554516919 85312218880139978331775379)
            ·
              refine ⟨127968328320209967497663069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85312218880139978331775379 127968328320209967497663069)
              ·
                refine ⟨47988123120078737811623651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127968328320209967497663069 47988123120078737811623651)
                ·
                  refine ⟨71982184680118106717435477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47988123120078737811623651 71982184680118106717435477)
                  ·
                    refine ⟨843541226720134063094947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71982184680118106717435477 843541226720134063094947)
                    ·
                      rfl

theorem cell22_2464186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_2464186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464186 prefixEnd_2464186 := by exact prefixLift 2464186
  have htrace : WordTrace (prefixWord ++ tailWord_2464186) baseStart_2464186 baseEnd_2464186 := by
    simpa [prefixWord, tailWord_2464186, baseEnd_2464186] using wordTrace_append hprefix tailTrace_2464186
  have hstable : (prefixWord ++ tailWord_2464186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464186).length < 2 ^ (prefixWord ++ tailWord_2464186).sum := by decide
  have hdescent : baseEnd_2464186 < baseStart_2464186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464248 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_2464248 : Nat := 118140960795 + 2464248 * 2 ^ 59
def prefixEnd_2464248 : Nat := 4983230072969 + 3 ^ 40 * 2464248 * 2
def baseEnd_2464248 : Nat := 843562450587186568044757

theorem tailTrace_2464248 : CollatzResearch.WordTrace tailWord_2464248 prefixEnd_2464248 843562450587186568044757 := by
  unfold tailWord_2464248
  simp only [CollatzResearch.WordTrace]
  refine ⟨44939254188228915448564699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59919005584305220598086265 44939254188228915448564699)
  ·
    refine ⟨67408881282343373172847049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44939254188228915448564699 67408881282343373172847049)
    ·
      refine ⟨50556660961757529879635287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67408881282343373172847049 50556660961757529879635287)
      ·
        refine ⟨75834991442636294819452931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50556660961757529879635287 75834991442636294819452931)
        ·
          refine ⟨113752487163954442229179397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75834991442636294819452931 113752487163954442229179397)
          ·
            refine ⟨21328591343241457917971137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113752487163954442229179397 21328591343241457917971137)
            ·
              refine ⟨15996443507431093438478353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21328591343241457917971137 15996443507431093438478353)
              ·
                refine ⟨11997332630573320078858765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15996443507431093438478353 11997332630573320078858765)
                ·
                  refine ⟨4498999736464995029572037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11997332630573320078858765 4498999736464995029572037)
                  ·
                    refine ⟨843562450587186568044757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4498999736464995029572037 843562450587186568044757)
                    ·
                      rfl

theorem cell22_2464248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_2464248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464248 prefixEnd_2464248 := by exact prefixLift 2464248
  have htrace : WordTrace (prefixWord ++ tailWord_2464248) baseStart_2464248 baseEnd_2464248 := by
    simpa [prefixWord, tailWord_2464248, baseEnd_2464248] using wordTrace_append hprefix tailTrace_2464248
  have hstable : (prefixWord ++ tailWord_2464248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464248).length < 2 ^ (prefixWord ++ tailWord_2464248).sum := by decide
  have hdescent : baseEnd_2464248 < baseStart_2464248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464325 : List Nat := [1, 3, 1, 1, 1, 6, 3, 6]
def baseStart_2464325 : Nat := 118140960795 + 2464325 * 2 ^ 59
def prefixEnd_2464325 : Nat := 4983230072969 + 3 ^ 40 * 2464325 * 2
def baseEnd_2464325 : Nat := 93732089917864892652169

theorem tailTrace_2464325 : CollatzResearch.WordTrace tailWord_2464325 prefixEnd_2464325 93732089917864892652169 := by
  unfold tailWord_2464325
  simp only [CollatzResearch.WordTrace]
  refine ⟨89881316797178873047682429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59920877864785915365121619 89881316797178873047682429)
  ·
    refine ⟨33705493798942077392880911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89881316797178873047682429 33705493798942077392880911)
    ·
      refine ⟨50558240698413116089321367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33705493798942077392880911 50558240698413116089321367)
      ·
        refine ⟨75837361047619674133982051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50558240698413116089321367 75837361047619674133982051)
        ·
          refine ⟨113756041571429511200973077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75837361047619674133982051 113756041571429511200973077)
          ·
            refine ⟨5332314448660758337545613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113756041571429511200973077 5332314448660758337545613)
            ·
              refine ⟨1999617918247784376579605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5332314448660758337545613 1999617918247784376579605)
              ·
                refine ⟨93732089917864892652169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1999617918247784376579605 93732089917864892652169)
                ·
                  rfl

theorem cell22_2464325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 6].length) (baseStart_2464325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464325 prefixEnd_2464325 := by exact prefixLift 2464325
  have htrace : WordTrace (prefixWord ++ tailWord_2464325) baseStart_2464325 baseEnd_2464325 := by
    simpa [prefixWord, tailWord_2464325, baseEnd_2464325] using wordTrace_append hprefix tailTrace_2464325
  have hstable : (prefixWord ++ tailWord_2464325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464325).length < 2 ^ (prefixWord ++ tailWord_2464325).sum := by decide
  have hdescent : baseEnd_2464325 < baseStart_2464325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464327 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2464327 : Nat := 118140960795 + 2464327 * 2 ^ 59
def prefixEnd_2464327 : Nat := 4983230072969 + 3 ^ 40 * 2464327 * 2
def baseEnd_2464327 : Nat := 843589493901656695319515

theorem tailTrace_2464327 : CollatzResearch.WordTrace tailWord_2464327 prefixEnd_2464327 843589493901656695319515 := by
  unfold tailWord_2464327
  simp only [CollatzResearch.WordTrace]
  refine ⟨89881389743171627389255235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59920926495447751592836823 89881389743171627389255235)
  ·
    refine ⟨134822084614757441083882853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89881389743171627389255235 134822084614757441083882853)
    ·
      refine ⟨25279140865267020203228035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134822084614757441083882853 25279140865267020203228035)
      ·
        refine ⟨37918711297900530304842053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25279140865267020203228035 37918711297900530304842053)
        ·
          refine ⟨7109758368356349432157885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37918711297900530304842053 7109758368356349432157885)
          ·
            refine ⟨2666159388133631037059207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7109758368356349432157885 2666159388133631037059207)
            ·
              refine ⟨3999239082200446555588811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666159388133631037059207 3999239082200446555588811)
              ·
                refine ⟨5998858623300669833383217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999239082200446555588811 5998858623300669833383217)
                ·
                  refine ⟨4499143967475502375037413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5998858623300669833383217 4499143967475502375037413)
                  ·
                    refine ⟨843589493901656695319515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4499143967475502375037413 843589493901656695319515)
                    ·
                      rfl

theorem cell22_2464327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2464327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464327 prefixEnd_2464327 := by exact prefixLift 2464327
  have htrace : WordTrace (prefixWord ++ tailWord_2464327) baseStart_2464327 baseEnd_2464327 := by
    simpa [prefixWord, tailWord_2464327, baseEnd_2464327] using wordTrace_append hprefix tailTrace_2464327
  have hstable : (prefixWord ++ tailWord_2464327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464327).length < 2 ^ (prefixWord ++ tailWord_2464327).sum := by decide
  have hdescent : baseEnd_2464327 < baseStart_2464327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464460 : List Nat := [2, 2, 1, 5, 1, 11]
def baseStart_2464460 : Nat := 118140960795 + 2464460 * 2 ^ 59
def prefixEnd_2464460 : Nat := 4983230072969 + 3 ^ 40 * 2464460 * 2
def baseEnd_2464460 : Nat := 10415247191601094836347

theorem tailTrace_2464460 : CollatzResearch.WordTrace tailWord_2464460 prefixEnd_2464460 10415247191601094836347 := by
  unfold tailWord_2464460
  simp only [CollatzResearch.WordTrace]
  refine ⟨44943120325844895551923417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59924160434459860735897889 44943120325844895551923417)
  ·
    refine ⟨33707340244383671663942563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44943120325844895551923417 33707340244383671663942563)
    ·
      refine ⟨50561010366575507495913845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33707340244383671663942563 50561010366575507495913845)
      ·
        refine ⟨4740094721866453827741923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50561010366575507495913845 4740094721866453827741923)
        ·
          refine ⟨7110142082799680741612885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740094721866453827741923 7110142082799680741612885)
          ·
            refine ⟨10415247191601094836347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7110142082799680741612885 10415247191601094836347)
            ·
              rfl

theorem cell22_2464460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 11].length) (baseStart_2464460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464460 prefixEnd_2464460 := by exact prefixLift 2464460
  have htrace : WordTrace (prefixWord ++ tailWord_2464460) baseStart_2464460 baseEnd_2464460 := by
    simpa [prefixWord, tailWord_2464460, baseEnd_2464460] using wordTrace_append hprefix tailTrace_2464460
  have hstable : (prefixWord ++ tailWord_2464460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464460).length < 2 ^ (prefixWord ++ tailWord_2464460).sum := by decide
  have hdescent : baseEnd_2464460 < baseStart_2464460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464462 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2464462 : Nat := 118140960795 + 2464462 * 2 ^ 59
def prefixEnd_2464462 : Nat := 4983230072969 + 3 ^ 40 * 2464462 * 2
def baseEnd_2464462 : Nat := 843635707160561343194101

theorem tailTrace_2464462 : CollatzResearch.WordTrace tailWord_2464462 prefixEnd_2464462 843635707160561343194101 := by
  unfold tailWord_2464462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235789199710318180677455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59924209065121696963613093 11235789199710318180677455)
  ·
    refine ⟨16853683799565477271016183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11235789199710318180677455 16853683799565477271016183)
    ·
      refine ⟨25280525699348215906524275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16853683799565477271016183 25280525699348215906524275)
      ·
        refine ⟨37920788549022323859786413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25280525699348215906524275 37920788549022323859786413)
        ·
          refine ⟨14220295705883371447419905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37920788549022323859786413 14220295705883371447419905)
          ·
            refine ⟨10665221779412528585564929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14220295705883371447419905 10665221779412528585564929)
            ·
              refine ⟨7998916334559396439173697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10665221779412528585564929 7998916334559396439173697)
              ·
                refine ⟨5999187250919547329380273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7998916334559396439173697 5999187250919547329380273)
                ·
                  refine ⟨4499390438189660497035205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5999187250919547329380273 4499390438189660497035205)
                  ·
                    refine ⟨843635707160561343194101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4499390438189660497035205 843635707160561343194101)
                    ·
                      rfl

theorem cell22_2464462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2464462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464462 prefixEnd_2464462 := by exact prefixLift 2464462
  have htrace : WordTrace (prefixWord ++ tailWord_2464462) baseStart_2464462 baseEnd_2464462 := by
    simpa [prefixWord, tailWord_2464462, baseEnd_2464462] using wordTrace_append hprefix tailTrace_2464462
  have hstable : (prefixWord ++ tailWord_2464462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464462).length < 2 ^ (prefixWord ++ tailWord_2464462).sum := by decide
  have hdescent : baseEnd_2464462 < baseStart_2464462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464490 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2464490 : Nat := 118140960795 + 2464490 * 2 ^ 59
def prefixEnd_2464490 : Nat := 4983230072969 + 3 ^ 40 * 2464490 * 2
def baseEnd_2464490 : Nat := 843645292132778603494015

theorem tailTrace_2464490 : CollatzResearch.WordTrace tailWord_2464490 prefixEnd_2464490 843645292132778603494015 := by
  unfold tailWord_2464490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22471833710395276556859731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59924889894387404151625949 22471833710395276556859731)
  ·
    refine ⟨33707750565592914835289597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22471833710395276556859731 33707750565592914835289597)
    ·
      refine ⟨12640406462097343063233599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33707750565592914835289597 12640406462097343063233599)
      ·
        refine ⟨18960609693146014594850399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12640406462097343063233599 18960609693146014594850399)
        ·
          refine ⟨28440914539719021892275599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18960609693146014594850399 28440914539719021892275599)
          ·
            refine ⟨42661371809578532838413399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28440914539719021892275599 42661371809578532838413399)
            ·
              refine ⟨63992057714367799257620099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42661371809578532838413399 63992057714367799257620099)
              ·
                refine ⟨95988086571551698886430149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63992057714367799257620099 95988086571551698886430149)
                ·
                  refine ⟨17997766232165943541205653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95988086571551698886430149 17997766232165943541205653)
                  ·
                    refine ⟨843645292132778603494015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17997766232165943541205653 843645292132778603494015)
                    ·
                      rfl

theorem cell22_2464490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2464490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464490 prefixEnd_2464490 := by exact prefixLift 2464490
  have htrace : WordTrace (prefixWord ++ tailWord_2464490) baseStart_2464490 baseEnd_2464490 := by
    simpa [prefixWord, tailWord_2464490, baseEnd_2464490] using wordTrace_append hprefix tailTrace_2464490
  have hstable : (prefixWord ++ tailWord_2464490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464490).length < 2 ^ (prefixWord ++ tailWord_2464490).sum := by decide
  have hdescent : baseEnd_2464490 < baseStart_2464490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464597 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2464597 : Nat := 118140960795 + 2464597 * 2 ^ 59
def prefixEnd_2464597 : Nat := 4983230072969 + 3 ^ 40 * 2464597 * 2
def baseEnd_2464597 : Nat := 843681920419465991068687

theorem tailTrace_2464597 : CollatzResearch.WordTrace tailWord_2464597 prefixEnd_2464597 843681920419465991068687 := by
  unfold tailWord_2464597
  simp only [CollatzResearch.WordTrace]
  refine ⟨89891237452193463501584045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59927491634795642334389363 89891237452193463501584045)
  ·
    refine ⟨33709214044572548813094017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89891237452193463501584045 33709214044572548813094017)
    ·
      refine ⟨25281910533429411609820513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33709214044572548813094017 25281910533429411609820513)
      ·
        refine ⟨18961432900072058707365385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25281910533429411609820513 18961432900072058707365385)
        ·
          refine ⟨14221074675054044030524039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18961432900072058707365385 14221074675054044030524039)
          ·
            refine ⟨21331612012581066045786059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14221074675054044030524039 21331612012581066045786059)
            ·
              refine ⟨31997418018871599068679089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21331612012581066045786059 31997418018871599068679089)
              ·
                refine ⟨23998063514153699301509317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31997418018871599068679089 23998063514153699301509317)
                ·
                  refine ⟨4499636908903818619032997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23998063514153699301509317 4499636908903818619032997)
                  ·
                    refine ⟨843681920419465991068687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4499636908903818619032997 843681920419465991068687)
                    ·
                      rfl

theorem cell22_2464597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2464597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464597 prefixEnd_2464597 := by exact prefixLift 2464597
  have htrace : WordTrace (prefixWord ++ tailWord_2464597) baseStart_2464597 baseEnd_2464597 := by
    simpa [prefixWord, tailWord_2464597, baseEnd_2464597] using wordTrace_append hprefix tailTrace_2464597
  have hstable : (prefixWord ++ tailWord_2464597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464597).length < 2 ^ (prefixWord ++ tailWord_2464597).sum := by decide
  have hdescent : baseEnd_2464597 < baseStart_2464597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464612 : List Nat := [2, 3, 1, 1, 4, 1, 2, 8]
def baseStart_2464612 : Nat := 118140960795 + 2464612 * 2 ^ 59
def prefixEnd_2464612 : Nat := 4983230072969 + 3 ^ 40 * 2464612 * 2
def baseEnd_2464612 : Nat := 93743006136223439104849

theorem tailTrace_2464612 : CollatzResearch.WordTrace tailWord_2464612 prefixEnd_2464612 93743006136223439104849 := by
  unfold tailWord_2464612
  simp only [CollatzResearch.WordTrace]
  refine ⟨44945892273569560531690045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59927856364759414042253393 44945892273569560531690045)
  ·
    refine ⟨16854709602588585199383767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44945892273569560531690045 16854709602588585199383767)
    ·
      refine ⟨25282064403882877799075651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16854709602588585199383767 25282064403882877799075651)
      ·
        refine ⟨37923096605824316698613477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25282064403882877799075651 37923096605824316698613477)
        ·
          refine ⟨7110580613592059380990027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37923096605824316698613477 7110580613592059380990027)
          ·
            refine ⟨10665870920388089071485041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7110580613592059380990027 10665870920388089071485041)
            ·
              refine ⟨7999403190291066803613781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10665870920388089071485041 7999403190291066803613781)
              ·
                refine ⟨93743006136223439104849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7999403190291066803613781 93743006136223439104849)
                ·
                  rfl

theorem cell22_2464612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_2464612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464612 prefixEnd_2464612 := by exact prefixLift 2464612
  have htrace : WordTrace (prefixWord ++ tailWord_2464612) baseStart_2464612 baseEnd_2464612 := by
    simpa [prefixWord, tailWord_2464612, baseEnd_2464612] using wordTrace_append hprefix tailTrace_2464612
  have hstable : (prefixWord ++ tailWord_2464612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464612).length < 2 ^ (prefixWord ++ tailWord_2464612).sum := by decide
  have hdescent : baseEnd_2464612 < baseStart_2464612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464644 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2464644 : Nat := 118140960795 + 2464644 * 2 ^ 59
def prefixEnd_2464644 : Nat := 4983230072969 + 3 ^ 40 * 2464644 * 2
def baseEnd_2464644 : Nat := 843698009479973535143543

theorem tailTrace_2464644 : CollatzResearch.WordTrace tailWord_2464644 prefixEnd_2464644 843698009479973535143543 := by
  unfold tailWord_2464644
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946475841511595264272493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59928634455348793685696657 44946475841511595264272493)
  ·
    refine ⟨16854928440566848224102185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44946475841511595264272493 16854928440566848224102185)
    ·
      refine ⟨12641196330425136168076639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16854928440566848224102185 12641196330425136168076639)
      ·
        refine ⟨18961794495637704252114959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12641196330425136168076639 18961794495637704252114959)
        ·
          refine ⟨28442691743456556378172439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18961794495637704252114959 28442691743456556378172439)
          ·
            refine ⟨42664037615184834567258659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28442691743456556378172439 42664037615184834567258659)
            ·
              refine ⟨63996056422777251850887989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42664037615184834567258659 63996056422777251850887989)
              ·
                refine ⟨5999630289635367361020749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63996056422777251850887989 5999630289635367361020749)
                ·
                  refine ⟨2249861358613262760382781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5999630289635367361020749 2249861358613262760382781)
                  ·
                    refine ⟨843698009479973535143543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2249861358613262760382781 843698009479973535143543)
                    ·
                      rfl

theorem cell22_2464644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2464644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464644 prefixEnd_2464644 := by exact prefixLift 2464644
  have htrace : WordTrace (prefixWord ++ tailWord_2464644) baseStart_2464644 baseEnd_2464644 := by
    simpa [prefixWord, tailWord_2464644, baseEnd_2464644] using wordTrace_append hprefix tailTrace_2464644
  have hstable : (prefixWord ++ tailWord_2464644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464644).length < 2 ^ (prefixWord ++ tailWord_2464644).sum := by decide
  have hdescent : baseEnd_2464644 < baseStart_2464644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464687 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 5, 4]
def baseStart_2464687 : Nat := 118140960795 + 2464687 * 2 ^ 59
def prefixEnd_2464687 : Nat := 4983230072969 + 3 ^ 40 * 2464687 * 2
def baseEnd_2464687 : Nat := 843712729258735756318411

theorem tailTrace_2464687 : CollatzResearch.WordTrace tailWord_2464687 prefixEnd_2464687 843712729258735756318411 := by
  unfold tailWord_2464687
  simp only [CollatzResearch.WordTrace]
  refine ⟨89894520021867408872360315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59929680014578272581573543 89894520021867408872360315)
  ·
    refine ⟨134841780032801113308540473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89894520021867408872360315 134841780032801113308540473)
    ·
      refine ⟨101131335024600834981405355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134841780032801113308540473 101131335024600834981405355)
      ·
        refine ⟨151697002536901252472108033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101131335024600834981405355 151697002536901252472108033)
        ·
          refine ⟨113772751902675939354081025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151697002536901252472108033 113772751902675939354081025)
          ·
            refine ⟨85329563927006954515560769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113772751902675939354081025 85329563927006954515560769)
            ·
              refine ⟨63997172945255215886670577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85329563927006954515560769 63997172945255215886670577)
              ·
                refine ⟨47997879708941411915002933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63997172945255215886670577 47997879708941411915002933)
                ·
                  refine ⟨4499801222713257367031525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47997879708941411915002933 4499801222713257367031525)
                  ·
                    refine ⟨843712729258735756318411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4499801222713257367031525 843712729258735756318411)
                    ·
                      rfl

theorem cell22_2464687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_2464687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464687 prefixEnd_2464687 := by exact prefixLift 2464687
  have htrace : WordTrace (prefixWord ++ tailWord_2464687) baseStart_2464687 baseEnd_2464687 := by
    simpa [prefixWord, tailWord_2464687, baseEnd_2464687] using wordTrace_append hprefix tailTrace_2464687
  have hstable : (prefixWord ++ tailWord_2464687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464687).length < 2 ^ (prefixWord ++ tailWord_2464687).sum := by decide
  have hdescent : baseEnd_2464687 < baseStart_2464687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464738 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2464738 : Nat := 118140960795 + 2464738 * 2 ^ 59
def prefixEnd_2464738 : Nat := 4983230072969 + 3 ^ 40 * 2464738 * 2
def baseEnd_2464738 : Nat := 843730187600988623293255

theorem tailTrace_2464738 : CollatzResearch.WordTrace tailWord_2464738 prefixEnd_2464738 843730187600988623293255 := by
  unfold tailWord_2464738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474095036170661145616717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59930920096455096388311245 22474095036170661145616717)
  ·
    refine ⟨8427785638563997929606269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22474095036170661145616717 8427785638563997929606269)
    ·
      refine ⟨3160419614461499223602351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8427785638563997929606269 3160419614461499223602351)
      ·
        refine ⟨4740629421692248835403527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160419614461499223602351 4740629421692248835403527)
        ·
          refine ⟨7110944132538373253105291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740629421692248835403527 7110944132538373253105291)
          ·
            refine ⟨10666416198807559879657937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7110944132538373253105291 10666416198807559879657937)
            ·
              refine ⟨7999812149105669909743453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10666416198807559879657937 7999812149105669909743453)
              ·
                refine ⟨2999929555914626216153795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7999812149105669909743453 2999929555914626216153795)
                ·
                  refine ⟨4499894333871939324230693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999929555914626216153795 4499894333871939324230693)
                  ·
                    refine ⟨843730187600988623293255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4499894333871939324230693 843730187600988623293255)
                    ·
                      rfl

theorem cell22_2464738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2464738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464738 prefixEnd_2464738 := by exact prefixLift 2464738
  have htrace : WordTrace (prefixWord ++ tailWord_2464738) baseStart_2464738 baseEnd_2464738 := by
    simpa [prefixWord, tailWord_2464738, baseEnd_2464738] using wordTrace_append hprefix tailTrace_2464738
  have hstable : (prefixWord ++ tailWord_2464738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464738).length < 2 ^ (prefixWord ++ tailWord_2464738).sum := by decide
  have hdescent : baseEnd_2464738 < baseStart_2464738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464753 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 4]
def baseStart_2464753 : Nat := 118140960795 + 2464753 * 2 ^ 59
def prefixEnd_2464753 : Nat := 4983230072969 + 3 ^ 40 * 2464753 * 2
def baseEnd_2464753 : Nat := 281245107469177861389403

theorem tailTrace_2464753 : CollatzResearch.WordTrace tailWord_2464753 prefixEnd_2464753 281245107469177861389403 := by
  unfold tailWord_2464753
  simp only [CollatzResearch.WordTrace]
  refine ⟨89896927239628302144262913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59931284826418868096175275 89896927239628302144262913)
  ·
    refine ⟨67422695429721226608197185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89896927239628302144262913 67422695429721226608197185)
    ·
      refine ⟨50567021572290919956147889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67422695429721226608197185 50567021572290919956147889)
      ·
        refine ⟨37925266179218189967110917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50567021572290919956147889 37925266179218189967110917)
        ·
          refine ⟨7110987408603410618833297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37925266179218189967110917 7110987408603410618833297)
          ·
            refine ⟨5333240556452557964124973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7110987408603410618833297 5333240556452557964124973)
            ·
              refine ⟨1999965208669709236546865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5333240556452557964124973 1999965208669709236546865)
              ·
                refine ⟨1499973906502281927410149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999965208669709236546865 1499973906502281927410149)
                ·
                  refine ⟨281245107469177861389403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499973906502281927410149 281245107469177861389403)
                  ·
                    rfl

theorem cell22_2464753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_2464753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464753 prefixEnd_2464753 := by exact prefixLift 2464753
  have htrace : WordTrace (prefixWord ++ tailWord_2464753) baseStart_2464753 baseEnd_2464753 := by
    simpa [prefixWord, tailWord_2464753, baseEnd_2464753] using wordTrace_append hprefix tailTrace_2464753
  have hstable : (prefixWord ++ tailWord_2464753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464753).length < 2 ^ (prefixWord ++ tailWord_2464753).sum := by decide
  have hdescent : baseEnd_2464753 < baseStart_2464753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464764 : List Nat := [2, 2, 2, 1, 2, 4, 2, 7]
def baseStart_2464764 : Nat := 118140960795 + 2464764 * 2 ^ 59
def prefixEnd_2464764 : Nat := 4983230072969 + 3 ^ 40 * 2464764 * 2
def baseEnd_2464764 : Nat := 93748787548037024682575

theorem tailTrace_2464764 : CollatzResearch.WordTrace tailWord_2464764 prefixEnd_2464764 93748787548037024682575 := by
  unfold tailWord_2464764
  simp only [CollatzResearch.WordTrace]
  refine ⟨44948664221294225511456673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59931552295058967348608897 44948664221294225511456673)
  ·
    refine ⟨33711498165970669133592505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44948664221294225511456673 33711498165970669133592505)
    ·
      refine ⟨25283623624478001850194379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33711498165970669133592505 25283623624478001850194379)
      ·
        refine ⟨37925435436717002775291569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25283623624478001850194379 37925435436717002775291569)
        ·
          refine ⟨28444076577537752081468677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37925435436717002775291569 28444076577537752081468677)
          ·
            refine ⟨5333264358288328515275377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28444076577537752081468677 5333264358288328515275377)
            ·
              refine ⟨3999948268716246386456533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5333264358288328515275377 3999948268716246386456533)
              ·
                refine ⟨93748787548037024682575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3999948268716246386456533 93748787548037024682575)
                ·
                  rfl

theorem cell22_2464764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_2464764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464764 prefixEnd_2464764 := by exact prefixLift 2464764
  have htrace : WordTrace (prefixWord ++ tailWord_2464764) baseStart_2464764 baseEnd_2464764 := by
    simpa [prefixWord, tailWord_2464764, baseEnd_2464764] using wordTrace_append hprefix tailTrace_2464764
  have hstable : (prefixWord ++ tailWord_2464764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464764).length < 2 ^ (prefixWord ++ tailWord_2464764).sum := by decide
  have hdescent : baseEnd_2464764 < baseStart_2464764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464824 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_2464824 : Nat := 118140960795 + 2464824 * 2 ^ 59
def prefixEnd_2464824 : Nat := 4983230072969 + 3 ^ 40 * 2464824 * 2
def baseEnd_2464824 : Nat := 843759627158513065642991

theorem tailTrace_2464824 : CollatzResearch.WordTrace tailWord_2464824 prefixEnd_2464824 843759627158513065642991 := by
  unfold tailWord_2464824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44949758411185540635048763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59933011214914054180065017 44949758411185540635048763)
  ·
    refine ⟨67424637616778310952573145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44949758411185540635048763 67424637616778310952573145)
    ·
      refine ⟨50568478212583733214429859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67424637616778310952573145 50568478212583733214429859)
      ·
        refine ⟨75852717318875599821644789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50568478212583733214429859 75852717318875599821644789)
        ·
          refine ⟨7111192248644587483279199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75852717318875599821644789 7111192248644587483279199)
          ·
            refine ⟨10666788372966881224918799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7111192248644587483279199 10666788372966881224918799)
            ·
              refine ⟨16000182559450321837378199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10666788372966881224918799 16000182559450321837378199)
              ·
                refine ⟨24000273839175482756067299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16000182559450321837378199 24000273839175482756067299)
                ·
                  refine ⟨36000410758763224134100949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24000273839175482756067299 36000410758763224134100949)
                  ·
                    refine ⟨843759627158513065642991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36000410758763224134100949 843759627158513065642991)
                    ·
                      rfl

theorem cell22_2464824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_2464824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464824 prefixEnd_2464824 := by exact prefixLift 2464824
  have htrace : WordTrace (prefixWord ++ tailWord_2464824) baseStart_2464824 baseEnd_2464824 := by
    simpa [prefixWord, tailWord_2464824, baseEnd_2464824] using wordTrace_append hprefix tailTrace_2464824
  have hstable : (prefixWord ++ tailWord_2464824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464824).length < 2 ^ (prefixWord ++ tailWord_2464824).sum := by decide
  have hdescent : baseEnd_2464824 < baseStart_2464824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464856 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_2464856 : Nat := 118140960795 + 2464856 * 2 ^ 59
def prefixEnd_2464856 : Nat := 4983230072969 + 3 ^ 40 * 2464856 * 2
def baseEnd_2464856 : Nat := 843770581412475648842893

theorem tailTrace_2464856 : CollatzResearch.WordTrace tailWord_2464856 prefixEnd_2464856 843770581412475648842893 := by
  unfold tailWord_2464856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44950341979127575367631211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59933789305503433823508281 44950341979127575367631211)
  ·
    refine ⟨67425512968691363051446817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44950341979127575367631211 67425512968691363051446817)
    ·
      refine ⟨50569134726518522288585113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67425512968691363051446817 50569134726518522288585113)
      ·
        refine ⟨37926851044888891716438835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50569134726518522288585113 37926851044888891716438835)
        ·
          refine ⟨56890276567333337574658253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37926851044888891716438835 56890276567333337574658253)
          ·
            refine ⟨21333853712750001590496845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56890276567333337574658253 21333853712750001590496845)
            ·
              refine ⟨8000195142281250596436317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21333853712750001590496845 8000195142281250596436317)
              ·
                refine ⟨3000073178355468973663619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8000195142281250596436317 3000073178355468973663619)
                ·
                  refine ⟨4500109767533203460495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000073178355468973663619 4500109767533203460495429)
                  ·
                    refine ⟨843770581412475648842893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4500109767533203460495429 843770581412475648842893)
                    ·
                      rfl

theorem cell22_2464856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_2464856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464856 prefixEnd_2464856 := by exact prefixLift 2464856
  have htrace : WordTrace (prefixWord ++ tailWord_2464856) baseStart_2464856 baseEnd_2464856 := by
    simpa [prefixWord, tailWord_2464856, baseEnd_2464856] using wordTrace_append hprefix tailTrace_2464856
  have hstable : (prefixWord ++ tailWord_2464856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464856).length < 2 ^ (prefixWord ++ tailWord_2464856).sum := by decide
  have hdescent : baseEnd_2464856 < baseStart_2464856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464871 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 6]
def baseStart_2464871 : Nat := 118140960795 + 2464871 * 2 ^ 59
def prefixEnd_2464871 : Nat := 4983230072969 + 3 ^ 40 * 2464871 * 2
def baseEnd_2464871 : Nat := 281258572073006869905949

theorem tailTrace_2464871 : CollatzResearch.WordTrace tailWord_2464871 prefixEnd_2464871 281258572073006869905949 := by
  unfold tailWord_2464871
  simp only [CollatzResearch.WordTrace]
  refine ⟨89901231053200808297058467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59934154035467205531372311 89901231053200808297058467)
  ·
    refine ⟨134851846579801212445587701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89901231053200808297058467 134851846579801212445587701)
    ·
      refine ⟨12642360616856363666773847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134851846579801212445587701 12642360616856363666773847)
      ·
        refine ⟨18963540925284545500160771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12642360616856363666773847 18963540925284545500160771)
        ·
          refine ⟨28445311387926818250241157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18963540925284545500160771 28445311387926818250241157)
          ·
            refine ⟨5333495885236278421920217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28445311387926818250241157 5333495885236278421920217)
            ·
              refine ⟨4000121913927208816440163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5333495885236278421920217 4000121913927208816440163)
              ·
                refine ⟨6000182870890813224660245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000121913927208816440163 6000182870890813224660245)
                ·
                  refine ⟨281258572073006869905949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6000182870890813224660245 281258572073006869905949)
                  ·
                    rfl

theorem cell22_2464871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 6].length) (baseStart_2464871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464871 prefixEnd_2464871 := by exact prefixLift 2464871
  have htrace : WordTrace (prefixWord ++ tailWord_2464871) baseStart_2464871 baseEnd_2464871 := by
    simpa [prefixWord, tailWord_2464871, baseEnd_2464871] using wordTrace_append hprefix tailTrace_2464871
  have hstable : (prefixWord ++ tailWord_2464871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464871).length < 2 ^ (prefixWord ++ tailWord_2464871).sum := by decide
  have hdescent : baseEnd_2464871 < baseStart_2464871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464899 : List Nat := [1, 1, 1, 3, 3, 2, 3, 8]
def baseStart_2464899 : Nat := 118140960795 + 2464899 * 2 ^ 59
def prefixEnd_2464899 : Nat := 4983230072969 + 3 ^ 40 * 2464899 * 2
def baseEnd_2464899 : Nat := 93753922354581985557529

theorem tailTrace_2464899 : CollatzResearch.WordTrace tailWord_2464899 prefixEnd_2464899 93753922354581985557529 := by
  unfold tailWord_2464899
  simp only [CollatzResearch.WordTrace]
  refine ⟨89902252297099369079077751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59934834864732912719385167 89902252297099369079077751)
  ·
    refine ⟨134853378445649053618616627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89902252297099369079077751 134853378445649053618616627)
    ·
      refine ⟨202280067668473580427924941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134853378445649053618616627 202280067668473580427924941)
      ·
        refine ⟨75855025375677592660471853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202280067668473580427924941 75855025375677592660471853)
        ·
          refine ⟨28445634515879097247676945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75855025375677592660471853 28445634515879097247676945)
          ·
            refine ⟨21334225886909322935757709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28445634515879097247676945 21334225886909322935757709)
            ·
              refine ⟨8000334707590996100909141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21334225886909322935757709 8000334707590996100909141)
              ·
                refine ⟨93753922354581985557529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8000334707590996100909141 93753922354581985557529)
                ·
                  rfl

theorem cell22_2464899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 8].length) (baseStart_2464899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464899 prefixEnd_2464899 := by exact prefixLift 2464899
  have htrace : WordTrace (prefixWord ++ tailWord_2464899) baseStart_2464899 baseEnd_2464899 := by
    simpa [prefixWord, tailWord_2464899, baseEnd_2464899] using wordTrace_append hprefix tailTrace_2464899
  have hstable : (prefixWord ++ tailWord_2464899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464899).length < 2 ^ (prefixWord ++ tailWord_2464899).sum := by decide
  have hdescent : baseEnd_2464899 < baseStart_2464899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464978 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_2464978 : Nat := 118140960795 + 2464978 * 2 ^ 59
def prefixEnd_2464978 : Nat := 4983230072969 + 3 ^ 40 * 2464978 * 2
def baseEnd_2464978 : Nat := 281270781501902665764173

theorem tailTrace_2464978 : CollatzResearch.WordTrace tailWord_2464978 prefixEnd_2464978 281270781501902665764173 := by
  unfold tailWord_2464978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476283415953291392800897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59936755775875443714135725 22476283415953291392800897)
  ·
    refine ⟨16857212561964968544600673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22476283415953291392800897 16857212561964968544600673)
    ·
      refine ⟨12642909421473726408450505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16857212561964968544600673 12642909421473726408450505)
      ·
        refine ⟨9482182066105294806337879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12642909421473726408450505 9482182066105294806337879)
        ·
          refine ⟨14223273099157942209506819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9482182066105294806337879 14223273099157942209506819)
          ·
            refine ⟨21334909648736913314260229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14223273099157942209506819 21334909648736913314260229)
            ·
              refine ⟨4000295559138171246423793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21334909648736913314260229 4000295559138171246423793)
              ·
                refine ⟨3000221669353628434817845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4000295559138171246423793 3000221669353628434817845)
                ·
                  refine ⟨281270781501902665764173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3000221669353628434817845 281270781501902665764173)
                  ·
                    rfl

theorem cell22_2464978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_2464978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464978 prefixEnd_2464978 := by exact prefixLift 2464978
  have htrace : WordTrace (prefixWord ++ tailWord_2464978) baseStart_2464978 baseEnd_2464978 := by
    simpa [prefixWord, tailWord_2464978, baseEnd_2464978] using wordTrace_append hprefix tailTrace_2464978
  have hstable : (prefixWord ++ tailWord_2464978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464978).length < 2 ^ (prefixWord ++ tailWord_2464978).sum := by decide
  have hdescent : baseEnd_2464978 < baseStart_2464978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2464991 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 3, 4]
def baseStart_2464991 : Nat := 118140960795 + 2464991 * 2 ^ 59
def prefixEnd_2464991 : Nat := 4983230072969 + 3 ^ 40 * 2464991 * 2
def baseEnd_2464991 : Nat := 843816794671380296717479

theorem tailTrace_2464991 : CollatzResearch.WordTrace tailWord_2464991 prefixEnd_2464991 843816794671380296717479 := by
  unfold tailWord_2464991
  simp only [CollatzResearch.WordTrace]
  refine ⟨89905607812766068791426827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59937071875177379194284551 89905607812766068791426827)
  ·
    refine ⟨134858411719149103187140241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89905607812766068791426827 134858411719149103187140241)
    ·
      refine ⟨101143808789361827390355181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134858411719149103187140241 101143808789361827390355181)
      ·
        refine ⟨37928928296010685271383193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101143808789361827390355181 37928928296010685271383193)
        ·
          refine ⟨28446696222008013953537395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37928928296010685271383193 28446696222008013953537395)
          ·
            refine ⟨42670044333012020930306093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28446696222008013953537395 42670044333012020930306093)
            ·
              refine ⟨16001266624879507848864785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42670044333012020930306093 16001266624879507848864785)
              ·
                refine ⟨12000949968659630886648589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16001266624879507848864785 12000949968659630886648589)
                ·
                  refine ⟨4500356238247361582493221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12000949968659630886648589 4500356238247361582493221)
                  ·
                    refine ⟨843816794671380296717479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4500356238247361582493221 843816794671380296717479)
                    ·
                      rfl

theorem cell22_2464991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_2464991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2464991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2464991 prefixEnd_2464991 := by exact prefixLift 2464991
  have htrace : WordTrace (prefixWord ++ tailWord_2464991) baseStart_2464991 baseEnd_2464991 := by
    simpa [prefixWord, tailWord_2464991, baseEnd_2464991] using wordTrace_append hprefix tailTrace_2464991
  have hstable : (prefixWord ++ tailWord_2464991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2464991).length < 2 ^ (prefixWord ++ tailWord_2464991).sum := by decide
  have hdescent : baseEnd_2464991 < baseStart_2464991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2464991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465006 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_2465006 : Nat := 118140960795 + 2465006 * 2 ^ 59
def prefixEnd_2465006 : Nat := 4983230072969 + 3 ^ 40 * 2465006 * 2
def baseEnd_2465006 : Nat := 281273976492641752530811

theorem tailTrace_2465006 : CollatzResearch.WordTrace tailWord_2465006 prefixEnd_2465006 281273976492641752530811 := by
  unfold tailWord_2465006
  simp only [CollatzResearch.WordTrace]
  refine ⟨11238269363463965794152859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59937436605141150902148581 11238269363463965794152859)
  ·
    refine ⟨16857404045195948691229289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11238269363463965794152859 16857404045195948691229289)
    ·
      refine ⟨12643053033896961518421967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16857404045195948691229289 12643053033896961518421967)
      ·
        refine ⟨18964579550845442277632951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12643053033896961518421967 18964579550845442277632951)
        ·
          refine ⟨28446869326268163416449427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18964579550845442277632951 28446869326268163416449427)
          ·
            refine ⟨42670303989402245124674141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28446869326268163416449427 42670303989402245124674141)
            ·
              refine ⟨16001363996025841921752803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42670303989402245124674141 16001363996025841921752803)
              ·
                refine ⟨24002045994038762882629205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16001363996025841921752803 24002045994038762882629205)
                ·
                  refine ⟨281273976492641752530811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24002045994038762882629205 281273976492641752530811)
                  ·
                    rfl

theorem cell22_2465006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_2465006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465006 prefixEnd_2465006 := by exact prefixLift 2465006
  have htrace : WordTrace (prefixWord ++ tailWord_2465006) baseStart_2465006 baseEnd_2465006 := by
    simpa [prefixWord, tailWord_2465006, baseEnd_2465006] using wordTrace_append hprefix tailTrace_2465006
  have hstable : (prefixWord ++ tailWord_2465006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465006).length < 2 ^ (prefixWord ++ tailWord_2465006).sum := by decide
  have hdescent : baseEnd_2465006 < baseStart_2465006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465023 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 4]
def baseStart_2465023 : Nat := 118140960795 + 2465023 * 2 ^ 59
def prefixEnd_2465023 : Nat := 4983230072969 + 3 ^ 40 * 2465023 * 2
def baseEnd_2465023 : Nat := 281275916308447626639127

theorem tailTrace_2465023 : CollatzResearch.WordTrace tailWord_2465023 prefixEnd_2465023 281275916308447626639127 := by
  unfold tailWord_2465023
  simp only [CollatzResearch.WordTrace]
  refine ⟨89906774948650138256591723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59937849965766758837727815 89906774948650138256591723)
  ·
    refine ⟨134860162422975207384887585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89906774948650138256591723 134860162422975207384887585)
    ·
      refine ⟨101145121817231405538665689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134860162422975207384887585 101145121817231405538665689)
      ·
        refine ⟨75858841362923554153999267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101145121817231405538665689 75858841362923554153999267)
        ·
          refine ⟨113788262044385331230998901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75858841362923554153999267 113788262044385331230998901)
          ·
            refine ⟨10667649566661124802906147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113788262044385331230998901 10667649566661124802906147)
            ·
              refine ⟨16001474349991687204359221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10667649566661124802906147 16001474349991687204359221)
              ·
                refine ⟨1500138220311720675408677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16001474349991687204359221 1500138220311720675408677)
                ·
                  refine ⟨281275916308447626639127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1500138220311720675408677 281275916308447626639127)
                  ·
                    rfl

theorem cell22_2465023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 4].length) (baseStart_2465023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465023 prefixEnd_2465023 := by exact prefixLift 2465023
  have htrace : WordTrace (prefixWord ++ tailWord_2465023) baseStart_2465023 baseEnd_2465023 := by
    simpa [prefixWord, tailWord_2465023, baseEnd_2465023] using wordTrace_append hprefix tailTrace_2465023
  have hstable : (prefixWord ++ tailWord_2465023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465023).length < 2 ^ (prefixWord ++ tailWord_2465023).sum := by decide
  have hdescent : baseEnd_2465023 < baseStart_2465023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465025 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2465025 : Nat := 118140960795 + 2465025 * 2 ^ 59
def prefixEnd_2465025 : Nat := 4983230072969 + 3 ^ 40 * 2465025 * 2
def baseEnd_2465025 : Nat := 843828433566215541367375

theorem tailTrace_2465025 : CollatzResearch.WordTrace tailWord_2465025 prefixEnd_2465025 843828433566215541367375 := by
  unfold tailWord_2465025
  simp only [CollatzResearch.WordTrace]
  refine ⟨89906847894642892598164529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59937898596428595065443019 89906847894642892598164529)
  ·
    refine ⟨67430135920982169448623397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89906847894642892598164529 67430135920982169448623397)
    ·
      refine ⟨12643150485184156771616887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67430135920982169448623397 12643150485184156771616887)
      ·
        refine ⟨18964725727776235157425331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12643150485184156771616887 18964725727776235157425331)
        ·
          refine ⟨28447088591664352736137997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18964725727776235157425331 28447088591664352736137997)
          ·
            refine ⟨10667658221874132276051749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28447088591664352736137997 10667658221874132276051749)
            ·
              refine ⟨2000185916601399801759703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10667658221874132276051749 2000185916601399801759703)
              ·
                refine ⟨3000278874902099702639555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000185916601399801759703 3000278874902099702639555)
                ·
                  refine ⟨4500418312353149553959333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000278874902099702639555 4500418312353149553959333)
                  ·
                    refine ⟨843828433566215541367375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4500418312353149553959333 843828433566215541367375)
                    ·
                      rfl

theorem cell22_2465025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2465025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465025 prefixEnd_2465025 := by exact prefixLift 2465025
  have htrace : WordTrace (prefixWord ++ tailWord_2465025) baseStart_2465025 baseEnd_2465025 := by
    simpa [prefixWord, tailWord_2465025, baseEnd_2465025] using wordTrace_append hprefix tailTrace_2465025
  have hstable : (prefixWord ++ tailWord_2465025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465025).length < 2 ^ (prefixWord ++ tailWord_2465025).sum := by decide
  have hdescent : baseEnd_2465025 < baseStart_2465025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465053 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2465053 : Nat := 118140960795 + 2465053 * 2 ^ 59
def prefixEnd_2465053 : Nat := 4983230072969 + 3 ^ 40 * 2465053 * 2
def baseEnd_2465053 : Nat := 843838018538432801667289

theorem tailTrace_2465053 : CollatzResearch.WordTrace tailWord_2465053 prefixEnd_2465053 843838018538432801667289 := by
  unfold tailWord_2465053
  simp only [CollatzResearch.WordTrace]
  refine ⟨89907869138541453380183813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59938579425694302253455875 89907869138541453380183813)
  ·
    refine ⟨16857725463476522508784465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89907869138541453380183813 16857725463476522508784465)
    ·
      refine ⟨12643294097607391881588349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16857725463476522508784465 12643294097607391881588349)
      ·
        refine ⟨4741235286602771955595631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12643294097607391881588349 4741235286602771955595631)
        ·
          refine ⟨7111852929904157933393447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741235286602771955595631 7111852929904157933393447)
          ·
            refine ⟨10667779394856236900090171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7111852929904157933393447 10667779394856236900090171)
            ·
              refine ⟨16001669092284355350135257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10667779394856236900090171 16001669092284355350135257)
              ·
                refine ⟨12001251819213266512601443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16001669092284355350135257 12001251819213266512601443)
                ·
                  refine ⟨18001877728819899768902165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12001251819213266512601443 18001877728819899768902165)
                  ·
                    refine ⟨843838018538432801667289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18001877728819899768902165 843838018538432801667289)
                    ·
                      rfl

theorem cell22_2465053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2465053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465053 prefixEnd_2465053 := by exact prefixLift 2465053
  have htrace : WordTrace (prefixWord ++ tailWord_2465053) baseStart_2465053 baseEnd_2465053 := by
    simpa [prefixWord, tailWord_2465053, baseEnd_2465053] using wordTrace_append hprefix tailTrace_2465053
  have hstable : (prefixWord ++ tailWord_2465053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465053).length < 2 ^ (prefixWord ++ tailWord_2465053).sum := by decide
  have hdescent : baseEnd_2465053 < baseStart_2465053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465055 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 1, 5]
def baseStart_2465055 : Nat := 118140960795 + 2465055 * 2 ^ 59
def prefixEnd_2465055 : Nat := 4983230072969 + 3 ^ 40 * 2465055 * 2
def baseEnd_2465055 : Nat := 843838703179305463117283

theorem tailTrace_2465055 : CollatzResearch.WordTrace tailWord_2465055 prefixEnd_2465055 843838703179305463117283 := by
  unfold tailWord_2465055
  simp only [CollatzResearch.WordTrace]
  refine ⟨89907942084534207721756619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59938628056356138481171079 89907942084534207721756619)
  ·
    refine ⟨134861913126801311582634929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89907942084534207721756619 134861913126801311582634929)
    ·
      refine ⟨101146434845100983686976197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134861913126801311582634929 101146434845100983686976197)
      ·
        refine ⟨18964956533456434441308037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101146434845100983686976197 18964956533456434441308037)
        ·
          refine ⟨3555929350023081457745257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18964956533456434441308037 3555929350023081457745257)
          ·
            refine ⟨2666947012517311093308943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3555929350023081457745257 2666947012517311093308943)
            ·
              refine ⟨4000420518775966639963415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666947012517311093308943 4000420518775966639963415)
              ·
                refine ⟨6000630778163949959945123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000420518775966639963415 6000630778163949959945123)
                ·
                  refine ⟨9000946167245924939917685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6000630778163949959945123 9000946167245924939917685)
                  ·
                    refine ⟨843838703179305463117283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9000946167245924939917685 843838703179305463117283)
                    ·
                      rfl

theorem cell22_2465055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_2465055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465055 prefixEnd_2465055 := by exact prefixLift 2465055
  have htrace : WordTrace (prefixWord ++ tailWord_2465055) baseStart_2465055 baseEnd_2465055 := by
    simpa [prefixWord, tailWord_2465055, baseEnd_2465055] using wordTrace_append hprefix tailTrace_2465055
  have hstable : (prefixWord ++ tailWord_2465055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465055).length < 2 ^ (prefixWord ++ tailWord_2465055).sum := by decide
  have hdescent : baseEnd_2465055 < baseStart_2465055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465085 : List Nat := [1, 4, 1, 5, 1, 2, 8]
def baseStart_2465085 : Nat := 118140960795 + 2465085 * 2 ^ 59
def prefixEnd_2465085 : Nat := 4983230072969 + 3 ^ 40 * 2465085 * 2
def baseEnd_2465085 : Nat := 31253665658977606846933

theorem tailTrace_2465085 : CollatzResearch.WordTrace tailWord_2465085 prefixEnd_2465085 31253665658977606846933 := by
  unfold tailWord_2465085
  simp only [CollatzResearch.WordTrace]
  refine ⟨89909036274425522845348709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59939357516283681896899139 89909036274425522845348709)
  ·
    refine ⟨16857944301454785533502883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89909036274425522845348709 16857944301454785533502883)
    ·
      refine ⟨25286916452182178300254325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16857944301454785533502883 25286916452182178300254325)
      ·
        refine ⟨2370648417392079215648843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25286916452182178300254325 2370648417392079215648843)
        ·
          refine ⟨3555972626088118823473265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370648417392079215648843 3555972626088118823473265)
          ·
            refine ⟨2666979469566089117604949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3555972626088118823473265 2666979469566089117604949)
            ·
              refine ⟨31253665658977606846933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2666979469566089117604949 31253665658977606846933)
              ·
                rfl

theorem cell22_2465085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 8].length) (baseStart_2465085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465085 prefixEnd_2465085 := by exact prefixLift 2465085
  have htrace : WordTrace (prefixWord ++ tailWord_2465085) baseStart_2465085 baseEnd_2465085 := by
    simpa [prefixWord, tailWord_2465085, baseEnd_2465085] using wordTrace_append hprefix tailTrace_2465085
  have hstable : (prefixWord ++ tailWord_2465085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465085).length < 2 ^ (prefixWord ++ tailWord_2465085).sum := by decide
  have hdescent : baseEnd_2465085 < baseStart_2465085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465100 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_2465100 : Nat := 118140960795 + 2465100 * 2 ^ 59
def prefixEnd_2465100 : Nat := 4983230072969 + 3 ^ 40 * 2465100 * 2
def baseEnd_2465100 : Nat := 843854107598940345742145

theorem tailTrace_2465100 : CollatzResearch.WordTrace tailWord_2465100 prefixEnd_2465100 843854107598940345742145 := by
  unfold tailWord_2465100
  simp only [CollatzResearch.WordTrace]
  refine ⟨44954791684685590203572377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59939722246247453604763169 44954791684685590203572377)
  ·
    refine ⟨33716093763514192652679283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44954791684685590203572377 33716093763514192652679283)
    ·
      refine ⟨50574140645271288979018925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33716093763514192652679283 50574140645271288979018925)
      ·
        refine ⟨18965302741976733367132097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50574140645271288979018925 18965302741976733367132097)
        ·
          refine ⟨14223977056482550025349073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18965302741976733367132097 14223977056482550025349073)
          ·
            refine ⟨10667982792361912519011805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14223977056482550025349073 10667982792361912519011805)
            ·
              refine ⟨4000493547135717194629427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10667982792361912519011805 4000493547135717194629427)
              ·
                refine ⟨6000740320703575791944141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000493547135717194629427 6000740320703575791944141)
                ·
                  refine ⟨2250277620263840921979053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6000740320703575791944141 2250277620263840921979053)
                  ·
                    refine ⟨843854107598940345742145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2250277620263840921979053 843854107598940345742145)
                    ·
                      rfl

theorem cell22_2465100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_2465100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465100 prefixEnd_2465100 := by exact prefixLift 2465100
  have htrace : WordTrace (prefixWord ++ tailWord_2465100) baseStart_2465100 baseEnd_2465100 := by
    simpa [prefixWord, tailWord_2465100, baseEnd_2465100] using wordTrace_append hprefix tailTrace_2465100
  have hstable : (prefixWord ++ tailWord_2465100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465100).length < 2 ^ (prefixWord ++ tailWord_2465100).sum := by decide
  have hdescent : baseEnd_2465100 < baseStart_2465100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465173 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2465173 : Nat := 118140960795 + 2465173 * 2 ^ 59
def prefixEnd_2465173 : Nat := 4983230072969 + 3 ^ 40 * 2465173 * 2
def baseEnd_2465173 : Nat := 843879096990792488666921

theorem tailTrace_2465173 : CollatzResearch.WordTrace tailWord_2465173 prefixEnd_2465173 843879096990792488666921 := by
  unfold tailWord_2465173
  simp only [CollatzResearch.WordTrace]
  refine ⟨89912245898106713874552173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59941497265404475916368115 89912245898106713874552173)
  ·
    refine ⟨33717092211790017702957065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89912245898106713874552173 33717092211790017702957065)
    ·
      refine ⟨25287819158842513277217799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33717092211790017702957065 25287819158842513277217799)
      ·
        refine ⟨37931728738263769915826699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25287819158842513277217799 37931728738263769915826699)
        ·
          refine ⟨56897593107395654873740049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37931728738263769915826699 56897593107395654873740049)
          ·
            refine ⟨42673194830546741155305037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56897593107395654873740049 42673194830546741155305037)
            ·
              refine ⟨16002448061455027933239389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42673194830546741155305037 16002448061455027933239389)
              ·
                refine ⟨6000918023045635474964771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16002448061455027933239389 6000918023045635474964771)
                ·
                  refine ⟨9001377034568453212447157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6000918023045635474964771 9001377034568453212447157)
                  ·
                    refine ⟨843879096990792488666921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9001377034568453212447157 843879096990792488666921)
                    ·
                      rfl

theorem cell22_2465173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2465173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465173 prefixEnd_2465173 := by exact prefixLift 2465173
  have htrace : WordTrace (prefixWord ++ tailWord_2465173) baseStart_2465173 baseEnd_2465173 := by
    simpa [prefixWord, tailWord_2465173, baseEnd_2465173] using wordTrace_append hprefix tailTrace_2465173
  have hstable : (prefixWord ++ tailWord_2465173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465173).length < 2 ^ (prefixWord ++ tailWord_2465173).sum := by decide
  have hdescent : baseEnd_2465173 < baseStart_2465173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465263 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_2465263 : Nat := 118140960795 + 2465263 * 2 ^ 59
def prefixEnd_2465263 : Nat := 4983230072969 + 3 ^ 40 * 2465263 * 2
def baseEnd_2465263 : Nat := 843909905830062253916645

theorem tailTrace_2465263 : CollatzResearch.WordTrace tailWord_2465263 prefixEnd_2465263 843909905830062253916645 := by
  unfold tailWord_2465263
  simp only [CollatzResearch.WordTrace]
  refine ⟨89915528467780659245328443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59943685645187106163552295 89915528467780659245328443)
  ·
    refine ⟨134873292701670988867992665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89915528467780659245328443 134873292701670988867992665)
    ·
      refine ⟨101154969526253241650994499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134873292701670988867992665 101154969526253241650994499)
      ·
        refine ⟨151732454289379862476491749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101154969526253241650994499 151732454289379862476491749)
        ·
          refine ⟨28449835179258724214342203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151732454289379862476491749 28449835179258724214342203)
          ·
            refine ⟨42674752768888086321513305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28449835179258724214342203 42674752768888086321513305)
            ·
              refine ⟨32006064576666064741134979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42674752768888086321513305 32006064576666064741134979)
              ·
                refine ⟨48009096864999097111702469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32006064576666064741134979 48009096864999097111702469)
                ·
                  refine ⟨9001705662187330708444213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48009096864999097111702469 9001705662187330708444213)
                  ·
                    refine ⟨843909905830062253916645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9001705662187330708444213 843909905830062253916645)
                    ·
                      rfl

theorem cell22_2465263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_2465263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465263 prefixEnd_2465263 := by exact prefixLift 2465263
  have htrace : WordTrace (prefixWord ++ tailWord_2465263) baseStart_2465263 baseEnd_2465263 := by
    simpa [prefixWord, tailWord_2465263, baseEnd_2465263] using wordTrace_append hprefix tailTrace_2465263
  have hstable : (prefixWord ++ tailWord_2465263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465263).length < 2 ^ (prefixWord ++ tailWord_2465263).sum := by decide
  have hdescent : baseEnd_2465263 < baseStart_2465263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465269 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2465269 : Nat := 118140960795 + 2465269 * 2 ^ 59
def prefixEnd_2465269 : Nat := 4983230072969 + 3 ^ 40 * 2465269 * 2
def baseEnd_2465269 : Nat := 843911959752680238266627

theorem tailTrace_2465269 : CollatzResearch.WordTrace tailWord_2465269 prefixEnd_2465269 843911959752680238266627 := by
  unfold tailWord_2465269
  simp only [CollatzResearch.WordTrace]
  refine ⟨89915747305758922270046861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59943831537172614846697907 89915747305758922270046861)
  ·
    refine ⟨33718405239659595851267573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89915747305758922270046861 33718405239659595851267573)
    ·
      refine ⟨3161100491218087111056335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33718405239659595851267573 3161100491218087111056335)
      ·
        refine ⟨4741650736827130666584503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161100491218087111056335 4741650736827130666584503)
        ·
          refine ⟨7112476105240695999876755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741650736827130666584503 7112476105240695999876755)
          ·
            refine ⟨10668714157861043999815133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7112476105240695999876755 10668714157861043999815133)
            ·
              refine ⟨4000767809197891499930675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10668714157861043999815133 4000767809197891499930675)
              ·
                refine ⟨6001151713796837249896013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000767809197891499930675 6001151713796837249896013)
                ·
                  refine ⟨2250431892673813968711005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6001151713796837249896013 2250431892673813968711005)
                  ·
                    refine ⟨843911959752680238266627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2250431892673813968711005 843911959752680238266627)
                    ·
                      rfl

theorem cell22_2465269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2465269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465269 prefixEnd_2465269 := by exact prefixLift 2465269
  have htrace : WordTrace (prefixWord ++ tailWord_2465269) baseStart_2465269 baseEnd_2465269 := by
    simpa [prefixWord, tailWord_2465269, baseEnd_2465269] using wordTrace_append hprefix tailTrace_2465269
  have hstable : (prefixWord ++ tailWord_2465269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465269).length < 2 ^ (prefixWord ++ tailWord_2465269).sum := by decide
  have hdescent : baseEnd_2465269 < baseStart_2465269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465320 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2465320 : Nat := 118140960795 + 2465320 * 2 ^ 59
def prefixEnd_2465320 : Nat := 4983230072969 + 3 ^ 40 * 2465320 * 2
def baseEnd_2465320 : Nat := 843929418094933105241471

theorem tailTrace_2465320 : CollatzResearch.WordTrace tailWord_2465320 prefixEnd_2465320 843929418094933105241471 := by
  unfold tailWord_2465320
  simp only [CollatzResearch.WordTrace]
  refine ⟨44958803714287078990076707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59945071619049438653435609 44958803714287078990076707)
  ·
    refine ⟨67438205571430618485115061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44958803714287078990076707 67438205571430618485115061)
    ·
      refine ⟨6322331772321620482979537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67438205571430618485115061 6322331772321620482979537)
      ·
        refine ⟨4741748829241215362234653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6322331772321620482979537 4741748829241215362234653)
        ·
          refine ⟨1778155810965455760837995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4741748829241215362234653 1778155810965455760837995)
          ·
            refine ⟨2667233716448183641256993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778155810965455760837995 2667233716448183641256993)
            ·
              refine ⟨2000425287336137730942745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667233716448183641256993 2000425287336137730942745)
              ·
                refine ⟨1500318965502103298207059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000425287336137730942745 1500318965502103298207059)
                ·
                  refine ⟨2250478448253154947310589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500318965502103298207059 2250478448253154947310589)
                  ·
                    refine ⟨843929418094933105241471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2250478448253154947310589 843929418094933105241471)
                    ·
                      rfl

theorem cell22_2465320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2465320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465320 prefixEnd_2465320 := by exact prefixLift 2465320
  have htrace : WordTrace (prefixWord ++ tailWord_2465320) baseStart_2465320 baseEnd_2465320 := by
    simpa [prefixWord, tailWord_2465320, baseEnd_2465320] using wordTrace_append hprefix tailTrace_2465320
  have hstable : (prefixWord ++ tailWord_2465320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465320).length < 2 ^ (prefixWord ++ tailWord_2465320).sum := by decide
  have hdescent : baseEnd_2465320 < baseStart_2465320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465323 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_2465323 : Nat := 118140960795 + 2465323 * 2 ^ 59
def prefixEnd_2465323 : Nat := 4983230072969 + 3 ^ 40 * 2465323 * 2
def baseEnd_2465323 : Nat := 843930445056242097416461

theorem tailTrace_2465323 : CollatzResearch.WordTrace tailWord_2465323 prefixEnd_2465323 843930445056242097416461 := by
  unfold tailWord_2465323
  simp only [CollatzResearch.WordTrace]
  refine ⟨89917716847563289492512623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59945144565042192995008415 89917716847563289492512623)
  ·
    refine ⟨134876575271344934238768935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89917716847563289492512623 134876575271344934238768935)
    ·
      refine ⟨202314862907017401358153403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134876575271344934238768935 202314862907017401358153403)
      ·
        refine ⟨303472294360526102037230105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202314862907017401358153403 303472294360526102037230105)
        ·
          refine ⟨227604220770394576527922579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303472294360526102037230105 227604220770394576527922579)
          ·
            refine ⟨341406331155591864791883869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227604220770394576527922579 341406331155591864791883869)
            ·
              refine ⟨128027374183346949296956451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341406331155591864791883869 128027374183346949296956451)
              ·
                refine ⟨192041061275020423945434677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128027374183346949296956451 192041061275020423945434677)
                ·
                  refine ⟨18003849494533164744884501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192041061275020423945434677 18003849494533164744884501)
                  ·
                    refine ⟨843930445056242097416461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18003849494533164744884501 843930445056242097416461)
                    ·
                      rfl

theorem cell22_2465323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_2465323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465323 prefixEnd_2465323 := by exact prefixLift 2465323
  have htrace : WordTrace (prefixWord ++ tailWord_2465323) baseStart_2465323 baseEnd_2465323 := by
    simpa [prefixWord, tailWord_2465323, baseEnd_2465323] using wordTrace_append hprefix tailTrace_2465323
  have hstable : (prefixWord ++ tailWord_2465323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465323).length < 2 ^ (prefixWord ++ tailWord_2465323).sum := by decide
  have hdescent : baseEnd_2465323 < baseStart_2465323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465511 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2465511 : Nat := 118140960795 + 2465511 * 2 ^ 59
def prefixEnd_2465511 : Nat := 4983230072969 + 3 ^ 40 * 2465511 * 2
def baseEnd_2465511 : Nat := 843994801298272273715885

theorem tailTrace_2465511 : CollatzResearch.WordTrace tailWord_2465511 prefixEnd_2465511 843994801298272273715885 := by
  unfold tailWord_2465511
  simp only [CollatzResearch.WordTrace]
  refine ⟨89924573770882197600356387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59949715847254798400237591 89924573770882197600356387)
  ·
    refine ⟨134886860656323296400534581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89924573770882197600356387 134886860656323296400534581)
    ·
      refine ⟨12645643186530309037550117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134886860656323296400534581 12645643186530309037550117)
      ·
        refine ⟨2371058097474432944540647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12645643186530309037550117 2371058097474432944540647)
        ·
          refine ⟨3556587146211649416810971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371058097474432944540647 3556587146211649416810971)
          ·
            refine ⟨5334880719317474125216457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556587146211649416810971 5334880719317474125216457)
            ·
              refine ⟨4001160539488105593912343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5334880719317474125216457 4001160539488105593912343)
              ·
                refine ⟨6001740809232158390868515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4001160539488105593912343 6001740809232158390868515)
                ·
                  refine ⟨9002611213848237586302773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6001740809232158390868515 9002611213848237586302773)
                  ·
                    refine ⟨843994801298272273715885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9002611213848237586302773 843994801298272273715885)
                    ·
                      rfl

theorem cell22_2465511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2465511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465511 prefixEnd_2465511 := by exact prefixLift 2465511
  have htrace : WordTrace (prefixWord ++ tailWord_2465511) baseStart_2465511 baseEnd_2465511 := by
    simpa [prefixWord, tailWord_2465511, baseEnd_2465511] using wordTrace_append hprefix tailTrace_2465511
  have hstable : (prefixWord ++ tailWord_2465511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465511).length < 2 ^ (prefixWord ++ tailWord_2465511).sum := by decide
  have hdescent : baseEnd_2465511 < baseStart_2465511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465526 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_2465526 : Nat := 118140960795 + 2465526 * 2 ^ 59
def prefixEnd_2465526 : Nat := 4983230072969 + 3 ^ 40 * 2465526 * 2
def baseEnd_2465526 : Nat := 843999936104817234590839

theorem tailTrace_2465526 : CollatzResearch.WordTrace tailWord_2465526 prefixEnd_2465526 843999936104817234590839 := by
  unfold tailWord_2465526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620320054114240947634527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59950080577218570108101621 5620320054114240947634527)
  ·
    refine ⟨8430480081171361421451791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620320054114240947634527 8430480081171361421451791)
    ·
      refine ⟨12645720121757042132177687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8430480081171361421451791 12645720121757042132177687)
      ·
        refine ⟨18968580182635563198266531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645720121757042132177687 18968580182635563198266531)
        ·
          refine ⟨28452870273953344797399797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18968580182635563198266531 28452870273953344797399797)
          ·
            refine ⟨2667456588183126074756231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28452870273953344797399797 2667456588183126074756231)
            ·
              refine ⟨4001184882274689112134347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667456588183126074756231 4001184882274689112134347)
              ·
                refine ⟨6001777323412033668201521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4001184882274689112134347 6001777323412033668201521)
                ·
                  refine ⟨4501332992559025251151141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6001777323412033668201521 4501332992559025251151141)
                  ·
                    refine ⟨843999936104817234590839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501332992559025251151141 843999936104817234590839)
                    ·
                      rfl

theorem cell22_2465526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_2465526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465526 prefixEnd_2465526 := by exact prefixLift 2465526
  have htrace : WordTrace (prefixWord ++ tailWord_2465526) baseStart_2465526 baseEnd_2465526 := by
    simpa [prefixWord, tailWord_2465526, baseEnd_2465526] using wordTrace_append hprefix tailTrace_2465526
  have hstable : (prefixWord ++ tailWord_2465526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465526).length < 2 ^ (prefixWord ++ tailWord_2465526).sum := by decide
  have hdescent : baseEnd_2465526 < baseStart_2465526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465567 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_2465567 : Nat := 118140960795 + 2465567 * 2 ^ 59
def prefixEnd_2465567 : Nat := 4983230072969 + 3 ^ 40 * 2465567 * 2
def baseEnd_2465567 : Nat := 844013971242706794315713

theorem tailTrace_2465567 : CollatzResearch.WordTrace tailWord_2465567 prefixEnd_2465567 844013971242706794315713 := by
  unfold tailWord_2465567
  simp only [CollatzResearch.WordTrace]
  refine ⟨89926616258679319164394955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59951077505786212776263303 89926616258679319164394955)
  ·
    refine ⟨134889924388018978746592433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89926616258679319164394955 134889924388018978746592433)
    ·
      refine ⟨101167443291014234059944325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134889924388018978746592433 101167443291014234059944325)
      ·
        refine ⟨18968895617065168886239561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101167443291014234059944325 18968895617065168886239561)
        ·
          refine ⟨14226671712798876664679671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18968895617065168886239561 14226671712798876664679671)
          ·
            refine ⟨21340007569198314997019507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14226671712798876664679671 21340007569198314997019507)
            ·
              refine ⟨32010011353797472495529261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21340007569198314997019507 32010011353797472495529261)
              ·
                refine ⟨12003754257674052185823473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32010011353797472495529261 12003754257674052185823473)
                ·
                  refine ⟨9002815693255539139367605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12003754257674052185823473 9002815693255539139367605)
                  ·
                    refine ⟨844013971242706794315713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9002815693255539139367605 844013971242706794315713)
                    ·
                      rfl

theorem cell22_2465567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_2465567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465567 prefixEnd_2465567 := by exact prefixLift 2465567
  have htrace : WordTrace (prefixWord ++ tailWord_2465567) baseStart_2465567 baseEnd_2465567 := by
    simpa [prefixWord, tailWord_2465567, baseEnd_2465567] using wordTrace_append hprefix tailTrace_2465567
  have hstable : (prefixWord ++ tailWord_2465567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465567).length < 2 ^ (prefixWord ++ tailWord_2465567).sum := by decide
  have hdescent : baseEnd_2465567 < baseStart_2465567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465590 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2465590 : Nat := 118140960795 + 2465590 * 2 ^ 59
def prefixEnd_2465590 : Nat := 4983230072969 + 3 ^ 40 * 2465590 * 2
def baseEnd_2465590 : Nat := 844021844612742400990643

theorem tailTrace_2465590 : CollatzResearch.WordTrace tailWord_2465590 prefixEnd_2465590 844021844612742400990643 := by
  unfold tailWord_2465590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620465946099749630780139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59951636758397329394988149 5620465946099749630780139)
  ·
    refine ⟨8430698919149624446170209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620465946099749630780139 8430698919149624446170209)
    ·
      refine ⟨6323024189362218334627657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8430698919149624446170209 6323024189362218334627657)
      ·
        refine ⟨4742268142021663750970743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6323024189362218334627657 4742268142021663750970743)
        ·
          refine ⟨7113402213032495626456115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742268142021663750970743 7113402213032495626456115)
          ·
            refine ⟨10670103319548743439684173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7113402213032495626456115 10670103319548743439684173)
            ·
              refine ⟨4001288744830778789881565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10670103319548743439684173 4001288744830778789881565)
              ·
                refine ⟨1500483279311542046205587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4001288744830778789881565 1500483279311542046205587)
                ·
                  refine ⟨2250724918967313069308381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500483279311542046205587 2250724918967313069308381)
                  ·
                    refine ⟨844021844612742400990643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2250724918967313069308381 844021844612742400990643)
                    ·
                      rfl

theorem cell22_2465590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2465590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465590 prefixEnd_2465590 := by exact prefixLift 2465590
  have htrace : WordTrace (prefixWord ++ tailWord_2465590) baseStart_2465590 baseEnd_2465590 := by
    simpa [prefixWord, tailWord_2465590, baseEnd_2465590] using wordTrace_append hprefix tailTrace_2465590
  have hstable : (prefixWord ++ tailWord_2465590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465590).length < 2 ^ (prefixWord ++ tailWord_2465590).sum := by decide
  have hdescent : baseEnd_2465590 < baseStart_2465590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465644 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_2465644 : Nat := 118140960795 + 2465644 * 2 ^ 59
def prefixEnd_2465644 : Nat := 4983230072969 + 3 ^ 40 * 2465644 * 2
def baseEnd_2465644 : Nat := 844040329916304260140477

theorem tailTrace_2465644 : CollatzResearch.WordTrace tailWord_2465644 prefixEnd_2465644 844040329916304260140477 := by
  unfold tailWord_2465644
  simp only [CollatzResearch.WordTrace]
  refine ⟨44964712339700180657473993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59952949786266907543298657 44964712339700180657473993)
  ·
    refine ⟨33723534254775135493105495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44964712339700180657473993 33723534254775135493105495)
    ·
      refine ⟨50585301382162703239658243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33723534254775135493105495 50585301382162703239658243)
      ·
        refine ⟨75877952073244054859487365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50585301382162703239658243 75877952073244054859487365)
        ·
          refine ⟨14227116013733260286153881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75877952073244054859487365 14227116013733260286153881)
          ·
            refine ⟨10670337010299945214615411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14227116013733260286153881 10670337010299945214615411)
            ·
              refine ⟨16005505515449917821923117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10670337010299945214615411 16005505515449917821923117)
              ·
                refine ⟨6002064568293719183221169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16005505515449917821923117 6002064568293719183221169)
                ·
                  refine ⟨4501548426220289387415877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6002064568293719183221169 4501548426220289387415877)
                  ·
                    refine ⟨844040329916304260140477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501548426220289387415877 844040329916304260140477)
                    ·
                      rfl

theorem cell22_2465644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_2465644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465644 prefixEnd_2465644 := by exact prefixLift 2465644
  have htrace : WordTrace (prefixWord ++ tailWord_2465644) baseStart_2465644 baseEnd_2465644 := by
    simpa [prefixWord, tailWord_2465644, baseEnd_2465644] using wordTrace_append hprefix tailTrace_2465644
  have hstable : (prefixWord ++ tailWord_2465644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465644).length < 2 ^ (prefixWord ++ tailWord_2465644).sum := by decide
  have hdescent : baseEnd_2465644 < baseStart_2465644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465646 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2465646 : Nat := 118140960795 + 2465646 * 2 ^ 59
def prefixEnd_2465646 : Nat := 4983230072969 + 3 ^ 40 * 2465646 * 2
def baseEnd_2465646 : Nat := 844041014557176921590471

theorem tailTrace_2465646 : CollatzResearch.WordTrace tailWord_2465646 prefixEnd_2465646 844041014557176921590471 := by
  unfold tailWord_2465646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11241187203174139457065099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59952998416928743771013861 11241187203174139457065099)
  ·
    refine ⟨16861780804761209185597649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11241187203174139457065099 16861780804761209185597649)
    ·
      refine ⟨12646335603570906889198237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16861780804761209185597649 12646335603570906889198237)
      ·
        refine ⟨4742375851339090083449339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12646335603570906889198237 4742375851339090083449339)
        ·
          refine ⟨7113563777008635125174009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742375851339090083449339 7113563777008635125174009)
          ·
            refine ⟨5335172832756476343880507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7113563777008635125174009 5335172832756476343880507)
            ·
              refine ⟨8002759249134714515820761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5335172832756476343880507 8002759249134714515820761)
              ·
                refine ⟨6002069436851035886865571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8002759249134714515820761 6002069436851035886865571)
                ·
                  refine ⟨9003104155276553830298357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6002069436851035886865571 9003104155276553830298357)
                  ·
                    refine ⟨844041014557176921590471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9003104155276553830298357 844041014557176921590471)
                    ·
                      rfl

theorem cell22_2465646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2465646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465646 prefixEnd_2465646 := by exact prefixLift 2465646
  have htrace : WordTrace (prefixWord ++ tailWord_2465646) baseStart_2465646 baseEnd_2465646 := by
    simpa [prefixWord, tailWord_2465646, baseEnd_2465646] using wordTrace_append hprefix tailTrace_2465646
  have hstable : (prefixWord ++ tailWord_2465646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465646).length < 2 ^ (prefixWord ++ tailWord_2465646).sum := by decide
  have hdescent : baseEnd_2465646 < baseStart_2465646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465751 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 1, 4]
def baseStart_2465751 : Nat := 118140960795 + 2465751 * 2 ^ 59
def prefixEnd_2465751 : Nat := 4983230072969 + 3 ^ 40 * 2465751 * 2
def baseEnd_2465751 : Nat := 844076958202991647715149

theorem tailTrace_2465751 : CollatzResearch.WordTrace tailWord_2465751 prefixEnd_2465751 844076958202991647715149 := by
  unfold tailWord_2465751
  simp only [CollatzResearch.WordTrace]
  refine ⟨89933327290012718589093107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59955551526675145726062071 89933327290012718589093107)
  ·
    refine ⟨134899990935019077883639661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89933327290012718589093107 134899990935019077883639661)
    ·
      refine ⟨50587496600632154206364873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134899990935019077883639661 50587496600632154206364873)
      ·
        refine ⟨37940622450474115654773655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50587496600632154206364873 37940622450474115654773655)
        ·
          refine ⟨56910933675711173482160483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37940622450474115654773655 56910933675711173482160483)
          ·
            refine ⟨85366400513566760223240725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56910933675711173482160483 85366400513566760223240725)
            ·
              refine ⟨4001550024073441885464409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85366400513566760223240725 4001550024073441885464409)
              ·
                refine ⟨3001162518055081414098307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4001550024073441885464409 3001162518055081414098307)
                ·
                  refine ⟨4501743777082622121147461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001162518055081414098307 4501743777082622121147461)
                  ·
                    refine ⟨844076958202991647715149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501743777082622121147461 844076958202991647715149)
                    ·
                      rfl

theorem cell22_2465751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_2465751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465751 prefixEnd_2465751 := by exact prefixLift 2465751
  have htrace : WordTrace (prefixWord ++ tailWord_2465751) baseStart_2465751 baseEnd_2465751 := by
    simpa [prefixWord, tailWord_2465751, baseEnd_2465751] using wordTrace_append hprefix tailTrace_2465751
  have hstable : (prefixWord ++ tailWord_2465751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465751).length < 2 ^ (prefixWord ++ tailWord_2465751).sum := by decide
  have hdescent : baseEnd_2465751 < baseStart_2465751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465764 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_2465764 : Nat := 118140960795 + 2465764 * 2 ^ 59
def prefixEnd_2465764 : Nat := 4983230072969 + 3 ^ 40 * 2465764 * 2
def baseEnd_2465764 : Nat := 844081408368663947140109

theorem tailTrace_2465764 : CollatzResearch.WordTrace tailWord_2465764 prefixEnd_2465764 844081408368663947140109 := by
  unfold tailWord_2465764
  simp only [CollatzResearch.WordTrace]
  refine ⟨44966900719482810904658173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59955867625977081206210897 44966900719482810904658173)
  ·
    refine ⟨16862587769806054089246815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44966900719482810904658173 16862587769806054089246815)
    ·
      refine ⟨25293881654709081133870223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16862587769806054089246815 25293881654709081133870223)
      ·
        refine ⟨37940822482063621700805335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25293881654709081133870223 37940822482063621700805335)
        ·
          refine ⟨56911233723095432551208003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37940822482063621700805335 56911233723095432551208003)
          ·
            refine ⟨85366850584643148826812005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56911233723095432551208003 85366850584643148826812005)
            ·
              refine ⟨16006284484620590405027251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85366850584643148826812005 16006284484620590405027251)
              ·
                refine ⟨24009426726930885607540877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16006284484620590405027251 24009426726930885607540877)
                ·
                  refine ⟨9003535022599082102827829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24009426726930885607540877 9003535022599082102827829)
                  ·
                    refine ⟨844081408368663947140109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9003535022599082102827829 844081408368663947140109)
                    ·
                      rfl

theorem cell22_2465764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_2465764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465764 prefixEnd_2465764 := by exact prefixLift 2465764
  have htrace : WordTrace (prefixWord ++ tailWord_2465764) baseStart_2465764 baseEnd_2465764 := by
    simpa [prefixWord, tailWord_2465764, baseEnd_2465764] using wordTrace_append hprefix tailTrace_2465764
  have hstable : (prefixWord ++ tailWord_2465764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465764).length < 2 ^ (prefixWord ++ tailWord_2465764).sum := by decide
  have hdescent : baseEnd_2465764 < baseStart_2465764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465813 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2465813 : Nat := 118140960795 + 2465813 * 2 ^ 59
def prefixEnd_2465813 : Nat := 4983230072969 + 3 ^ 40 * 2465813 * 2
def baseEnd_2465813 : Nat := 844098182070044152664959

theorem tailTrace_2465813 : CollatzResearch.WordTrace tailWord_2465813 prefixEnd_2465813 844098182070044152664959 := by
  unfold tailWord_2465813
  simp only [CollatzResearch.WordTrace]
  refine ⟨89935588615788103177850093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59957059077192068785233395 89935588615788103177850093)
  ·
    refine ⟨33725845730920538691693785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89935588615788103177850093 33725845730920538691693785)
    ·
      refine ⟨25294384298190404018770339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33725845730920538691693785 25294384298190404018770339)
      ·
        refine ⟨37941576447285606028155509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25294384298190404018770339 37941576447285606028155509)
        ·
          refine ⟨3557022791933025565139579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37941576447285606028155509 3557022791933025565139579)
          ·
            refine ⟨5335534187899538347709369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557022791933025565139579 5335534187899538347709369)
            ·
              refine ⟨4001650640924653760782027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5335534187899538347709369 4001650640924653760782027)
              ·
                refine ⟨6002475961386980641173041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4001650640924653760782027 6002475961386980641173041)
                ·
                  refine ⟨4501856971040235480879781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6002475961386980641173041 4501856971040235480879781)
                  ·
                    refine ⟨844098182070044152664959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501856971040235480879781 844098182070044152664959)
                    ·
                      rfl

theorem cell22_2465813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2465813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465813 prefixEnd_2465813 := by exact prefixLift 2465813
  have htrace : WordTrace (prefixWord ++ tailWord_2465813) baseStart_2465813 baseEnd_2465813 := by
    simpa [prefixWord, tailWord_2465813, baseEnd_2465813] using wordTrace_append hprefix tailTrace_2465813
  have hstable : (prefixWord ++ tailWord_2465813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465813).length < 2 ^ (prefixWord ++ tailWord_2465813).sum := by decide
  have hdescent : baseEnd_2465813 < baseStart_2465813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465832 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2465832 : Nat := 118140960795 + 2465832 * 2 ^ 59
def prefixEnd_2465832 : Nat := 4983230072969 + 3 ^ 40 * 2465832 * 2
def baseEnd_2465832 : Nat := 844104686158334436439901

theorem tailTrace_2465832 : CollatzResearch.WordTrace tailWord_2465832 prefixEnd_2465832 844104686158334436439901 := by
  unfold tailWord_2465832
  simp only [CollatzResearch.WordTrace]
  refine ⟨44968140801359634711395875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59957521068479512948527833 44968140801359634711395875)
  ·
    refine ⟨67452211202039452067093813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44968140801359634711395875 67452211202039452067093813)
    ·
      refine ⟨6323644800191198631290045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67452211202039452067093813 6323644800191198631290045)
      ·
        refine ⟨2371366800071699486733767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6323644800191198631290045 2371366800071699486733767)
        ·
          refine ⟨3557050200107549230100651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371366800071699486733767 3557050200107549230100651)
          ·
            refine ⟨5335575300161323845150977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557050200107549230100651 5335575300161323845150977)
            ·
              refine ⟨4001681475120992883863233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5335575300161323845150977 4001681475120992883863233)
              ·
                refine ⟨3001261106340744662897425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4001681475120992883863233 3001261106340744662897425)
                ·
                  refine ⟨2250945829755558497173069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3001261106340744662897425 2250945829755558497173069)
                  ·
                    refine ⟨844104686158334436439901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2250945829755558497173069 844104686158334436439901)
                    ·
                      rfl

theorem cell22_2465832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2465832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465832 prefixEnd_2465832 := by exact prefixLift 2465832
  have htrace : WordTrace (prefixWord ++ tailWord_2465832) baseStart_2465832 baseEnd_2465832 := by
    simpa [prefixWord, tailWord_2465832, baseEnd_2465832] using wordTrace_append hprefix tailTrace_2465832
  have hstable : (prefixWord ++ tailWord_2465832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465832).length < 2 ^ (prefixWord ++ tailWord_2465832).sum := by decide
  have hdescent : baseEnd_2465832 < baseStart_2465832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465856 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_2465856 : Nat := 118140960795 + 2465856 * 2 ^ 59
def prefixEnd_2465856 : Nat := 4983230072969 + 3 ^ 40 * 2465856 * 2
def baseEnd_2465856 : Nat := 281370967282935457946609

theorem tailTrace_2465856 : CollatzResearch.WordTrace tailWord_2465856 prefixEnd_2465856 281370967282935457946609 := by
  unfold tailWord_2465856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44968578477316160760832711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59958104636421547681110281 44968578477316160760832711)
  ·
    refine ⟨67452867715974241141249067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44968578477316160760832711 67452867715974241141249067)
    ·
      refine ⟨101179301573961361711873601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67452867715974241141249067 101179301573961361711873601)
      ·
        refine ⟨75884476180471021283905201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101179301573961361711873601 75884476180471021283905201)
        ·
          refine ⟨56913357135353265962928901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75884476180471021283905201 56913357135353265962928901)
          ·
            refine ⟨10671254462878737368049169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56913357135353265962928901 10671254462878737368049169)
            ·
              refine ⟨8003440847159053026036877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10671254462878737368049169 8003440847159053026036877)
              ·
                refine ⟨3001290317684644884763829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8003440847159053026036877 3001290317684644884763829)
                ·
                  refine ⟨281370967282935457946609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3001290317684644884763829 281370967282935457946609)
                  ·
                    rfl

theorem cell22_2465856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_2465856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465856 prefixEnd_2465856 := by exact prefixLift 2465856
  have htrace : WordTrace (prefixWord ++ tailWord_2465856) baseStart_2465856 baseEnd_2465856 := by
    simpa [prefixWord, tailWord_2465856, baseEnd_2465856] using wordTrace_append hprefix tailTrace_2465856
  have hstable : (prefixWord ++ tailWord_2465856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465856).length < 2 ^ (prefixWord ++ tailWord_2465856).sum := by decide
  have hdescent : baseEnd_2465856 < baseStart_2465856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465899 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_2465899 : Nat := 118140960795 + 2465899 * 2 ^ 59
def prefixEnd_2465899 : Nat := 4983230072969 + 3 ^ 40 * 2465899 * 2
def baseEnd_2465899 : Nat := 844127621627568595014695

theorem tailTrace_2465899 : CollatzResearch.WordTrace tailWord_2465899 prefixEnd_2465899 844127621627568595014695 := by
  unfold tailWord_2465899
  simp only [CollatzResearch.WordTrace]
  refine ⟨89938725293476539865480751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59959150195651026576987167 89938725293476539865480751)
  ·
    refine ⟨134908087940214809798221127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89938725293476539865480751 134908087940214809798221127)
    ·
      refine ⟨202362131910322214697331691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134908087940214809798221127 202362131910322214697331691)
      ·
        refine ⟨303543197865483322045997537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202362131910322214697331691 303543197865483322045997537)
        ·
          refine ⟨227657398399112491534498153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303543197865483322045997537 227657398399112491534498153)
          ·
            refine ⟨170743048799334368650873615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227657398399112491534498153 170743048799334368650873615)
            ·
              refine ⟨256114573199001552976310423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170743048799334368650873615 256114573199001552976310423)
              ·
                refine ⟨384171859798502329464465635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256114573199001552976310423 384171859798502329464465635)
                ·
                  refine ⟨576257789697753494196698453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384171859798502329464465635 576257789697753494196698453)
                  ·
                    refine ⟨844127621627568595014695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 576257789697753494196698453 844127621627568595014695)
                    ·
                      rfl

theorem cell22_2465899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_2465899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465899 prefixEnd_2465899 := by exact prefixLift 2465899
  have htrace : WordTrace (prefixWord ++ tailWord_2465899) baseStart_2465899 baseEnd_2465899 := by
    simpa [prefixWord, tailWord_2465899, baseEnd_2465899] using wordTrace_append hprefix tailTrace_2465899
  have hstable : (prefixWord ++ tailWord_2465899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465899).length < 2 ^ (prefixWord ++ tailWord_2465899).sum := by decide
  have hdescent : baseEnd_2465899 < baseStart_2465899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465948 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2465948 : Nat := 118140960795 + 2465948 * 2 ^ 59
def prefixEnd_2465948 : Nat := 4983230072969 + 3 ^ 40 * 2465948 * 2
def baseEnd_2465948 : Nat := 844144395328948800539545

theorem tailTrace_2465948 : CollatzResearch.WordTrace tailWord_2465948 prefixEnd_2465948 844144395328948800539545 := by
  unfold tailWord_2465948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44970256235149510617007249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59960341646866014156009665 44970256235149510617007249)
  ·
    refine ⟨33727692176362132962755437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44970256235149510617007249 33727692176362132962755437)
    ·
      refine ⟨12647884566135799861033289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33727692176362132962755437 12647884566135799861033289)
      ·
        refine ⟨9485913424601849895774967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12647884566135799861033289 9485913424601849895774967)
        ·
          refine ⟨14228870136902774843662451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9485913424601849895774967 14228870136902774843662451)
          ·
            refine ⟨21343305205354162265493677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14228870136902774843662451 21343305205354162265493677)
            ·
              refine ⟨8003739452007810849560129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21343305205354162265493677 8003739452007810849560129)
              ·
                refine ⟨6002804589005858137170097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8003739452007810849560129 6002804589005858137170097)
                ·
                  refine ⟨4502103441754393602877573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6002804589005858137170097 4502103441754393602877573)
                  ·
                    refine ⟨844144395328948800539545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4502103441754393602877573 844144395328948800539545)
                    ·
                      rfl

theorem cell22_2465948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2465948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465948 prefixEnd_2465948 := by exact prefixLift 2465948
  have htrace : WordTrace (prefixWord ++ tailWord_2465948) baseStart_2465948 baseEnd_2465948 := by
    simpa [prefixWord, tailWord_2465948, baseEnd_2465948] using wordTrace_append hprefix tailTrace_2465948
  have hstable : (prefixWord ++ tailWord_2465948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465948).length < 2 ^ (prefixWord ++ tailWord_2465948).sum := by decide
  have hdescent : baseEnd_2465948 < baseStart_2465948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465978 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_2465978 : Nat := 118140960795 + 2465978 * 2 ^ 59
def prefixEnd_2465978 : Nat := 4983230072969 + 3 ^ 40 * 2465978 * 2
def baseEnd_2465978 : Nat := 844154664942038722289453

theorem tailTrace_2465978 : CollatzResearch.WordTrace tailWord_2465978 prefixEnd_2465978 844154664942038722289453 := by
  unfold tailWord_2465978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22485401665047584089401647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59961071106793557571737725 22485401665047584089401647)
  ·
    refine ⟨33728102497571376134102471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22485401665047584089401647 33728102497571376134102471)
    ·
      refine ⟨50592153746357064201153707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33728102497571376134102471 50592153746357064201153707)
      ·
        refine ⟨75888230619535596301730561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50592153746357064201153707 75888230619535596301730561)
        ·
          refine ⟨56916172964651697226297921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75888230619535596301730561 56916172964651697226297921)
          ·
            refine ⟨42687129723488772919723441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56916172964651697226297921 42687129723488772919723441)
            ·
              refine ⟨32015347292616579689792581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42687129723488772919723441 32015347292616579689792581)
              ·
                refine ⟨6002877617365608691836109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32015347292616579689792581 6002877617365608691836109)
                ·
                  refine ⟨2251079106512103259438541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6002877617365608691836109 2251079106512103259438541)
                  ·
                    refine ⟨844154664942038722289453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251079106512103259438541 844154664942038722289453)
                    ·
                      rfl

theorem cell22_2465978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_2465978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465978 prefixEnd_2465978 := by exact prefixLift 2465978
  have htrace : WordTrace (prefixWord ++ tailWord_2465978) baseStart_2465978 baseEnd_2465978 := by
    simpa [prefixWord, tailWord_2465978, baseEnd_2465978] using wordTrace_append hprefix tailTrace_2465978
  have hstable : (prefixWord ++ tailWord_2465978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465978).length < 2 ^ (prefixWord ++ tailWord_2465978).sum := by decide
  have hdescent : baseEnd_2465978 < baseStart_2465978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465995 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 1, 3]
def baseStart_2465995 : Nat := 118140960795 + 2465995 * 2 ^ 59
def prefixEnd_2465995 : Nat := 4983230072969 + 3 ^ 40 * 2465995 * 2
def baseEnd_2465995 : Nat := 844160484389456344614401

theorem tailTrace_2465995 : CollatzResearch.WordTrace tailWord_2465995 prefixEnd_2465995 844160484389456344614401 := by
  unfold tailWord_2465995
  simp only [CollatzResearch.WordTrace]
  refine ⟨89942226701128748260975439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59961484467419165507316959 89942226701128748260975439)
  ·
    refine ⟨134913340051693122391463159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89942226701128748260975439 134913340051693122391463159)
    ·
      refine ⟨202370010077539683587194739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134913340051693122391463159 202370010077539683587194739)
      ·
        refine ⟨303555015116309525380792109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202370010077539683587194739 303555015116309525380792109)
        ·
          refine ⟨113833130668616072017797041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303555015116309525380792109 113833130668616072017797041)
          ·
            refine ⟨85374848001462054013347781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113833130668616072017797041 85374848001462054013347781)
            ·
              refine ⟨16007784000274135127502709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85374848001462054013347781 16007784000274135127502709)
              ·
                refine ⟨1500729750025700168203379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16007784000274135127502709 1500729750025700168203379)
                ·
                  refine ⟨2251094625038550252305069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500729750025700168203379 2251094625038550252305069)
                  ·
                    refine ⟨844160484389456344614401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251094625038550252305069 844160484389456344614401)
                    ·
                      rfl

theorem cell22_2465995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 3].length) (baseStart_2465995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2465995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2465995 prefixEnd_2465995 := by exact prefixLift 2465995
  have htrace : WordTrace (prefixWord ++ tailWord_2465995) baseStart_2465995 baseEnd_2465995 := by
    simpa [prefixWord, tailWord_2465995, baseEnd_2465995] using wordTrace_append hprefix tailTrace_2465995
  have hstable : (prefixWord ++ tailWord_2465995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465995).length < 2 ^ (prefixWord ++ tailWord_2465995).sum := by decide
  have hdescent : baseEnd_2465995 < baseStart_2465995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466008 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_2466008 : Nat := 118140960795 + 2466008 * 2 ^ 59
def prefixEnd_2466008 : Nat := 4983230072969 + 3 ^ 40 * 2466008 * 2
def baseEnd_2466008 : Nat := 281388311518376214679787

theorem tailTrace_2466008 : CollatzResearch.WordTrace tailWord_2466008 prefixEnd_2466008 281388311518376214679787 := by
  unfold tailWord_2466008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44971350425040825740599339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59961800566721100987465785 44971350425040825740599339)
  ·
    refine ⟨67457025637561238610899009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44971350425040825740599339 67457025637561238610899009)
    ·
      refine ⟨50592769228170928958174257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67457025637561238610899009 50592769228170928958174257)
      ·
        refine ⟨37944576921128196718630693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50592769228170928958174257 37944576921128196718630693)
        ·
          refine ⟨7114608172711536884743255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37944576921128196718630693 7114608172711536884743255)
          ·
            refine ⟨10671912259067305327114883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7114608172711536884743255 10671912259067305327114883)
            ·
              refine ⟨16007868388600957990672325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10671912259067305327114883 16007868388600957990672325)
              ·
                refine ⟨3001475322862679623251061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16007868388600957990672325 3001475322862679623251061)
                ·
                  refine ⟨281388311518376214679787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3001475322862679623251061 281388311518376214679787)
                  ·
                    rfl

theorem cell22_2466008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_2466008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466008 prefixEnd_2466008 := by exact prefixLift 2466008
  have htrace : WordTrace (prefixWord ++ tailWord_2466008) baseStart_2466008 baseEnd_2466008 := by
    simpa [prefixWord, tailWord_2466008, baseEnd_2466008] using wordTrace_append hprefix tailTrace_2466008
  have hstable : (prefixWord ++ tailWord_2466008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466008).length < 2 ^ (prefixWord ++ tailWord_2466008).sum := by decide
  have hdescent : baseEnd_2466008 < baseStart_2466008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466023 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2466023 : Nat := 118140960795 + 2466023 * 2 ^ 59
def prefixEnd_2466023 : Nat := 4983230072969 + 3 ^ 40 * 2466023 * 2
def baseEnd_2466023 : Nat := 844170069361673604914315

theorem tailTrace_2466023 : CollatzResearch.WordTrace tailWord_2466023 prefixEnd_2466023 844170069361673604914315 := by
  unfold tailWord_2466023
  simp only [CollatzResearch.WordTrace]
  refine ⟨89943247945027309042994723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59962165296684872695329815 89943247945027309042994723)
  ·
    refine ⟨134914871917540963564492085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89943247945027309042994723 134914871917540963564492085)
    ·
      refine ⟨12648269242269465334171133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134914871917540963564492085 12648269242269465334171133)
      ·
        refine ⟨4743100965851049500314175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12648269242269465334171133 4743100965851049500314175)
        ·
          refine ⟨7114651448776574250471263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743100965851049500314175 7114651448776574250471263)
          ·
            refine ⟨10671977173164861375706895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7114651448776574250471263 10671977173164861375706895)
            ·
              refine ⟨16007965759747292063560343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10671977173164861375706895 16007965759747292063560343)
              ·
                refine ⟨24011948639620938095340515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16007965759747292063560343 24011948639620938095340515)
                ·
                  refine ⟨36017922959431407143010773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24011948639620938095340515 36017922959431407143010773)
                  ·
                    refine ⟨844170069361673604914315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36017922959431407143010773 844170069361673604914315)
                    ·
                      rfl

theorem cell22_2466023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2466023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466023 prefixEnd_2466023 := by exact prefixLift 2466023
  have htrace : WordTrace (prefixWord ++ tailWord_2466023) baseStart_2466023 baseEnd_2466023 := by
    simpa [prefixWord, tailWord_2466023, baseEnd_2466023] using wordTrace_append hprefix tailTrace_2466023
  have hstable : (prefixWord ++ tailWord_2466023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466023).length < 2 ^ (prefixWord ++ tailWord_2466023).sum := by decide
  have hdescent : baseEnd_2466023 < baseStart_2466023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466100 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2466100 : Nat := 118140960795 + 2466100 * 2 ^ 59
def prefixEnd_2466100 : Nat := 4983230072969 + 3 ^ 40 * 2466100 * 2
def baseEnd_2466100 : Nat := 844196428035271070739079

theorem tailTrace_2466100 : CollatzResearch.WordTrace tailWord_2466100 prefixEnd_2466100 844196428035271070739079 := by
  unfold tailWord_2466100
  simp only [CollatzResearch.WordTrace]
  refine ⟨44973028182874175596773877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59964037577165567462365169 44973028182874175596773877)
  ·
    refine ⟨4216221392144453962197551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44973028182874175596773877 4216221392144453962197551)
    ·
      refine ⟨6324332088216680943296327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216221392144453962197551 6324332088216680943296327)
      ·
        refine ⟨9486498132325021414944491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324332088216680943296327 9486498132325021414944491)
        ·
          refine ⟨14229747198487532122416737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9486498132325021414944491 14229747198487532122416737)
          ·
            refine ⟨10672310398865649091812553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14229747198487532122416737 10672310398865649091812553)
            ·
              refine ⟨8004232799149236818859415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10672310398865649091812553 8004232799149236818859415)
              ·
                refine ⟨12006349198723855228289123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8004232799149236818859415 12006349198723855228289123)
                ·
                  refine ⟨18009523798085782842433685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12006349198723855228289123 18009523798085782842433685)
                  ·
                    refine ⟨844196428035271070739079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18009523798085782842433685 844196428035271070739079)
                    ·
                      rfl

theorem cell22_2466100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2466100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466100 prefixEnd_2466100 := by exact prefixLift 2466100
  have htrace : WordTrace (prefixWord ++ tailWord_2466100) baseStart_2466100 baseEnd_2466100 := by
    simpa [prefixWord, tailWord_2466100, baseEnd_2466100] using wordTrace_append hprefix tailTrace_2466100
  have hstable : (prefixWord ++ tailWord_2466100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466100).length < 2 ^ (prefixWord ++ tailWord_2466100).sum := by decide
  have hdescent : baseEnd_2466100 < baseStart_2466100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466177 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 5]
def baseStart_2466177 : Nat := 118140960795 + 2466177 * 2 ^ 59
def prefixEnd_2466177 : Nat := 4983230072969 + 3 ^ 40 * 2466177 * 2
def baseEnd_2466177 : Nat := 281407595569622845521281

theorem tailTrace_2466177 : CollatzResearch.WordTrace tailWord_2466177 prefixEnd_2466177 281407595569622845521281 := by
  unfold tailWord_2466177
  simp only [CollatzResearch.WordTrace]
  refine ⟨89948864786469393344100785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59965909857646262229400523 89948864786469393344100785)
  ·
    refine ⟨67461648589852045008075589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89948864786469393344100785 67461648589852045008075589)
    ·
      refine ⟨12649059110597258439014173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67461648589852045008075589 12649059110597258439014173)
      ·
        refine ⟨4743397166473971914630315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12649059110597258439014173 4743397166473971914630315)
        ·
          refine ⟨7115095749710957871945473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743397166473971914630315 7115095749710957871945473)
          ·
            refine ⟨5336321812283218403959105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7115095749710957871945473 5336321812283218403959105)
            ·
              refine ⟨4002241359212413802969329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5336321812283218403959105 4002241359212413802969329)
              ·
                refine ⟨3001681019409310352226997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002241359212413802969329 3001681019409310352226997)
                ·
                  refine ⟨281407595569622845521281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3001681019409310352226997 281407595569622845521281)
                  ·
                    rfl

theorem cell22_2466177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_2466177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466177 prefixEnd_2466177 := by exact prefixLift 2466177
  have htrace : WordTrace (prefixWord ++ tailWord_2466177) baseStart_2466177 baseEnd_2466177 := by
    simpa [prefixWord, tailWord_2466177, baseEnd_2466177] using wordTrace_append hprefix tailTrace_2466177
  have hstable : (prefixWord ++ tailWord_2466177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466177).length < 2 ^ (prefixWord ++ tailWord_2466177).sum := by decide
  have hdescent : baseEnd_2466177 < baseStart_2466177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466198 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2466198 : Nat := 118140960795 + 2466198 * 2 ^ 59
def prefixEnd_2466198 : Nat := 4983230072969 + 3 ^ 40 * 2466198 * 2
def baseEnd_2466198 : Nat := 844229975438031481788779

theorem tailTrace_2466198 : CollatzResearch.WordTrace tailWord_2466198 prefixEnd_2466198 844229975438031481788779 := by
  unfold tailWord_2466198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621851919962082120663453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59966420479595542620410165 5621851919962082120663453)
  ·
    refine ⟨2108194469985780795248795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5621851919962082120663453 2108194469985780795248795)
    ·
      refine ⟨3162291704978671192873193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108194469985780795248795 3162291704978671192873193)
      ·
        refine ⟨2371718778734003394654895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3162291704978671192873193 2371718778734003394654895)
        ·
          refine ⟨3557578168101005091982343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371718778734003394654895 3557578168101005091982343)
          ·
            refine ⟨5336367252151507637973515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557578168101005091982343 5336367252151507637973515)
            ·
              refine ⟨8004550878227261456960273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336367252151507637973515 8004550878227261456960273)
              ·
                refine ⟨6003413158670446092720205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8004550878227261456960273 6003413158670446092720205)
                ·
                  refine ⟨2251279934501417284770077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6003413158670446092720205 2251279934501417284770077)
                  ·
                    refine ⟨844229975438031481788779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251279934501417284770077 844229975438031481788779)
                    ·
                      rfl

theorem cell22_2466198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2466198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466198 prefixEnd_2466198 := by exact prefixLift 2466198
  have htrace : WordTrace (prefixWord ++ tailWord_2466198) baseStart_2466198 baseEnd_2466198 := by
    simpa [prefixWord, tailWord_2466198, baseEnd_2466198] using wordTrace_append hprefix tailTrace_2466198
  have hstable : (prefixWord ++ tailWord_2466198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466198).length < 2 ^ (prefixWord ++ tailWord_2466198).sum := by decide
  have hdescent : baseEnd_2466198 < baseStart_2466198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466220 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_2466220 : Nat := 118140960795 + 2466220 * 2 ^ 59
def prefixEnd_2466220 : Nat := 4983230072969 + 3 ^ 40 * 2466220 * 2
def baseEnd_2466220 : Nat := 844237506487630757738711

theorem tailTrace_2466220 : CollatzResearch.WordTrace tailWord_2466220 prefixEnd_2466220 844237506487630757738711 := by
  unfold tailWord_2466220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44975216562656805843958057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59966955416875741125277409 44975216562656805843958057)
  ·
    refine ⟨33731412421992604382968543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44975216562656805843958057 33731412421992604382968543)
    ·
      refine ⟨50597118632988906574452815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33731412421992604382968543 50597118632988906574452815)
      ·
        refine ⟨75895677949483359861679223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50597118632988906574452815 75895677949483359861679223)
        ·
          refine ⟨113843516924225039792518835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75895677949483359861679223 113843516924225039792518835)
          ·
            refine ⟨170765275386337559688778253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113843516924225039792518835 170765275386337559688778253)
            ·
              refine ⟨64036978269876584883291845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170765275386337559688778253 64036978269876584883291845)
              ·
                refine ⟨12006933425601859665617221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64036978269876584883291845 12006933425601859665617221)
                ·
                  refine ⟨2251300017300348687303229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12006933425601859665617221 2251300017300348687303229)
                  ·
                    refine ⟨844237506487630757738711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251300017300348687303229 844237506487630757738711)
                    ·
                      rfl

theorem cell22_2466220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_2466220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466220 prefixEnd_2466220 := by exact prefixLift 2466220
  have htrace : WordTrace (prefixWord ++ tailWord_2466220) baseStart_2466220 baseEnd_2466220 := by
    simpa [prefixWord, tailWord_2466220, baseEnd_2466220] using wordTrace_append hprefix tailTrace_2466220
  have hstable : (prefixWord ++ tailWord_2466220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466220).length < 2 ^ (prefixWord ++ tailWord_2466220).sum := by decide
  have hdescent : baseEnd_2466220 < baseStart_2466220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466228 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2466228 : Nat := 118140960795 + 2466228 * 2 ^ 59
def prefixEnd_2466228 : Nat := 4983230072969 + 3 ^ 40 * 2466228 * 2
def baseEnd_2466228 : Nat := 281413415017040467846229

theorem tailTrace_2466228 : CollatzResearch.WordTrace tailWord_2466228 prefixEnd_2466228 281413415017040467846229 := by
  unfold tailWord_2466228
  simp only [CollatzResearch.WordTrace]
  refine ⟨44975362454642314527103669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59967149939523086036138225 44975362454642314527103669)
  ·
    refine ⟨4216440230122716986915969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44975362454642314527103669 4216440230122716986915969)
    ·
      refine ⟨3162330172592037740186977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4216440230122716986915969 3162330172592037740186977)
      ·
        refine ⟨2371747629444028305140233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3162330172592037740186977 2371747629444028305140233)
        ·
          refine ⟨1778810722083021228855175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2371747629444028305140233 1778810722083021228855175)
          ·
            refine ⟨2668216083124531843282763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778810722083021228855175 2668216083124531843282763)
            ·
              refine ⟨4002324124686797764924145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668216083124531843282763 4002324124686797764924145)
              ·
                refine ⟨3001743093515098323693109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002324124686797764924145 3001743093515098323693109)
                ·
                  refine ⟨281413415017040467846229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3001743093515098323693109 281413415017040467846229)
                  ·
                    rfl

theorem cell22_2466228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2466228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466228 prefixEnd_2466228 := by exact prefixLift 2466228
  have htrace : WordTrace (prefixWord ++ tailWord_2466228) baseStart_2466228 baseEnd_2466228 := by
    simpa [prefixWord, tailWord_2466228, baseEnd_2466228] using wordTrace_append hprefix tailTrace_2466228
  have hstable : (prefixWord ++ tailWord_2466228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466228).length < 2 ^ (prefixWord ++ tailWord_2466228).sum := by decide
  have hdescent : baseEnd_2466228 < baseStart_2466228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466237 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_2466237 : Nat := 118140960795 + 2466237 * 2 ^ 59
def prefixEnd_2466237 : Nat := 4983230072969 + 3 ^ 40 * 2466237 * 2
def baseEnd_2466237 : Nat := 844243325935048380063659

theorem tailTrace_2466237 : CollatzResearch.WordTrace tailWord_2466237 prefixEnd_2466237 844243325935048380063659 := by
  unfold tailWord_2466237
  simp only [CollatzResearch.WordTrace]
  refine ⟨89951053166252023591284965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59967368777501349060856643 89951053166252023591284965)
  ·
    refine ⟨16865822468672254423365931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89951053166252023591284965 16865822468672254423365931)
    ·
      refine ⟨25298733703008381635048897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16865822468672254423365931 25298733703008381635048897)
      ·
        refine ⟨18974050277256286226286673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25298733703008381635048897 18974050277256286226286673)
        ·
          refine ⟨14230537707942214669715005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18974050277256286226286673 14230537707942214669715005)
          ·
            refine ⟨5336451640478330501143127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14230537707942214669715005 5336451640478330501143127)
            ·
              refine ⟨8004677460717495751714691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336451640478330501143127 8004677460717495751714691)
              ·
                refine ⟨12007016191076243627572037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8004677460717495751714691 12007016191076243627572037)
                ·
                  refine ⟨2251315535826795680169757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12007016191076243627572037 2251315535826795680169757)
                  ·
                    refine ⟨844243325935048380063659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251315535826795680169757 844243325935048380063659)
                    ·
                      rfl

theorem cell22_2466237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_2466237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466237 prefixEnd_2466237 := by exact prefixLift 2466237
  have htrace : WordTrace (prefixWord ++ tailWord_2466237) baseStart_2466237 baseEnd_2466237 := by
    simpa [prefixWord, tailWord_2466237, baseEnd_2466237] using wordTrace_append hprefix tailTrace_2466237
  have hstable : (prefixWord ++ tailWord_2466237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466237).length < 2 ^ (prefixWord ++ tailWord_2466237).sum := by decide
  have hdescent : baseEnd_2466237 < baseStart_2466237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466350 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2466350 : Nat := 118140960795 + 2466350 * 2 ^ 59
def prefixEnd_2466350 : Nat := 4983230072969 + 3 ^ 40 * 2466350 * 2
def baseEnd_2466350 : Nat := 844282008144353751988313

theorem tailTrace_2466350 : CollatzResearch.WordTrace tailWord_2466350 prefixEnd_2466350 844282008144353751988313 := by
  unfold tailWord_2466350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244396826855330486268563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59970116409895095926765669 11244396826855330486268563)
  ·
    refine ⟨16866595240282995729402845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11244396826855330486268563 16866595240282995729402845)
    ·
      refine ⟨6324973215106123398526067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16866595240282995729402845 6324973215106123398526067)
      ·
        refine ⟨9487459822659185097789101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324973215106123398526067 9487459822659185097789101)
        ·
          refine ⟨3557797433497194411670913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9487459822659185097789101 3557797433497194411670913)
          ·
            refine ⟨2668348075122895808753185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3557797433497194411670913 2668348075122895808753185)
            ·
              refine ⟨2001261056342171856564889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668348075122895808753185 2001261056342171856564889)
              ·
                refine ⟨1500945792256628892423667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001261056342171856564889 1500945792256628892423667)
                ·
                  refine ⟨2251418688384943338635501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500945792256628892423667 2251418688384943338635501)
                  ·
                    refine ⟨844282008144353751988313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251418688384943338635501 844282008144353751988313)
                    ·
                      rfl

theorem cell22_2466350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2466350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466350 prefixEnd_2466350 := by exact prefixLift 2466350
  have htrace : WordTrace (prefixWord ++ tailWord_2466350) baseStart_2466350 baseEnd_2466350 := by
    simpa [prefixWord, tailWord_2466350, baseEnd_2466350] using wordTrace_append hprefix tailTrace_2466350
  have hstable : (prefixWord ++ tailWord_2466350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466350).length < 2 ^ (prefixWord ++ tailWord_2466350).sum := by decide
  have hdescent : baseEnd_2466350 < baseStart_2466350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466355 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_2466355 : Nat := 118140960795 + 2466355 * 2 ^ 59
def prefixEnd_2466355 : Nat := 4983230072969 + 3 ^ 40 * 2466355 * 2
def baseEnd_2466355 : Nat := 844283719746535405613297

theorem tailTrace_2466355 : CollatzResearch.WordTrace tailWord_2466355 prefixEnd_2466355 844283719746535405613297 := by
  unfold tailWord_2466355
  simp only [CollatzResearch.WordTrace]
  refine ⟨89955356979824529744080519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59970237986549686496053679 89955356979824529744080519)
  ·
    refine ⟨134933035469736794616120779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89955356979824529744080519 134933035469736794616120779)
    ·
      refine ⟨202399553204605191924181169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134933035469736794616120779 202399553204605191924181169)
      ·
        refine ⟨151799664903453893943135877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202399553204605191924181169 151799664903453893943135877)
        ·
          refine ⟨28462437169397605114337977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151799664903453893943135877 28462437169397605114337977)
          ·
            refine ⟨21346827877048203835753483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28462437169397605114337977 21346827877048203835753483)
            ·
              refine ⟨32020241815572305753630225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21346827877048203835753483 32020241815572305753630225)
              ·
                refine ⟨24015181361679229315222669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32020241815572305753630225 24015181361679229315222669)
                ·
                  refine ⟨9005693010629710993208501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24015181361679229315222669 9005693010629710993208501)
                  ·
                    refine ⟨844283719746535405613297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9005693010629710993208501 844283719746535405613297)
                    ·
                      rfl

theorem cell22_2466355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_2466355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466355 prefixEnd_2466355 := by exact prefixLift 2466355
  have htrace : WordTrace (prefixWord ++ tailWord_2466355) baseStart_2466355 baseEnd_2466355 := by
    simpa [prefixWord, tailWord_2466355, baseEnd_2466355] using wordTrace_append hprefix tailTrace_2466355
  have hstable : (prefixWord ++ tailWord_2466355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466355).length < 2 ^ (prefixWord ++ tailWord_2466355).sum := by decide
  have hdescent : baseEnd_2466355 < baseStart_2466355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466374 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2466374 : Nat := 118140960795 + 2466374 * 2 ^ 59
def prefixEnd_2466374 : Nat := 4983230072969 + 3 ^ 40 * 2466374 * 2
def baseEnd_2466374 : Nat := 281430074611608563129413

theorem tailTrace_2466374 : CollatzResearch.WordTrace tailWord_2466374 prefixEnd_2466374 281430074611608563129413 := by
  unfold tailWord_2466374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811126561461115499656943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59970699977837130659348117 2811126561461115499656943)
  ·
    refine ⟨4216689842191673249485415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2811126561461115499656943 4216689842191673249485415)
    ·
      refine ⟨6325034763287509874228123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216689842191673249485415 6325034763287509874228123)
      ·
        refine ⟨9487552144931264811342185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325034763287509874228123 9487552144931264811342185)
        ·
          refine ⟨7115664108698448608506639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9487552144931264811342185 7115664108698448608506639)
          ·
            refine ⟨10673496163047672912759959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7115664108698448608506639 10673496163047672912759959)
            ·
              refine ⟨16010244244571509369139939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10673496163047672912759959 16010244244571509369139939)
              ·
                refine ⟨24015366366857264053709909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16010244244571509369139939 24015366366857264053709909)
                ·
                  refine ⟨281430074611608563129413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24015366366857264053709909 281430074611608563129413)
                  ·
                    rfl

theorem cell22_2466374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2466374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466374 prefixEnd_2466374 := by exact prefixLift 2466374
  have htrace : WordTrace (prefixWord ++ tailWord_2466374) baseStart_2466374 baseEnd_2466374 := by
    simpa [prefixWord, tailWord_2466374, baseEnd_2466374] using wordTrace_append hprefix tailTrace_2466374
  have hstable : (prefixWord ++ tailWord_2466374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466374).length < 2 ^ (prefixWord ++ tailWord_2466374).sum := by decide
  have hdescent : baseEnd_2466374 < baseStart_2466374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466415 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_2466415 : Nat := 118140960795 + 2466415 * 2 ^ 59
def prefixEnd_2466415 : Nat := 4983230072969 + 3 ^ 40 * 2466415 * 2
def baseEnd_2466415 : Nat := 844304258972715249113113

theorem tailTrace_2466415 : CollatzResearch.WordTrace tailWord_2466415 prefixEnd_2466415 844304258972715249113113 := by
  unfold tailWord_2466415
  simp only [CollatzResearch.WordTrace]
  refine ⟨89957545359607159991264699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59971696906404773327509799 89957545359607159991264699)
  ·
    refine ⟨134936318039410739986897049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89957545359607159991264699 134936318039410739986897049)
    ·
      refine ⟨101202238529558054990172787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134936318039410739986897049 101202238529558054990172787)
      ·
        refine ⟨151803357794337082485259181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101202238529558054990172787 151803357794337082485259181)
        ·
          refine ⟨56926259172876405931972193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151803357794337082485259181 56926259172876405931972193)
          ·
            refine ⟨42694694379657304448979145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56926259172876405931972193 42694694379657304448979145)
            ·
              refine ⟨32021020784742978336734359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42694694379657304448979145 32021020784742978336734359)
              ·
                refine ⟨48031531177114467505101539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32021020784742978336734359 48031531177114467505101539)
                ·
                  refine ⟨72047296765671701257652309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48031531177114467505101539 72047296765671701257652309)
                  ·
                    refine ⟨844304258972715249113113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72047296765671701257652309 844304258972715249113113)
                    ·
                      rfl

theorem cell22_2466415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_2466415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466415 prefixEnd_2466415 := by exact prefixLift 2466415
  have htrace : WordTrace (prefixWord ++ tailWord_2466415) baseStart_2466415 baseEnd_2466415 := by
    simpa [prefixWord, tailWord_2466415, baseEnd_2466415] using wordTrace_append hprefix tailTrace_2466415
  have hstable : (prefixWord ++ tailWord_2466415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466415).length < 2 ^ (prefixWord ++ tailWord_2466415).sum := by decide
  have hdescent : baseEnd_2466415 < baseStart_2466415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466468 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_2466468 : Nat := 118140960795 + 2466468 * 2 ^ 59
def prefixEnd_2466468 : Nat := 4983230072969 + 3 ^ 40 * 2466468 * 2
def baseEnd_2466468 : Nat := 844322401955840777537951

theorem tailTrace_2466468 : CollatzResearch.WordTrace tailWord_2466468 prefixEnd_2466468 844322401955840777537951 := by
  unfold tailWord_2466468
  simp only [CollatzResearch.WordTrace]
  refine ⟨44979739214207575021472029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59972985618943433361962705 44979739214207575021472029)
  ·
    refine ⟨16867402205327840633052011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44979739214207575021472029 16867402205327840633052011)
    ·
      refine ⟨25301103307991760949578017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16867402205327840633052011 25301103307991760949578017)
      ·
        refine ⟨18975827480993820712183513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25301103307991760949578017 18975827480993820712183513)
        ·
          refine ⟨14231870610745365534137635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18975827480993820712183513 14231870610745365534137635)
          ·
            refine ⟨21347805916118048301206453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14231870610745365534137635 21347805916118048301206453)
            ·
              refine ⟨2001356804636067028238105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21347805916118048301206453 2001356804636067028238105)
              ·
                refine ⟨1501017603477050271178579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001356804636067028238105 1501017603477050271178579)
                ·
                  refine ⟨2251526405215575406767869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501017603477050271178579 2251526405215575406767869)
                  ·
                    refine ⟨844322401955840777537951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251526405215575406767869 844322401955840777537951)
                    ·
                      rfl

theorem cell22_2466468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_2466468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466468 prefixEnd_2466468 := by exact prefixLift 2466468
  have htrace : WordTrace (prefixWord ++ tailWord_2466468) baseStart_2466468 baseEnd_2466468 := by
    simpa [prefixWord, tailWord_2466468, baseEnd_2466468] using wordTrace_append hprefix tailTrace_2466468
  have hstable : (prefixWord ++ tailWord_2466468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466468).length < 2 ^ (prefixWord ++ tailWord_2466468).sum := by decide
  have hdescent : baseEnd_2466468 < baseStart_2466468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466481 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 5]
def baseStart_2466481 : Nat := 118140960795 + 2466481 * 2 ^ 59
def prefixEnd_2466481 : Nat := 4983230072969 + 3 ^ 40 * 2466481 * 2
def baseEnd_2466481 : Nat := 281442284040504358987637

theorem tailTrace_2466481 : CollatzResearch.WordTrace tailWord_2466481 prefixEnd_2466481 281442284040504358987637 := by
  unfold tailWord_2466481
  simp only [CollatzResearch.WordTrace]
  refine ⟨89959952577368053263167297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59973301718245368842111531 89959952577368053263167297)
  ·
    refine ⟨67469964433026039947375473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89959952577368053263167297 67469964433026039947375473)
    ·
      refine ⟨50602473324769529960531605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67469964433026039947375473 50602473324769529960531605)
      ·
        refine ⟨2371990937098571716899919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50602473324769529960531605 2371990937098571716899919)
        ·
          refine ⟨3557986405647857575349879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371990937098571716899919 3557986405647857575349879)
          ·
            refine ⟨5336979608471786363024819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557986405647857575349879 5336979608471786363024819)
            ·
              refine ⟨8005469412707679544537229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336979608471786363024819 8005469412707679544537229)
              ·
                refine ⟨3002051029765379829201461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8005469412707679544537229 3002051029765379829201461)
                ·
                  refine ⟨281442284040504358987637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3002051029765379829201461 281442284040504358987637)
                  ·
                    rfl

theorem cell22_2466481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_2466481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466481 prefixEnd_2466481 := by exact prefixLift 2466481
  have htrace : WordTrace (prefixWord ++ tailWord_2466481) baseStart_2466481 baseEnd_2466481 := by
    simpa [prefixWord, tailWord_2466481, baseEnd_2466481] using wordTrace_append hprefix tailTrace_2466481
  have hstable : (prefixWord ++ tailWord_2466481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466481).length < 2 ^ (prefixWord ++ tailWord_2466481).sum := by decide
  have hdescent : baseEnd_2466481 < baseStart_2466481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466492 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_2466492 : Nat := 118140960795 + 2466492 * 2 ^ 59
def prefixEnd_2466492 : Nat := 4983230072969 + 3 ^ 40 * 2466492 * 2
def baseEnd_2466492 : Nat := 281443539215437571645959

theorem tailTrace_2466492 : CollatzResearch.WordTrace tailWord_2466492 prefixEnd_2466492 281443539215437571645959 := by
  unfold tailWord_2466492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44980176890164101070908865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59973569186885468094545153 44980176890164101070908865)
  ·
    refine ⟨33735132667623075803181649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44980176890164101070908865 33735132667623075803181649)
    ·
      refine ⟨25301349500717306852386237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33735132667623075803181649 25301349500717306852386237)
      ·
        refine ⟨9488006062768990069644839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25301349500717306852386237 9488006062768990069644839)
        ·
          refine ⟨14232009094153485104467259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9488006062768990069644839 14232009094153485104467259)
          ·
            refine ⟨21348013641230227656700889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232009094153485104467259 21348013641230227656700889)
            ·
              refine ⟨16011010230922670742525667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21348013641230227656700889 16011010230922670742525667)
              ·
                refine ⟨24016515346384006113788501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16011010230922670742525667 24016515346384006113788501)
                ·
                  refine ⟨281443539215437571645959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24016515346384006113788501 281443539215437571645959)
                  ·
                    rfl

theorem cell22_2466492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_2466492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466492 prefixEnd_2466492 := by exact prefixLift 2466492
  have htrace : WordTrace (prefixWord ++ tailWord_2466492) baseStart_2466492 baseEnd_2466492 := by
    simpa [prefixWord, tailWord_2466492, baseEnd_2466492] using wordTrace_append hprefix tailTrace_2466492
  have hstable : (prefixWord ++ tailWord_2466492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466492).length < 2 ^ (prefixWord ++ tailWord_2466492).sum := by decide
  have hdescent : baseEnd_2466492 < baseStart_2466492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466494 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2466494 : Nat := 118140960795 + 2466494 * 2 ^ 59
def prefixEnd_2466494 : Nat := 4983230072969 + 3 ^ 40 * 2466494 * 2
def baseEnd_2466494 : Nat := 844331302287185376387871

theorem tailTrace_2466494 : CollatzResearch.WordTrace tailWord_2466494 prefixEnd_2466494 844331302287185376387871 := by
  unfold tailWord_2466494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11245053340790119560423817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59973617817547304322260357 11245053340790119560423817)
  ·
    refine ⟨8433790005592589670317863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11245053340790119560423817 8433790005592589670317863)
    ·
      refine ⟨12650685008388884505476795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8433790005592589670317863 12650685008388884505476795)
      ·
        refine ⟨18976027512583326758215193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12650685008388884505476795 18976027512583326758215193)
        ·
          refine ⟨14232020634437495068661395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18976027512583326758215193 14232020634437495068661395)
          ·
            refine ⟨21348030951656242602992093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232020634437495068661395 21348030951656242602992093)
            ·
              refine ⟨8005511606871090976122035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21348030951656242602992093 8005511606871090976122035)
              ·
                refine ⟨12008267410306636464183053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8005511606871090976122035 12008267410306636464183053)
                ·
                  refine ⟨4503100278864988674068645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12008267410306636464183053 4503100278864988674068645)
                  ·
                    refine ⟨844331302287185376387871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503100278864988674068645 844331302287185376387871)
                    ·
                      rfl

theorem cell22_2466494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2466494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466494 prefixEnd_2466494 := by exact prefixLift 2466494
  have htrace : WordTrace (prefixWord ++ tailWord_2466494) baseStart_2466494 baseEnd_2466494 := by
    simpa [prefixWord, tailWord_2466494, baseEnd_2466494] using wordTrace_append hprefix tailTrace_2466494
  have hstable : (prefixWord ++ tailWord_2466494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466494).length < 2 ^ (prefixWord ++ tailWord_2466494).sum := by decide
  have hdescent : baseEnd_2466494 < baseStart_2466494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466537 : List Nat := [1, 2, 1, 1, 1, 2, 7, 7]
def baseStart_2466537 : Nat := 118140960795 + 2466537 * 2 ^ 59
def prefixEnd_2466537 : Nat := 4983230072969 + 3 ^ 40 * 2466537 * 2
def baseEnd_2466537 : Nat := 93816224673994177506971

theorem tailTrace_2466537 : CollatzResearch.WordTrace tailWord_2466537 prefixEnd_2466537 93816224673994177506971 := by
  unfold tailWord_2466537
  simp only [CollatzResearch.WordTrace]
  refine ⟨89961995065165174827205865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59974663376776783218137243 89961995065165174827205865)
  ·
    refine ⟨67471496298873881120404399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89961995065165174827205865 67471496298873881120404399)
    ·
      refine ⟨101207244448310821680606599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67471496298873881120404399 101207244448310821680606599)
      ·
        refine ⟨151810866672466232520909899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101207244448310821680606599 151810866672466232520909899)
        ·
          refine ⟨227716300008699348781364849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151810866672466232520909899 227716300008699348781364849)
          ·
            refine ⟨170787225006524511586023637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227716300008699348781364849 170787225006524511586023637)
            ·
              refine ⟨4002825586090418240297429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 170787225006524511586023637 4002825586090418240297429)
              ·
                refine ⟨93816224673994177506971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4002825586090418240297429 93816224673994177506971)
                ·
                  rfl

theorem cell22_2466537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 7].length) (baseStart_2466537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466537 prefixEnd_2466537 := by exact prefixLift 2466537
  have htrace : WordTrace (prefixWord ++ tailWord_2466537) baseStart_2466537 baseEnd_2466537 := by
    simpa [prefixWord, tailWord_2466537, baseEnd_2466537] using wordTrace_append hprefix tailTrace_2466537
  have hstable : (prefixWord ++ tailWord_2466537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466537).length < 2 ^ (prefixWord ++ tailWord_2466537).sum := by decide
  have hdescent : baseEnd_2466537 < baseStart_2466537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466541 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2466541 : Nat := 118140960795 + 2466541 * 2 ^ 59
def prefixEnd_2466541 : Nat := 4983230072969 + 3 ^ 40 * 2466541 * 2
def baseEnd_2466541 : Nat := 844347391347692920462727

theorem tailTrace_2466541 : CollatzResearch.WordTrace tailWord_2466541 prefixEnd_2466541 844347391347692920462727 := by
  unfold tailWord_2466541
  simp only [CollatzResearch.WordTrace]
  refine ⟨89962140957150683510351477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59974760638100455673567651 89962140957150683510351477)
  ·
    refine ⟨8433950714732876579095451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89962140957150683510351477 8433950714732876579095451)
    ·
      refine ⟨12650926072099314868643177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8433950714732876579095451 12650926072099314868643177)
      ·
        refine ⟨9488194554074486151482383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12650926072099314868643177 9488194554074486151482383)
        ·
          refine ⟨14232291831111729227223575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9488194554074486151482383 14232291831111729227223575)
          ·
            refine ⟨21348437746667593840835363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232291831111729227223575 21348437746667593840835363)
            ·
              refine ⟨32022656620001390761253045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21348437746667593840835363 32022656620001390761253045)
              ·
                refine ⟨3002124058125130383867473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32022656620001390761253045 3002124058125130383867473)
                ·
                  refine ⟨2251593043593847787900605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002124058125130383867473 2251593043593847787900605)
                  ·
                    refine ⟨844347391347692920462727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251593043593847787900605 844347391347692920462727)
                    ·
                      rfl

theorem cell22_2466541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2466541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466541 prefixEnd_2466541 := by exact prefixLift 2466541
  have htrace : WordTrace (prefixWord ++ tailWord_2466541) baseStart_2466541 baseEnd_2466541 := by
    simpa [prefixWord, tailWord_2466541, baseEnd_2466541] using wordTrace_append hprefix tailTrace_2466541
  have hstable : (prefixWord ++ tailWord_2466541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466541).length < 2 ^ (prefixWord ++ tailWord_2466541).sum := by decide
  have hdescent : baseEnd_2466541 < baseStart_2466541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466556 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_2466556 : Nat := 118140960795 + 2466556 * 2 ^ 59
def prefixEnd_2466556 : Nat := 4983230072969 + 3 ^ 40 * 2466556 * 2
def baseEnd_2466556 : Nat := 844352526154237881337681

theorem tailTrace_2466556 : CollatzResearch.WordTrace tailWord_2466556 prefixEnd_2466556 844352526154237881337681 := by
  unfold tailWord_2466556
  simp only [CollatzResearch.WordTrace]
  refine ⟨44981344026048170536073761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59975125368064227381431681 44981344026048170536073761)
  ·
    refine ⟨33736008019536127902055321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44981344026048170536073761 33736008019536127902055321)
    ·
      refine ⟨25302006014652095926541491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33736008019536127902055321 25302006014652095926541491)
      ·
        refine ⟨37953009021978143889812237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25302006014652095926541491 37953009021978143889812237)
        ·
          refine ⟨14232378383241803958679589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37953009021978143889812237 14232378383241803958679589)
          ·
            refine ⟨2668570946857838242252423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14232378383241803958679589 2668570946857838242252423)
            ·
              refine ⟨4002856420286757363378635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668570946857838242252423 4002856420286757363378635)
              ·
                refine ⟨6004284630430136045067953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002856420286757363378635 6004284630430136045067953)
                ·
                  refine ⟨4503213472822602033800965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004284630430136045067953 4503213472822602033800965)
                  ·
                    refine ⟨844352526154237881337681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503213472822602033800965 844352526154237881337681)
                    ·
                      rfl

theorem cell22_2466556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_2466556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466556 prefixEnd_2466556 := by exact prefixLift 2466556
  have htrace : WordTrace (prefixWord ++ tailWord_2466556) baseStart_2466556 baseEnd_2466556 := by
    simpa [prefixWord, tailWord_2466556, baseEnd_2466556] using wordTrace_append hprefix tailTrace_2466556
  have hstable : (prefixWord ++ tailWord_2466556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466556).length < 2 ^ (prefixWord ++ tailWord_2466556).sum := by decide
  have hdescent : baseEnd_2466556 < baseStart_2466556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466586 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_2466586 : Nat := 118140960795 + 2466586 * 2 ^ 59
def prefixEnd_2466586 : Nat := 4983230072969 + 3 ^ 40 * 2466586 * 2
def baseEnd_2466586 : Nat := 844362795767327803087589

theorem tailTrace_2466586 : CollatzResearch.WordTrace tailWord_2466586 prefixEnd_2466586 844362795767327803087589 := by
  unfold tailWord_2466586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22490945560496914048934903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59975854827991770797159741 22490945560496914048934903)
  ·
    refine ⟨33736418340745371073402355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22490945560496914048934903 33736418340745371073402355)
    ·
      refine ⟨50604627511118056610103533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33736418340745371073402355 50604627511118056610103533)
      ·
        refine ⟨18976735316669271228788825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50604627511118056610103533 18976735316669271228788825)
        ·
          refine ⟨14232551487501953421591619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18976735316669271228788825 14232551487501953421591619)
          ·
            refine ⟨21348827231252930132387429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232551487501953421591619 21348827231252930132387429)
            ·
              refine ⟨4002905105859924399822643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21348827231252930132387429 4002905105859924399822643)
              ·
                refine ⟨6004357658789886599733965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002905105859924399822643 6004357658789886599733965)
                ·
                  refine ⟨2251634122046207474900237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6004357658789886599733965 2251634122046207474900237)
                  ·
                    refine ⟨844362795767327803087589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251634122046207474900237 844362795767327803087589)
                    ·
                      rfl

theorem cell22_2466586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_2466586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466586 prefixEnd_2466586 := by exact prefixLift 2466586
  have htrace : WordTrace (prefixWord ++ tailWord_2466586) baseStart_2466586 baseEnd_2466586 := by
    simpa [prefixWord, tailWord_2466586, baseEnd_2466586] using wordTrace_append hprefix tailTrace_2466586
  have hstable : (prefixWord ++ tailWord_2466586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466586).length < 2 ^ (prefixWord ++ tailWord_2466586).sum := by decide
  have hdescent : baseEnd_2466586 < baseStart_2466586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466605 : List Nat := [1, 5, 3, 2, 1, 2, 2, 6]
def baseStart_2466605 : Nat := 118140960795 + 2466605 * 2 ^ 59
def prefixEnd_2466605 : Nat := 4983230072969 + 3 ^ 40 * 2466605 * 2
def baseEnd_2466605 : Nat := 93818811095068676318059

theorem tailTrace_2466605 : CollatzResearch.WordTrace tailWord_2466605 prefixEnd_2466605 93818811095068676318059 := by
  unfold tailWord_2466605
  simp only [CollatzResearch.WordTrace]
  refine ⟨89964475228918822440681269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59976316819279214960454179 89964475228918822440681269)
  ·
    refine ⟨8434169552711139603813869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89964475228918822440681269 8434169552711139603813869)
    ·
      refine ⟨3162813582266677351430201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8434169552711139603813869 3162813582266677351430201)
      ·
        refine ⟨2372110186700008013572651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3162813582266677351430201 2372110186700008013572651)
        ·
          refine ⟨3558165280050012020358977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372110186700008013572651 3558165280050012020358977)
          ·
            refine ⟨2668623960037509015269233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3558165280050012020358977 2668623960037509015269233)
            ·
              refine ⟨2001467970028131761451925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668623960037509015269233 2001467970028131761451925)
              ·
                refine ⟨93818811095068676318059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2001467970028131761451925 93818811095068676318059)
                ·
                  rfl

theorem cell22_2466605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 6].length) (baseStart_2466605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466605 prefixEnd_2466605 := by exact prefixLift 2466605
  have htrace : WordTrace (prefixWord ++ tailWord_2466605) baseStart_2466605 baseEnd_2466605 := by
    simpa [prefixWord, tailWord_2466605, baseEnd_2466605] using wordTrace_append hprefix tailTrace_2466605
  have hstable : (prefixWord ++ tailWord_2466605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466605).length < 2 ^ (prefixWord ++ tailWord_2466605).sum := by decide
  have hdescent : baseEnd_2466605 < baseStart_2466605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466637 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2466637 : Nat := 118140960795 + 2466637 * 2 ^ 59
def prefixEnd_2466637 : Nat := 4983230072969 + 3 ^ 40 * 2466637 * 2
def baseEnd_2466637 : Nat := 844380254109580670062433

theorem tailTrace_2466637 : CollatzResearch.WordTrace tailWord_2466637 prefixEnd_2466637 844380254109580670062433 := by
  unfold tailWord_2466637
  simp only [CollatzResearch.WordTrace]
  refine ⟨89965642364802891905846165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59977094909868594603897443 89965642364802891905846165)
  ·
    refine ⟨4217139485850135558086539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89965642364802891905846165 4217139485850135558086539)
    ·
      refine ⟨6325709228775203337129809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4217139485850135558086539 6325709228775203337129809)
      ·
        refine ⟨4744281921581402502847357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6325709228775203337129809 4744281921581402502847357)
        ·
          refine ⟨1779105720593025938567759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4744281921581402502847357 1779105720593025938567759)
          ·
            refine ⟨2668658580889538907851639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779105720593025938567759 2668658580889538907851639)
            ·
              refine ⟨4002987871334308361777459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668658580889538907851639 4002987871334308361777459)
              ·
                refine ⟨6004481807001462542666189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002987871334308361777459 6004481807001462542666189)
                ·
                  refine ⟨2251680677625548453499821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6004481807001462542666189 2251680677625548453499821)
                  ·
                    refine ⟨844380254109580670062433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251680677625548453499821 844380254109580670062433)
                    ·
                      rfl

theorem cell22_2466637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2466637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466637 prefixEnd_2466637 := by exact prefixLift 2466637
  have htrace : WordTrace (prefixWord ++ tailWord_2466637) baseStart_2466637 baseEnd_2466637 := by
    simpa [prefixWord, tailWord_2466637, baseEnd_2466637] using wordTrace_append hprefix tailTrace_2466637
  have hstable : (prefixWord ++ tailWord_2466637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466637).length < 2 ^ (prefixWord ++ tailWord_2466637).sum := by decide
  have hdescent : baseEnd_2466637 < baseStart_2466637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466663 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2466663 : Nat := 118140960795 + 2466663 * 2 ^ 59
def prefixEnd_2466663 : Nat := 4983230072969 + 3 ^ 40 * 2466663 * 2
def baseEnd_2466663 : Nat := 844389154440925268912353

theorem tailTrace_2466663 : CollatzResearch.WordTrace tailWord_2466663 prefixEnd_2466663 844389154440925268912353 := by
  unfold tailWord_2466663
  simp only [CollatzResearch.WordTrace]
  refine ⟨89966590662708698346292643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59977727108472465564195095 89966590662708698346292643)
  ·
    refine ⟨134949885994063047519438965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89966590662708698346292643 134949885994063047519438965)
    ·
      refine ⟨12651551811943410704947403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134949885994063047519438965 12651551811943410704947403)
      ·
        refine ⟨18977327717915116057421105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12651551811943410704947403 18977327717915116057421105)
        ·
          refine ⟨14232995788436337043065829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18977327717915116057421105 14232995788436337043065829)
          ·
            refine ⟨2668686710331813195574843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14232995788436337043065829 2668686710331813195574843)
            ·
              refine ⟨4003030065497719793362265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668686710331813195574843 4003030065497719793362265)
              ·
                refine ⟨3002272549123289845021699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003030065497719793362265 3002272549123289845021699)
                ·
                  refine ⟨4503408823684934767532549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002272549123289845021699 4503408823684934767532549)
                  ·
                    refine ⟨844389154440925268912353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503408823684934767532549 844389154440925268912353)
                    ·
                      rfl

theorem cell22_2466663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2466663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466663 prefixEnd_2466663 := by exact prefixLift 2466663
  have htrace : WordTrace (prefixWord ++ tailWord_2466663) baseStart_2466663 baseEnd_2466663 := by
    simpa [prefixWord, tailWord_2466663, baseEnd_2466663] using wordTrace_append hprefix tailTrace_2466663
  have hstable : (prefixWord ++ tailWord_2466663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466663).length < 2 ^ (prefixWord ++ tailWord_2466663).sum := by decide
  have hdescent : baseEnd_2466663 < baseStart_2466663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466674 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2466674 : Nat := 118140960795 + 2466674 * 2 ^ 59
def prefixEnd_2466674 : Nat := 4983230072969 + 3 ^ 40 * 2466674 * 2
def baseEnd_2466674 : Nat := 844392919965724906887319

theorem tailTrace_2466674 : CollatzResearch.WordTrace tailWord_2466674 prefixEnd_2466674 844392919965724906887319 := by
  unfold tailWord_2466674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491747966417211806235769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59977994577112564816628717 22491747966417211806235769)
  ·
    refine ⟨16868810974812908854676827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22491747966417211806235769 16868810974812908854676827)
    ·
      refine ⟨25303216462219363282015241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16868810974812908854676827 25303216462219363282015241)
      ·
        refine ⟨18977412346664522461511431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25303216462219363282015241 18977412346664522461511431)
        ·
          refine ⟨28466118519996783692267147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18977412346664522461511431 28466118519996783692267147)
          ·
            refine ⟨42699177779995175538400721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28466118519996783692267147 42699177779995175538400721)
            ·
              refine ⟨32024383334996381653800541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42699177779995175538400721 32024383334996381653800541)
              ·
                refine ⟨12009143750623643120175203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32024383334996381653800541 12009143750623643120175203)
                ·
                  refine ⟨18013715625935464680262805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12009143750623643120175203 18013715625935464680262805)
                  ·
                    refine ⟨844392919965724906887319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18013715625935464680262805 844392919965724906887319)
                    ·
                      rfl

theorem cell22_2466674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2466674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466674 prefixEnd_2466674 := by exact prefixLift 2466674
  have htrace : WordTrace (prefixWord ++ tailWord_2466674) baseStart_2466674 baseEnd_2466674 := by
    simpa [prefixWord, tailWord_2466674, baseEnd_2466674] using wordTrace_append hprefix tailTrace_2466674
  have hstable : (prefixWord ++ tailWord_2466674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466674).length < 2 ^ (prefixWord ++ tailWord_2466674).sum := by decide
  have hdescent : baseEnd_2466674 < baseStart_2466674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466693 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_2466693 : Nat := 118140960795 + 2466693 * 2 ^ 59
def prefixEnd_2466693 : Nat := 4983230072969 + 3 ^ 40 * 2466693 * 2
def baseEnd_2466693 : Nat := 844399424054015190662261

theorem tailTrace_2466693 : CollatzResearch.WordTrace tailWord_2466693 prefixEnd_2466693 844399424054015190662261 := by
  unfold tailWord_2466693
  simp only [CollatzResearch.WordTrace]
  refine ⟨89967684852600013469884733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59978456568400008979923155 89967684852600013469884733)
  ·
    refine ⟨33737881819725005051206775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89967684852600013469884733 33737881819725005051206775)
    ·
      refine ⟨50606822729587507576810163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33737881819725005051206775 50606822729587507576810163)
      ·
        refine ⟨75910234094381261365215245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50606822729587507576810163 75910234094381261365215245)
        ·
          refine ⟨28466337785392973011955717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75910234094381261365215245 28466337785392973011955717)
          ·
            refine ⟨5337438334761182439741697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28466337785392973011955717 5337438334761182439741697)
            ·
              refine ⟨4003078751070886829806273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5337438334761182439741697 4003078751070886829806273)
              ·
                refine ⟨3002309063303165122354705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003078751070886829806273 3002309063303165122354705)
                ·
                  refine ⟨2251731797477373841766029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002309063303165122354705 2251731797477373841766029)
                  ·
                    refine ⟨844399424054015190662261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251731797477373841766029 844399424054015190662261)
                    ·
                      rfl

theorem cell22_2466693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_2466693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466693 prefixEnd_2466693 := by exact prefixLift 2466693
  have htrace : WordTrace (prefixWord ++ tailWord_2466693) baseStart_2466693 baseEnd_2466693 := by
    simpa [prefixWord, tailWord_2466693, baseEnd_2466693] using wordTrace_append hprefix tailTrace_2466693
  have hstable : (prefixWord ++ tailWord_2466693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466693).length < 2 ^ (prefixWord ++ tailWord_2466693).sum := by decide
  have hdescent : baseEnd_2466693 < baseStart_2466693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466695 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 4]
def baseStart_2466695 : Nat := 118140960795 + 2466695 * 2 ^ 59
def prefixEnd_2466695 : Nat := 4983230072969 + 3 ^ 40 * 2466695 * 2
def baseEnd_2466695 : Nat := 281466702898295950704085

theorem tailTrace_2466695 : CollatzResearch.WordTrace tailWord_2466695 prefixEnd_2466695 281466702898295950704085 := by
  unfold tailWord_2466695
  simp only [CollatzResearch.WordTrace]
  refine ⟨89967757798592767811457539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59978505199061845207638359 89967757798592767811457539)
  ·
    refine ⟨134951636697889151717186309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89967757798592767811457539 134951636697889151717186309)
    ·
      refine ⟨25303431880854215946972433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134951636697889151717186309 25303431880854215946972433)
      ·
        refine ⟨18977573910640661960229325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25303431880854215946972433 18977573910640661960229325)
        ·
          refine ⟨7116590216490248235085997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18977573910640661960229325 7116590216490248235085997)
          ·
            refine ⟨2668721331183843088157249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7116590216490248235085997 2668721331183843088157249)
            ·
              refine ⟨2001540998387882316117937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668721331183843088157249 2001540998387882316117937)
              ·
                refine ⟨1501155748790911737088453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001540998387882316117937 1501155748790911737088453)
                ·
                  refine ⟨281466702898295950704085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501155748790911737088453 281466702898295950704085)
                  ·
                    rfl

theorem cell22_2466695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 4].length) (baseStart_2466695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466695 prefixEnd_2466695 := by exact prefixLift 2466695
  have htrace : WordTrace (prefixWord ++ tailWord_2466695) baseStart_2466695 baseEnd_2466695 := by
    simpa [prefixWord, tailWord_2466695, baseEnd_2466695] using wordTrace_append hprefix tailTrace_2466695
  have hstable : (prefixWord ++ tailWord_2466695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466695).length < 2 ^ (prefixWord ++ tailWord_2466695).sum := by decide
  have hdescent : baseEnd_2466695 < baseStart_2466695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466710 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2466710 : Nat := 118140960795 + 2466710 * 2 ^ 59
def prefixEnd_2466710 : Nat := 4983230072969 + 3 ^ 40 * 2466710 * 2
def baseEnd_2466710 : Nat := 844405243501432812987209

theorem tailTrace_2466710 : CollatzResearch.WordTrace tailWord_2466710 prefixEnd_2466710 844405243501432812987209 := by
  unfold tailWord_2466710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623019055846151585828349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59978869929025616915502389 5623019055846151585828349)
  ·
    refine ⟨2108632145942306844685631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5623019055846151585828349 2108632145942306844685631)
    ·
      refine ⟨3162948218913460267028447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108632145942306844685631 3162948218913460267028447)
      ·
        refine ⟨4744422328370190400542671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162948218913460267028447 4744422328370190400542671)
        ·
          refine ⟨7116633492555285600814007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744422328370190400542671 7116633492555285600814007)
          ·
            refine ⟨10674950238832928401221011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7116633492555285600814007 10674950238832928401221011)
            ·
              refine ⟨16012425358249392601831517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10674950238832928401221011 16012425358249392601831517)
              ·
                refine ⟨6004659509343522225686819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16012425358249392601831517 6004659509343522225686819)
                ·
                  refine ⟨9006989264015283338530229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6004659509343522225686819 9006989264015283338530229)
                  ·
                    refine ⟨844405243501432812987209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9006989264015283338530229 844405243501432812987209)
                    ·
                      rfl

theorem cell22_2466710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2466710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466710 prefixEnd_2466710 := by exact prefixLift 2466710
  have htrace : WordTrace (prefixWord ++ tailWord_2466710) baseStart_2466710 baseEnd_2466710 := by
    simpa [prefixWord, tailWord_2466710, baseEnd_2466710] using wordTrace_append hprefix tailTrace_2466710
  have hstable : (prefixWord ++ tailWord_2466710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466710).length < 2 ^ (prefixWord ++ tailWord_2466710).sum := by decide
  have hdescent : baseEnd_2466710 < baseStart_2466710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466766 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2466766 : Nat := 118140960795 + 2466766 * 2 ^ 59
def prefixEnd_2466766 : Nat := 4983230072969 + 3 ^ 40 * 2466766 * 2
def baseEnd_2466766 : Nat := 844424413445867333587037

theorem tailTrace_2466766 : CollatzResearch.WordTrace tailWord_2466766 prefixEnd_2466766 844424413445867333587037 := by
  unfold tailWord_2466766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11246293422666943367161519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59980231587557031291528101 11246293422666943367161519)
  ·
    refine ⟨16869440134000415050742279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11246293422666943367161519 16869440134000415050742279)
    ·
      refine ⟨25304160201000622576113419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16869440134000415050742279 25304160201000622576113419)
      ·
        refine ⟨37956240301500933864170129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25304160201000622576113419 37956240301500933864170129)
        ·
          refine ⟨28467180226125700398127597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37956240301500933864170129 28467180226125700398127597)
          ·
            refine ⟨10675192584797137649297849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28467180226125700398127597 10675192584797137649297849)
            ·
              refine ⟨8006394438597853236973387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10675192584797137649297849 8006394438597853236973387)
              ·
                refine ⟨12009591657896779855460081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8006394438597853236973387 12009591657896779855460081)
                ·
                  refine ⟨9007193743422584891595061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12009591657896779855460081 9007193743422584891595061)
                  ·
                    refine ⟨844424413445867333587037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9007193743422584891595061 844424413445867333587037)
                    ·
                      rfl

theorem cell22_2466766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2466766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466766 prefixEnd_2466766 := by exact prefixLift 2466766
  have htrace : WordTrace (prefixWord ++ tailWord_2466766) baseStart_2466766 baseEnd_2466766 := by
    simpa [prefixWord, tailWord_2466766, baseEnd_2466766] using wordTrace_append hprefix tailTrace_2466766
  have hstable : (prefixWord ++ tailWord_2466766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466766).length < 2 ^ (prefixWord ++ tailWord_2466766).sum := by decide
  have hdescent : baseEnd_2466766 < baseStart_2466766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466789 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_2466789 : Nat := 118140960795 + 2466789 * 2 ^ 59
def prefixEnd_2466789 : Nat := 4983230072969 + 3 ^ 40 * 2466789 * 2
def baseEnd_2466789 : Nat := 844432286815902940261967

theorem tailTrace_2466789 : CollatzResearch.WordTrace tailWord_2466789 prefixEnd_2466789 844432286815902940261967 := by
  unfold tailWord_2466789
  simp only [CollatzResearch.WordTrace]
  refine ⟨89971186260252221865379421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59980790840168147910252947 89971186260252221865379421)
  ·
    refine ⟨33739194847594583199517283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89971186260252221865379421 33739194847594583199517283)
    ·
      refine ⟨50608792271391874799275925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33739194847594583199517283 50608792271391874799275925)
      ·
        refine ⟨2372287137721494131216059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50608792271391874799275925 2372287137721494131216059)
        ·
          refine ⟨3558430706582241196824089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372287137721494131216059 3558430706582241196824089)
          ·
            refine ⟨2668823029936680897618067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3558430706582241196824089 2668823029936680897618067)
            ·
              refine ⟨4003234544905021346427101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668823029936680897618067 4003234544905021346427101)
              ·
                refine ⟨1501212954339383004910163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4003234544905021346427101 1501212954339383004910163)
                ·
                  refine ⟨2251819431509074507365245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501212954339383004910163 2251819431509074507365245)
                  ·
                    refine ⟨844432286815902940261967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251819431509074507365245 844432286815902940261967)
                    ·
                      rfl

theorem cell22_2466789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_2466789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466789 prefixEnd_2466789 := by exact prefixLift 2466789
  have htrace : WordTrace (prefixWord ++ tailWord_2466789) baseStart_2466789 baseEnd_2466789 := by
    simpa [prefixWord, tailWord_2466789, baseEnd_2466789] using wordTrace_append hprefix tailTrace_2466789
  have hstable : (prefixWord ++ tailWord_2466789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466789).length < 2 ^ (prefixWord ++ tailWord_2466789).sum := by decide
  have hdescent : baseEnd_2466789 < baseStart_2466789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466858 : List Nat := [3, 1, 4, 1, 4, 9]
def baseStart_2466858 : Nat := 118140960795 + 2466858 * 2 ^ 59
def prefixEnd_2466858 : Nat := 4983230072969 + 3 ^ 40 * 2466858 * 2
def baseEnd_2466858 : Nat := 10425381566987774818355

theorem tailTrace_2466858 : CollatzResearch.WordTrace tailWord_2466858 prefixEnd_2466858 10425381566987774818355 := by
  unfold tailWord_2466858
  simp only [CollatzResearch.WordTrace]
  refine ⟨22493425724250561662410307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59982468598001497766427485 22493425724250561662410307)
  ·
    refine ⟨33740138586375842493615461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22493425724250561662410307 33740138586375842493615461)
    ·
      refine ⟨6326275984945470467552899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33740138586375842493615461 6326275984945470467552899)
      ·
        refine ⟨9489413977418205701329349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6326275984945470467552899 9489413977418205701329349)
        ·
          refine ⟨1779265120765913568999253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9489413977418205701329349 1779265120765913568999253)
          ·
            refine ⟨10425381566987774818355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1779265120765913568999253 10425381566987774818355)
            ·
              rfl

theorem cell22_2466858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 9].length) (baseStart_2466858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466858 prefixEnd_2466858 := by exact prefixLift 2466858
  have htrace : WordTrace (prefixWord ++ tailWord_2466858) baseStart_2466858 baseEnd_2466858 := by
    simpa [prefixWord, tailWord_2466858, baseEnd_2466858] using wordTrace_append hprefix tailTrace_2466858
  have hstable : (prefixWord ++ tailWord_2466858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466858).length < 2 ^ (prefixWord ++ tailWord_2466858).sum := by decide
  have hdescent : baseEnd_2466858 < baseStart_2466858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466901 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2466901 : Nat := 118140960795 + 2466901 * 2 ^ 59
def prefixEnd_2466901 : Nat := 4983230072969 + 3 ^ 40 * 2466901 * 2
def baseEnd_2466901 : Nat := 844470626704771981461623

theorem tailTrace_2466901 : CollatzResearch.WordTrace tailWord_2466901 prefixEnd_2466901 844470626704771981461623 := by
  unfold tailWord_2466901
  simp only [CollatzResearch.WordTrace]
  refine ⟨89975271235846464993456557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59983514157230976662304371 89975271235846464993456557)
  ·
    refine ⟨33740726713442424372546209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89975271235846464993456557 33740726713442424372546209)
    ·
      refine ⟨25305545035081818279409657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33740726713442424372546209 25305545035081818279409657)
      ·
        refine ⟨18979158776311363709557243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25305545035081818279409657 18979158776311363709557243)
        ·
          refine ⟨28468738164467045564335865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18979158776311363709557243 28468738164467045564335865)
          ·
            refine ⟨21351553623350284173251899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28468738164467045564335865 21351553623350284173251899)
            ·
              refine ⟨32027330435025426259877849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21351553623350284173251899 32027330435025426259877849)
              ·
                refine ⟨24020497826269069694908387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32027330435025426259877849 24020497826269069694908387)
                ·
                  refine ⟨36030746739403604542362581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24020497826269069694908387 36030746739403604542362581)
                  ·
                    refine ⟨844470626704771981461623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36030746739403604542362581 844470626704771981461623)
                    ·
                      rfl

theorem cell22_2466901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2466901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466901 prefixEnd_2466901 := by exact prefixLift 2466901
  have htrace : WordTrace (prefixWord ++ tailWord_2466901) baseStart_2466901 baseEnd_2466901 := by
    simpa [prefixWord, tailWord_2466901, baseEnd_2466901] using wordTrace_append hprefix tailTrace_2466901
  have hstable : (prefixWord ++ tailWord_2466901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466901).length < 2 ^ (prefixWord ++ tailWord_2466901).sum := by decide
  have hdescent : baseEnd_2466901 < baseStart_2466901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466920 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 7]
def baseStart_2466920 : Nat := 118140960795 + 2466920 * 2 ^ 59
def prefixEnd_2466920 : Nat := 4983230072969 + 3 ^ 40 * 2466920 * 2
def baseEnd_2466920 : Nat := 281492376931020755078855

theorem tailTrace_2466920 : CollatzResearch.WordTrace tailWord_2466920 prefixEnd_2466920 281492376931020755078855 := by
  unfold tailWord_2466920
  simp only [CollatzResearch.WordTrace]
  refine ⟨44987982111388815619199107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59983976148518420825598809 44987982111388815619199107)
  ·
    refine ⟨67481973167083223428798661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44987982111388815619199107 67481973167083223428798661)
    ·
      refine ⟨12652869968828104392899749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67481973167083223428798661 12652869968828104392899749)
      ·
        refine ⟨2372413119155269573668703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12652869968828104392899749 2372413119155269573668703)
        ·
          refine ⟨3558619678732904360503055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372413119155269573668703 3558619678732904360503055)
          ·
            refine ⟨5337929518099356540754583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3558619678732904360503055 5337929518099356540754583)
            ·
              refine ⟨8006894277149034811131875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337929518099356540754583 8006894277149034811131875)
              ·
                refine ⟨12010341415723552216697813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8006894277149034811131875 12010341415723552216697813)
                ·
                  refine ⟨281492376931020755078855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12010341415723552216697813 281492376931020755078855)
                  ·
                    rfl

theorem cell22_2466920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_2466920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466920 prefixEnd_2466920 := by exact prefixLift 2466920
  have htrace : WordTrace (prefixWord ++ tailWord_2466920) baseStart_2466920 baseEnd_2466920 := by
    simpa [prefixWord, tailWord_2466920, baseEnd_2466920] using wordTrace_append hprefix tailTrace_2466920
  have hstable : (prefixWord ++ tailWord_2466920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466920).length < 2 ^ (prefixWord ++ tailWord_2466920).sum := by decide
  have hdescent : baseEnd_2466920 < baseStart_2466920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466948 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_2466948 : Nat := 118140960795 + 2466948 * 2 ^ 59
def prefixEnd_2466948 : Nat := 4983230072969 + 3 ^ 40 * 2466948 * 2
def baseEnd_2466948 : Nat := 281495571921759841845493

theorem tailTrace_2466948 : CollatzResearch.WordTrace tailWord_2466948 prefixEnd_2466948 281495571921759841845493 := by
  unfold tailWord_2466948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44988492733338096010208749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59984656977784128013611665 44988492733338096010208749)
  ·
    refine ⟨16870684775001786003828281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44988492733338096010208749 16870684775001786003828281)
    ·
      refine ⟨12653013581251339502871211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16870684775001786003828281 12653013581251339502871211)
      ·
        refine ⟨18979520371877009254306817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12653013581251339502871211 18979520371877009254306817)
        ·
          refine ⟨14234640278907756940730113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18979520371877009254306817 14234640278907756940730113)
          ·
            refine ⟨10675980209180817705547585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14234640278907756940730113 10675980209180817705547585)
            ·
              refine ⟨8006985156885613279160689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10675980209180817705547585 8006985156885613279160689)
              ·
                refine ⟨6005238867664209959370517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8006985156885613279160689 6005238867664209959370517)
                ·
                  refine ⟨281495571921759841845493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6005238867664209959370517 281495571921759841845493)
                  ·
                    rfl

theorem cell22_2466948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_2466948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466948 prefixEnd_2466948 := by exact prefixLift 2466948
  have htrace : WordTrace (prefixWord ++ tailWord_2466948) baseStart_2466948 baseEnd_2466948 := by
    simpa [prefixWord, tailWord_2466948, baseEnd_2466948] using wordTrace_append hprefix tailTrace_2466948
  have hstable : (prefixWord ++ tailWord_2466948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466948).length < 2 ^ (prefixWord ++ tailWord_2466948).sum := by decide
  have hdescent : baseEnd_2466948 < baseStart_2466948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466963 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 4, 3]
def baseStart_2466963 : Nat := 118140960795 + 2466963 * 2 ^ 59
def prefixEnd_2466963 : Nat := 4983230072969 + 3 ^ 40 * 2466963 * 2
def baseEnd_2466963 : Nat := 844491850571824486411433

theorem tailTrace_2466963 : CollatzResearch.WordTrace tailWord_2466963 prefixEnd_2466963 844491850571824486411433 := by
  unfold tailWord_2466963
  simp only [CollatzResearch.WordTrace]
  refine ⟨89977532561621849582213543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59985021707747899721475695 89977532561621849582213543)
  ·
    refine ⟨134966298842432774373320315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89977532561621849582213543 134966298842432774373320315)
    ·
      refine ⟨202449448263649161559980473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134966298842432774373320315 202449448263649161559980473)
      ·
        refine ⟨151837086197736871169985355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202449448263649161559980473 151837086197736871169985355)
        ·
          refine ⟨227755629296605306754978033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151837086197736871169985355 227755629296605306754978033)
          ·
            refine ⟨170816721972453980066233525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227755629296605306754978033 170816721972453980066233525)
            ·
              refine ⟨16014067684917560631209393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170816721972453980066233525 16014067684917560631209393)
              ·
                refine ⟨12010550763688170473407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16014067684917560631209393 12010550763688170473407045)
                ·
                  refine ⟨2251978268191531963763821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12010550763688170473407045 2251978268191531963763821)
                  ·
                    refine ⟨844491850571824486411433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251978268191531963763821 844491850571824486411433)
                    ·
                      rfl

theorem cell22_2466963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 3].length) (baseStart_2466963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466963 prefixEnd_2466963 := by exact prefixLift 2466963
  have htrace : WordTrace (prefixWord ++ tailWord_2466963) baseStart_2466963 baseEnd_2466963 := by
    simpa [prefixWord, tailWord_2466963, baseEnd_2466963] using wordTrace_append hprefix tailTrace_2466963
  have hstable : (prefixWord ++ tailWord_2466963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466963).length < 2 ^ (prefixWord ++ tailWord_2466963).sum := by decide
  have hdescent : baseEnd_2466963 < baseStart_2466963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466980 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_2466980 : Nat := 118140960795 + 2466980 * 2 ^ 59
def prefixEnd_2466980 : Nat := 4983230072969 + 3 ^ 40 * 2466980 * 2
def baseEnd_2466980 : Nat := 844497670019242108736381

theorem tailTrace_2466980 : CollatzResearch.WordTrace tailWord_2466980 prefixEnd_2466980 844497670019242108736381 := by
  unfold tailWord_2466980
  simp only [CollatzResearch.WordTrace]
  refine ⟨44989076301280130742791197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59985435068373507657054929 44989076301280130742791197)
  ·
    refine ⟨16870903612980049028546699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44989076301280130742791197 16870903612980049028546699)
    ·
      refine ⟨25306355419470073542820049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16870903612980049028546699 25306355419470073542820049)
      ·
        refine ⟨18979766564602555157115037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25306355419470073542820049 18979766564602555157115037)
        ·
          refine ⟨7117412461725958183918139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18979766564602555157115037 7117412461725958183918139)
          ·
            refine ⟨10676118692588937275877209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7117412461725958183918139 10676118692588937275877209)
            ·
              refine ⟨8007089019441702956907907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10676118692588937275877209 8007089019441702956907907)
              ·
                refine ⟨12010633529162554435361861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8007089019441702956907907 12010633529162554435361861)
                ·
                  refine ⟨2251993786717978956630349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12010633529162554435361861 2251993786717978956630349)
                  ·
                    refine ⟨844497670019242108736381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251993786717978956630349 844497670019242108736381)
                    ·
                      rfl

theorem cell22_2466980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_2466980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466980 prefixEnd_2466980 := by exact prefixLift 2466980
  have htrace : WordTrace (prefixWord ++ tailWord_2466980) baseStart_2466980 baseEnd_2466980 := by
    simpa [prefixWord, tailWord_2466980, baseEnd_2466980] using wordTrace_append hprefix tailTrace_2466980
  have hstable : (prefixWord ++ tailWord_2466980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466980).length < 2 ^ (prefixWord ++ tailWord_2466980).sum := by decide
  have hdescent : baseEnd_2466980 < baseStart_2466980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2466993 : List Nat := [1, 2, 2, 5, 1, 1, 1, 9]
def baseStart_2466993 : Nat := 118140960795 + 2466993 * 2 ^ 59
def prefixEnd_2466993 : Nat := 4983230072969 + 3 ^ 40 * 2466993 * 2
def baseEnd_2466993 : Nat := 93833568909434934240149

theorem tailTrace_2466993 : CollatzResearch.WordTrace tailWord_2466993 prefixEnd_2466993 93833568909434934240149 := by
  unfold tailWord_2466993
  simp only [CollatzResearch.WordTrace]
  refine ⟨89978626751513164705805633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59985751167675443137203755 89978626751513164705805633)
  ·
    refine ⟨67483970063634873529354225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89978626751513164705805633 67483970063634873529354225)
    ·
      refine ⟨50612977547726155147015669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67483970063634873529354225 50612977547726155147015669)
      ·
        refine ⟨4744966645099327045032719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50612977547726155147015669 4744966645099327045032719)
        ·
          refine ⟨7117449967648990567549079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744966645099327045032719 7117449967648990567549079)
          ·
            refine ⟨10676174951473485851323619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7117449967648990567549079 10676174951473485851323619)
            ·
              refine ⟨16014262427210228776985429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10676174951473485851323619 16014262427210228776985429)
              ·
                refine ⟨93833568909434934240149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16014262427210228776985429 93833568909434934240149)
                ·
                  rfl

theorem cell22_2466993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 9].length) (baseStart_2466993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2466993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2466993 prefixEnd_2466993 := by exact prefixLift 2466993
  have htrace : WordTrace (prefixWord ++ tailWord_2466993) baseStart_2466993 baseEnd_2466993 := by
    simpa [prefixWord, tailWord_2466993, baseEnd_2466993] using wordTrace_append hprefix tailTrace_2466993
  have hstable : (prefixWord ++ tailWord_2466993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2466993).length < 2 ^ (prefixWord ++ tailWord_2466993).sum := by decide
  have hdescent : baseEnd_2466993 < baseStart_2466993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2466993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467012 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2467012 : Nat := 118140960795 + 2467012 * 2 ^ 59
def prefixEnd_2467012 : Nat := 4983230072969 + 3 ^ 40 * 2467012 * 2
def baseEnd_2467012 : Nat := 844508624273204691936283

theorem tailTrace_2467012 : CollatzResearch.WordTrace tailWord_2467012 prefixEnd_2467012 844508624273204691936283 := by
  unfold tailWord_2467012
  simp only [CollatzResearch.WordTrace]
  refine ⟨44989659869222165475373645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59986213158962887300498193 44989659869222165475373645)
  ·
    refine ⟨16871122450958312053265117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44989659869222165475373645 16871122450958312053265117)
    ·
      refine ⟨6326670919109367019974419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16871122450958312053265117 6326670919109367019974419)
      ·
        refine ⟨9490006378664050529961629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6326670919109367019974419 9490006378664050529961629)
        ·
          refine ⟨3558752391999018948735611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9490006378664050529961629 3558752391999018948735611)
          ·
            refine ⟨5338128587998528423103417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3558752391999018948735611 5338128587998528423103417)
            ·
              refine ⟨4003596440998896317327563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5338128587998528423103417 4003596440998896317327563)
              ·
                refine ⟨6005394661498344475991345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003596440998896317327563 6005394661498344475991345)
                ·
                  refine ⟨4504045996123758356993509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005394661498344475991345 4504045996123758356993509)
                  ·
                    refine ⟨844508624273204691936283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4504045996123758356993509 844508624273204691936283)
                    ·
                      rfl

theorem cell22_2467012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2467012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467012 prefixEnd_2467012 := by exact prefixLift 2467012
  have htrace : WordTrace (prefixWord ++ tailWord_2467012) baseStart_2467012 baseEnd_2467012 := by
    simpa [prefixWord, tailWord_2467012, baseEnd_2467012] using wordTrace_append hprefix tailTrace_2467012
  have hstable : (prefixWord ++ tailWord_2467012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467012).length < 2 ^ (prefixWord ++ tailWord_2467012).sum := by decide
  have hdescent : baseEnd_2467012 < baseStart_2467012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467117 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2467117 : Nat := 118140960795 + 2467117 * 2 ^ 59
def prefixEnd_2467117 : Nat := 4983230072969 + 3 ^ 40 * 2467117 * 2
def baseEnd_2467117 : Nat := 281514855973006472686987

theorem tailTrace_2467117 : CollatzResearch.WordTrace tailWord_2467117 prefixEnd_2467117 281514855973006472686987 := by
  unfold tailWord_2467117
  simp only [CollatzResearch.WordTrace]
  refine ⟨89983149403063933883319605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59988766268709289255546403 89983149403063933883319605)
  ·
    refine ⟨8435920256537243801561213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89983149403063933883319605 8435920256537243801561213)
    ·
      refine ⟨3163470096201466425585455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8435920256537243801561213 3163470096201466425585455)
      ·
        refine ⟨4745205144302199638378183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163470096201466425585455 4745205144302199638378183)
        ·
          refine ⟨7117807716453299457567275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4745205144302199638378183 7117807716453299457567275)
          ·
            refine ⟨10676711574679949186350913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7117807716453299457567275 10676711574679949186350913)
            ·
              refine ⟨8007533681009961889763185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10676711574679949186350913 8007533681009961889763185)
              ·
                refine ⟨6005650260757471417322389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007533681009961889763185 6005650260757471417322389)
                ·
                  refine ⟨281514855973006472686987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6005650260757471417322389 281514855973006472686987)
                  ·
                    rfl

theorem cell22_2467117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2467117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467117 prefixEnd_2467117 := by exact prefixLift 2467117
  have htrace : WordTrace (prefixWord ++ tailWord_2467117) baseStart_2467117 baseEnd_2467117 := by
    simpa [prefixWord, tailWord_2467117, baseEnd_2467117] using wordTrace_append hprefix tailTrace_2467117
  have hstable : (prefixWord ++ tailWord_2467117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467117).length < 2 ^ (prefixWord ++ tailWord_2467117).sum := by decide
  have hdescent : baseEnd_2467117 < baseStart_2467117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467130 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_2467130 : Nat := 118140960795 + 2467130 * 2 ^ 59
def prefixEnd_2467130 : Nat := 4983230072969 + 3 ^ 40 * 2467130 * 2
def baseEnd_2467130 : Nat := 844549018084691717485921

theorem tailTrace_2467130 : CollatzResearch.WordTrace tailWord_2467130 prefixEnd_2467130 844549018084691717485921 := by
  unfold tailWord_2467130
  simp only [CollatzResearch.WordTrace]
  refine ⟨22495905888004209275885711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59989082368011224735695229 22495905888004209275885711)
  ·
    refine ⟨33743858832006313913828567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22495905888004209275885711 33743858832006313913828567)
    ·
      refine ⟨50615788248009470870742851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33743858832006313913828567 50615788248009470870742851)
      ·
        refine ⟨75923682372014206306114277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50615788248009470870742851 75923682372014206306114277)
        ·
          refine ⟨14235690444752663682396427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75923682372014206306114277 14235690444752663682396427)
          ·
            refine ⟨21353535667128995523594641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14235690444752663682396427 21353535667128995523594641)
            ·
              refine ⟨16015151750346746642695981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21353535667128995523594641 16015151750346746642695981)
              ·
                refine ⟨6005681906380029991010993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16015151750346746642695981 6005681906380029991010993)
                ·
                  refine ⟨4504261429785022493258245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005681906380029991010993 4504261429785022493258245)
                  ·
                    refine ⟨844549018084691717485921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4504261429785022493258245 844549018084691717485921)
                    ·
                      rfl

theorem cell22_2467130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_2467130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467130 prefixEnd_2467130 := by exact prefixLift 2467130
  have htrace : WordTrace (prefixWord ++ tailWord_2467130) baseStart_2467130 baseEnd_2467130 := by
    simpa [prefixWord, tailWord_2467130, baseEnd_2467130] using wordTrace_append hprefix tailTrace_2467130
  have hstable : (prefixWord ++ tailWord_2467130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467130).length < 2 ^ (prefixWord ++ tailWord_2467130).sum := by decide
  have hdescent : baseEnd_2467130 < baseStart_2467130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467207 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 5]
def baseStart_2467207 : Nat := 118140960795 + 2467207 * 2 ^ 59
def prefixEnd_2467207 : Nat := 4983230072969 + 3 ^ 40 * 2467207 * 2
def baseEnd_2467207 : Nat := 281525125586096394436895

theorem tailTrace_2467207 : CollatzResearch.WordTrace tailWord_2467207 prefixEnd_2467207 281525125586096394436895 := by
  unfold tailWord_2467207
  simp only [CollatzResearch.WordTrace]
  refine ⟨89986431972737879254095875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59990954648491919502730583 89986431972737879254095875)
  ·
    refine ⟨134979647959106818881143813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89986431972737879254095875 134979647959106818881143813)
    ·
      refine ⟨25308683992332528540214465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134979647959106818881143813 25308683992332528540214465)
      ·
        refine ⟨18981512994249396405160849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25308683992332528540214465 18981512994249396405160849)
        ·
          refine ⟨14236134745687047303870637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18981512994249396405160849 14236134745687047303870637)
          ·
            refine ⟨5338550529632642738951489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14236134745687047303870637 5338550529632642738951489)
            ·
              refine ⟨4003912897224482054213617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5338550529632642738951489 4003912897224482054213617)
              ·
                refine ⟨3002934672918361540660213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003912897224482054213617 3002934672918361540660213)
                ·
                  refine ⟨281525125586096394436895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3002934672918361540660213 281525125586096394436895)
                  ·
                    rfl

theorem cell22_2467207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 5].length) (baseStart_2467207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467207 prefixEnd_2467207 := by exact prefixLift 2467207
  have htrace : WordTrace (prefixWord ++ tailWord_2467207) baseStart_2467207 baseEnd_2467207 := by
    simpa [prefixWord, tailWord_2467207, baseEnd_2467207] using wordTrace_append hprefix tailTrace_2467207
  have hstable : (prefixWord ++ tailWord_2467207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467207).length < 2 ^ (prefixWord ++ tailWord_2467207).sum := by decide
  have hdescent : baseEnd_2467207 < baseStart_2467207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467235 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 6]
def baseStart_2467235 : Nat := 118140960795 + 2467235 * 2 ^ 59
def prefixEnd_2467235 : Nat := 4983230072969 + 3 ^ 40 * 2467235 * 2
def baseEnd_2467235 : Nat := 281528320576835481203533

theorem tailTrace_2467235 : CollatzResearch.WordTrace tailWord_2467235 prefixEnd_2467235 281528320576835481203533 := by
  unfold tailWord_2467235
  simp only [CollatzResearch.WordTrace]
  refine ⟨89987453216636440036115159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59991635477757626690743439 89987453216636440036115159)
  ·
    refine ⟨134981179824954660054172739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89987453216636440036115159 134981179824954660054172739)
    ·
      refine ⟨202471769737431990081259109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134981179824954660054172739 202471769737431990081259109)
      ·
        refine ⟨37963456825768498140236083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202471769737431990081259109 37963456825768498140236083)
        ·
          refine ⟨56945185238652747210354125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37963456825768498140236083 56945185238652747210354125)
          ·
            refine ⟨21354444464494780203882797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56945185238652747210354125 21354444464494780203882797)
            ·
              refine ⟨8007916674185542576456049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21354444464494780203882797 8007916674185542576456049)
              ·
                refine ⟨6005937505639156932342037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007916674185542576456049 6005937505639156932342037)
                ·
                  refine ⟨281528320576835481203533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6005937505639156932342037 281528320576835481203533)
                  ·
                    rfl

theorem cell22_2467235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_2467235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467235 prefixEnd_2467235 := by exact prefixLift 2467235
  have htrace : WordTrace (prefixWord ++ tailWord_2467235) baseStart_2467235 baseEnd_2467235 := by
    simpa [prefixWord, tailWord_2467235, baseEnd_2467235] using wordTrace_append hprefix tailTrace_2467235
  have hstable : (prefixWord ++ tailWord_2467235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467235).length < 2 ^ (prefixWord ++ tailWord_2467235).sum := by decide
  have hdescent : baseEnd_2467235 < baseStart_2467235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467250 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2467250 : Nat := 118140960795 + 2467250 * 2 ^ 59
def prefixEnd_2467250 : Nat := 4983230072969 + 3 ^ 40 * 2467250 * 2
def baseEnd_2467250 : Nat := 844590096537051404485553

theorem tailTrace_2467250 : CollatzResearch.WordTrace tailWord_2467250 prefixEnd_2467250 844590096537051404485553 := by
  unfold tailWord_2467250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497000077895524399477801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59992000207721398398607469 22497000077895524399477801)
  ·
    refine ⟨16872750058421643299608351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22497000077895524399477801 16872750058421643299608351)
    ·
      refine ⟨25309125087632464949412527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16872750058421643299608351 25309125087632464949412527)
      ·
        refine ⟨37963687631448697424118791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25309125087632464949412527 37963687631448697424118791)
        ·
          refine ⟨56945531447173046136178187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37963687631448697424118791 56945531447173046136178187)
          ·
            refine ⟨85418297170759569204267281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56945531447173046136178187 85418297170759569204267281)
            ·
              refine ⟨64063722878069676903200461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85418297170759569204267281 64063722878069676903200461)
              ·
                refine ⟨24023896079276128838700173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64063722878069676903200461 24023896079276128838700173)
                ·
                  refine ⟨9008961029728548314512565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24023896079276128838700173 9008961029728548314512565)
                  ·
                    refine ⟨844590096537051404485553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9008961029728548314512565 844590096537051404485553)
                    ·
                      rfl

theorem cell22_2467250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2467250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467250 prefixEnd_2467250 := by exact prefixLift 2467250
  have htrace : WordTrace (prefixWord ++ tailWord_2467250) baseStart_2467250 baseEnd_2467250 := by
    simpa [prefixWord, tailWord_2467250, baseEnd_2467250] using wordTrace_append hprefix tailTrace_2467250
  have hstable : (prefixWord ++ tailWord_2467250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467250).length < 2 ^ (prefixWord ++ tailWord_2467250).sum := by decide
  have hdescent : baseEnd_2467250 < baseStart_2467250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467295 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_2467295 : Nat := 118140960795 + 2467295 * 2 ^ 59
def prefixEnd_2467295 : Nat := 4983230072969 + 3 ^ 40 * 2467295 * 2
def baseEnd_2467295 : Nat := 844605500956686287110415

theorem tailTrace_2467295 : CollatzResearch.WordTrace tailWord_2467295 prefixEnd_2467295 844605500956686287110415 := by
  unfold tailWord_2467295
  simp only [CollatzResearch.WordTrace]
  refine ⟨89989641596419070283299339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59993094397612713522199559 89989641596419070283299339)
  ·
    refine ⟨134984462394628605424949009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89989641596419070283299339 134984462394628605424949009)
    ·
      refine ⟨101238346795971454068711757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134984462394628605424949009 101238346795971454068711757)
      ·
        refine ⟨37964380048489295275766909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101238346795971454068711757 37964380048489295275766909)
        ·
          refine ⟨14236642518183485728412591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37964380048489295275766909 14236642518183485728412591)
          ·
            refine ⟨21354963777275228592618887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14236642518183485728412591 21354963777275228592618887)
            ·
              refine ⟨32032445665912842888928331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21354963777275228592618887 32032445665912842888928331)
              ·
                refine ⟨48048668498869264333392497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32032445665912842888928331 48048668498869264333392497)
                ·
                  refine ⟨36036501374151948250044373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48048668498869264333392497 36036501374151948250044373)
                  ·
                    refine ⟨844605500956686287110415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36036501374151948250044373 844605500956686287110415)
                    ·
                      rfl

theorem cell22_2467295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_2467295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467295 prefixEnd_2467295 := by exact prefixLift 2467295
  have htrace : WordTrace (prefixWord ++ tailWord_2467295) baseStart_2467295 baseEnd_2467295 := by
    simpa [prefixWord, tailWord_2467295, baseEnd_2467295] using wordTrace_append hprefix tailTrace_2467295
  have hstable : (prefixWord ++ tailWord_2467295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467295).length < 2 ^ (prefixWord ++ tailWord_2467295).sum := by decide
  have hdescent : baseEnd_2467295 < baseStart_2467295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467297 : List Nat := [1, 2, 3, 1, 2, 3, 4, 6]
def baseStart_2467297 : Nat := 118140960795 + 2467297 * 2 ^ 59
def prefixEnd_2467297 : Nat := 4983230072969 + 3 ^ 40 * 2467297 * 2
def baseEnd_2467297 : Nat := 93845131733062105395601

theorem tailTrace_2467297 : CollatzResearch.WordTrace tailWord_2467297 prefixEnd_2467297 93845131733062105395601 := by
  unfold tailWord_2467297
  simp only [CollatzResearch.WordTrace]
  refine ⟨89989714542411824624872145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59993143028274549749914763 89989714542411824624872145)
  ·
    refine ⟨67492285906808868468654109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89989714542411824624872145 67492285906808868468654109)
    ·
      refine ⟨25309607215053325675745291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67492285906808868468654109 25309607215053325675745291)
      ·
        refine ⟨37964410822579988513617937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25309607215053325675745291 37964410822579988513617937)
        ·
          refine ⟨28473308116934991385213453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37964410822579988513617937 28473308116934991385213453)
          ·
            refine ⟨10677490543850621769455045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28473308116934991385213453 10677490543850621769455045)
            ·
              refine ⟨2002029476971991581772821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10677490543850621769455045 2002029476971991581772821)
              ·
                refine ⟨93845131733062105395601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2002029476971991581772821 93845131733062105395601)
                ·
                  rfl

theorem cell22_2467297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 6].length) (baseStart_2467297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467297 prefixEnd_2467297 := by exact prefixLift 2467297
  have htrace : WordTrace (prefixWord ++ tailWord_2467297) baseStart_2467297 baseEnd_2467297 := by
    simpa [prefixWord, tailWord_2467297, baseEnd_2467297] using wordTrace_append hprefix tailTrace_2467297
  have hstable : (prefixWord ++ tailWord_2467297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467297).length < 2 ^ (prefixWord ++ tailWord_2467297).sum := by decide
  have hdescent : baseEnd_2467297 < baseStart_2467297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467453 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_2467453 : Nat := 118140960795 + 2467453 * 2 ^ 59
def prefixEnd_2467453 : Nat := 4983230072969 + 3 ^ 40 * 2467453 * 2
def baseEnd_2467453 : Nat := 844659587585626541659931

theorem tailTrace_2467453 : CollatzResearch.WordTrace tailWord_2467453 prefixEnd_2467453 844659587585626541659931 := by
  unfold tailWord_2467453
  simp only [CollatzResearch.WordTrace]
  refine ⟨89995404329846663267551013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59996936219897775511700675 89995404329846663267551013)
  ·
    refine ⟨16874138311846249362665815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89995404329846663267551013 16874138311846249362665815)
    ·
      refine ⟨25311207467769374043998723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16874138311846249362665815 25311207467769374043998723)
      ·
        refine ⟨37966811201654061065998085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25311207467769374043998723 37966811201654061065998085)
        ·
          refine ⟨7118777100310136449874641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37966811201654061065998085 7118777100310136449874641)
          ·
            refine ⟨5339082825232602337405981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7118777100310136449874641 5339082825232602337405981)
            ·
              refine ⟨2002156059462225876527243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5339082825232602337405981 2002156059462225876527243)
              ·
                refine ⟨3003234089193338814790865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002156059462225876527243 3003234089193338814790865)
                ·
                  refine ⟨2252425566895004111093149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3003234089193338814790865 2252425566895004111093149)
                  ·
                    refine ⟨844659587585626541659931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252425566895004111093149 844659587585626541659931)
                    ·
                      rfl

theorem cell22_2467453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_2467453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467453 prefixEnd_2467453 := by exact prefixLift 2467453
  have htrace : WordTrace (prefixWord ++ tailWord_2467453) baseStart_2467453 baseEnd_2467453 := by
    simpa [prefixWord, tailWord_2467453, baseEnd_2467453] using wordTrace_append hprefix tailTrace_2467453
  have hstable : (prefixWord ++ tailWord_2467453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467453).length < 2 ^ (prefixWord ++ tailWord_2467453).sum := by decide
  have hdescent : baseEnd_2467453 < baseStart_2467453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467466 : List Nat := [3, 1, 2, 3, 2, 3, 2, 6]
def baseStart_2467466 : Nat := 118140960795 + 2467466 * 2 ^ 59
def prefixEnd_2467466 : Nat := 4983230072969 + 3 ^ 40 * 2467466 * 2
def baseEnd_2467466 : Nat := 93851559750144315676099

theorem tailTrace_2467466 : CollatzResearch.WordTrace tailWord_2467466 prefixEnd_2467466 93851559750144315676099 := by
  unfold tailWord_2467466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22498969619699891621943563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59997252319199710991849501 22498969619699891621943563)
  ·
    refine ⟨33748454429549837432915345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22498969619699891621943563 33748454429549837432915345)
    ·
      refine ⟨25311340822162378074686509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33748454429549837432915345 25311340822162378074686509)
      ·
        refine ⟨9491752808310891778007441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25311340822162378074686509 9491752808310891778007441)
        ·
          refine ⟨7118814606233168833505581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9491752808310891778007441 7118814606233168833505581)
          ·
            refine ⟨2669555477337438312564593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7118814606233168833505581 2669555477337438312564593)
            ·
              refine ⟨2002166608003078734423445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669555477337438312564593 2002166608003078734423445)
              ·
                refine ⟨93851559750144315676099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2002166608003078734423445 93851559750144315676099)
                ·
                  rfl

theorem cell22_2467466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_2467466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467466 prefixEnd_2467466 := by exact prefixLift 2467466
  have htrace : WordTrace (prefixWord ++ tailWord_2467466) baseStart_2467466 baseEnd_2467466 := by
    simpa [prefixWord, tailWord_2467466, baseEnd_2467466] using wordTrace_append hprefix tailTrace_2467466
  have hstable : (prefixWord ++ tailWord_2467466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467466).length < 2 ^ (prefixWord ++ tailWord_2467466).sum := by decide
  have hdescent : baseEnd_2467466 < baseStart_2467466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467481 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 1, 3]
def baseStart_2467481 : Nat := 118140960795 + 2467481 * 2 ^ 59
def prefixEnd_2467481 : Nat := 4983230072969 + 3 ^ 40 * 2467481 * 2
def baseEnd_2467481 : Nat := 844669172557843801959845

theorem tailTrace_2467481 : CollatzResearch.WordTrace tailWord_2467481 prefixEnd_2467481 844669172557843801959845 := by
  unfold tailWord_2467481
  simp only [CollatzResearch.WordTrace]
  refine ⟨89996425573745224049570297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59997617049163482699713531 89996425573745224049570297)
  ·
    refine ⟨67497319180308918037177723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89996425573745224049570297 67497319180308918037177723)
    ·
      refine ⟨101245978770463377055766585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67497319180308918037177723 101245978770463377055766585)
      ·
        refine ⟨75934484077847532791824939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101245978770463377055766585 75934484077847532791824939)
        ·
          refine ⟨113901726116771299187737409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75934484077847532791824939 113901726116771299187737409)
          ·
            refine ⟨85426294587578474390803057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113901726116771299187737409 85426294587578474390803057)
            ·
              refine ⟨64069720940683855793102293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85426294587578474390803057 64069720940683855793102293)
              ·
                refine ⟨1501634084547277870150835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64069720940683855793102293 1501634084547277870150835)
                ·
                  refine ⟨2252451126820916805226253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501634084547277870150835 2252451126820916805226253)
                  ·
                    refine ⟨844669172557843801959845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252451126820916805226253 844669172557843801959845)
                    ·
                      rfl

theorem cell22_2467481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_2467481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467481 prefixEnd_2467481 := by exact prefixLift 2467481
  have htrace : WordTrace (prefixWord ++ tailWord_2467481) baseStart_2467481 baseEnd_2467481 := by
    simpa [prefixWord, tailWord_2467481, baseEnd_2467481] using wordTrace_append hprefix tailTrace_2467481
  have hstable : (prefixWord ++ tailWord_2467481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467481).length < 2 ^ (prefixWord ++ tailWord_2467481).sum := by decide
  have hdescent : baseEnd_2467481 < baseStart_2467481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467511 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 5]
def baseStart_2467511 : Nat := 118140960795 + 2467511 * 2 ^ 59
def prefixEnd_2467511 : Nat := 4983230072969 + 3 ^ 40 * 2467511 * 2
def baseEnd_2467511 : Nat := 281559814056977907903251

theorem tailTrace_2467511 : CollatzResearch.WordTrace tailWord_2467511 prefixEnd_2467511 281559814056977907903251 := by
  unfold tailWord_2467511
  simp only [CollatzResearch.WordTrace]
  refine ⟨89997519763636539173162387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59998346509091026115441591 89997519763636539173162387)
  ·
    refine ⟨134996279645454808759743581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89997519763636539173162387 134996279645454808759743581)
    ·
      refine ⟨50623604867045553284903843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134996279645454808759743581 50623604867045553284903843)
      ·
        refine ⟨75935407300568329927355765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50623604867045553284903843 75935407300568329927355765)
        ·
          refine ⟨7118944434428280930689603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75935407300568329927355765 7118944434428280930689603)
          ·
            refine ⟨10678416651642421396034405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118944434428280930689603 10678416651642421396034405)
            ·
              refine ⟨2002203122182954011756451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10678416651642421396034405 2002203122182954011756451)
              ·
                refine ⟨3003304683274431017634677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002203122182954011756451 3003304683274431017634677)
                ·
                  refine ⟨281559814056977907903251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3003304683274431017634677 281559814056977907903251)
                  ·
                    rfl

theorem cell22_2467511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 5].length) (baseStart_2467511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467511 prefixEnd_2467511 := by exact prefixLift 2467511
  have htrace : WordTrace (prefixWord ++ tailWord_2467511) baseStart_2467511 baseEnd_2467511 := by
    simpa [prefixWord, tailWord_2467511, baseEnd_2467511] using wordTrace_append hprefix tailTrace_2467511
  have hstable : (prefixWord ++ tailWord_2467511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467511).length < 2 ^ (prefixWord ++ tailWord_2467511).sum := by decide
  have hdescent : baseEnd_2467511 < baseStart_2467511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467549 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2467549 : Nat := 118140960795 + 2467549 * 2 ^ 59
def prefixEnd_2467549 : Nat := 4983230072969 + 3 ^ 40 * 2467549 * 2
def baseEnd_2467549 : Nat := 844692450347514291259637

theorem tailTrace_2467549 : CollatzResearch.WordTrace tailWord_2467549 prefixEnd_2467549 844692450347514291259637 := by
  unfold tailWord_2467549
  simp only [CollatzResearch.WordTrace]
  refine ⟨89998905737498871663045701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59999270491665914442030467 89998905737498871663045701)
  ·
    refine ⟨16874794825781038436821069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89998905737498871663045701 16874794825781038436821069)
    ·
      refine ⟨6328048059667889413807901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16874794825781038436821069 6328048059667889413807901)
      ·
        refine ⟨2373018022375458530177963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6328048059667889413807901 2373018022375458530177963)
        ·
          refine ⟨3559527033563187795266945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373018022375458530177963 3559527033563187795266945)
          ·
            refine ⟨2669645275172390846450209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3559527033563187795266945 2669645275172390846450209)
            ·
              refine ⟨2002233956379293134837657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669645275172390846450209 2002233956379293134837657)
              ·
                refine ⟨1501675467284469851128243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002233956379293134837657 1501675467284469851128243)
                ·
                  refine ⟨2252513200926704776692365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501675467284469851128243 2252513200926704776692365)
                  ·
                    refine ⟨844692450347514291259637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252513200926704776692365 844692450347514291259637)
                    ·
                      rfl

theorem cell22_2467549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2467549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467549 prefixEnd_2467549 := by exact prefixLift 2467549
  have htrace : WordTrace (prefixWord ++ tailWord_2467549) baseStart_2467549 baseEnd_2467549 := by
    simpa [prefixWord, tailWord_2467549, baseEnd_2467549] using wordTrace_append hprefix tailTrace_2467549
  have hstable : (prefixWord ++ tailWord_2467549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467549).length < 2 ^ (prefixWord ++ tailWord_2467549).sum := by decide
  have hdescent : baseEnd_2467549 < baseStart_2467549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467556 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 4]
def baseStart_2467556 : Nat := 118140960795 + 2467556 * 2 ^ 59
def prefixEnd_2467556 : Nat := 4983230072969 + 3 ^ 40 * 2467556 * 2
def baseEnd_2467556 : Nat := 281564948863522868778205

theorem tailTrace_2467556 : CollatzResearch.WordTrace tailWord_2467556 prefixEnd_2467556 281564948863522868778205 := by
  unfold tailWord_2467556
  simp only [CollatzResearch.WordTrace]
  refine ⟨44999580524236755929275261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59999440698982341239033681 44999580524236755929275261)
  ·
    refine ⟨16874842696588783473478223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44999580524236755929275261 16874842696588783473478223)
    ·
      refine ⟨25312264044883175210217335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16874842696588783473478223 25312264044883175210217335)
      ·
        refine ⟨37968396067324762815326003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25312264044883175210217335 37968396067324762815326003)
        ·
          refine ⟨56952594100987144222989005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37968396067324762815326003 56952594100987144222989005)
          ·
            refine ⟨21357222787870179083620877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56952594100987144222989005 21357222787870179083620877)
            ·
              refine ⟨8008958545451317156357829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21357222787870179083620877 8008958545451317156357829)
              ·
                refine ⟨1501679727272121966817093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8008958545451317156357829 1501679727272121966817093)
                ·
                  refine ⟨281564948863522868778205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501679727272121966817093 281564948863522868778205)
                  ·
                    rfl

theorem cell22_2467556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_2467556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467556 prefixEnd_2467556 := by exact prefixLift 2467556
  have htrace : WordTrace (prefixWord ++ tailWord_2467556) baseStart_2467556 baseEnd_2467556 := by
    simpa [prefixWord, tailWord_2467556, baseEnd_2467556] using wordTrace_append hprefix tailTrace_2467556
  have hstable : (prefixWord ++ tailWord_2467556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467556).length < 2 ^ (prefixWord ++ tailWord_2467556).sum := by decide
  have hdescent : baseEnd_2467556 < baseStart_2467556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467571 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 2, 3]
def baseStart_2467571 : Nat := 118140960795 + 2467571 * 2 ^ 59
def prefixEnd_2467571 : Nat := 4983230072969 + 3 ^ 40 * 2467571 * 2
def baseEnd_2467571 : Nat := 844699981397113567209569

theorem tailTrace_2467571 : CollatzResearch.WordTrace tailWord_2467571 prefixEnd_2467571 844699981397113567209569 := by
  unfold tailWord_2467571
  simp only [CollatzResearch.WordTrace]
  refine ⟨89999708143419169420346567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59999805428946112946897711 89999708143419169420346567)
  ·
    refine ⟨134999562215128754130519851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89999708143419169420346567 134999562215128754130519851)
    ·
      refine ⟨202499343322693131195779777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134999562215128754130519851 202499343322693131195779777)
      ·
        refine ⟨151874507492019848396834833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202499343322693131195779777 151874507492019848396834833)
        ·
          refine ⟨113905880619014886297626125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151874507492019848396834833 113905880619014886297626125)
          ·
            refine ⟨42714705232130582361609797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113905880619014886297626125 42714705232130582361609797)
            ·
              refine ⟨8009007231024484192801837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42714705232130582361609797 8009007231024484192801837)
              ·
                refine ⟨3003377711634181572300689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8009007231024484192801837 3003377711634181572300689)
                ·
                  refine ⟨2252533283725636179225517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3003377711634181572300689 2252533283725636179225517)
                  ·
                    refine ⟨844699981397113567209569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252533283725636179225517 844699981397113567209569)
                    ·
                      rfl

theorem cell22_2467571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 3].length) (baseStart_2467571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467571 prefixEnd_2467571 := by exact prefixLift 2467571
  have htrace : WordTrace (prefixWord ++ tailWord_2467571) baseStart_2467571 baseEnd_2467571 := by
    simpa [prefixWord, tailWord_2467571, baseEnd_2467571] using wordTrace_append hprefix tailTrace_2467571
  have hstable : (prefixWord ++ tailWord_2467571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467571).length < 2 ^ (prefixWord ++ tailWord_2467571).sum := by decide
  have hdescent : baseEnd_2467571 < baseStart_2467571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467586 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2467586 : Nat := 118140960795 + 2467586 * 2 ^ 59
def prefixEnd_2467586 : Nat := 4983230072969 + 3 ^ 40 * 2467586 * 2
def baseEnd_2467586 : Nat := 844705116203658528084523

theorem tailTrace_2467586 : CollatzResearch.WordTrace tailWord_2467586 prefixEnd_2467586 844705116203658528084523 := by
  unfold tailWord_2467586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22500063809591206745535653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60000170158909884654761741 22500063809591206745535653)
  ·
    refine ⟨4218761964298351264787935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22500063809591206745535653 4218761964298351264787935)
    ·
      refine ⟨6328142946447526897181903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218761964298351264787935 6328142946447526897181903)
      ·
        refine ⟨9492214419671290345772855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6328142946447526897181903 9492214419671290345772855)
        ·
          refine ⟨14238321629506935518659283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9492214419671290345772855 14238321629506935518659283)
          ·
            refine ⟨21357482444260403277988925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14238321629506935518659283 21357482444260403277988925)
            ·
              refine ⟨8009055916597651229245847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21357482444260403277988925 8009055916597651229245847)
              ·
                refine ⟨12013583874896476843868771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8009055916597651229245847 12013583874896476843868771)
                ·
                  refine ⟨18020375812344715265803157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12013583874896476843868771 18020375812344715265803157)
                  ·
                    refine ⟨844705116203658528084523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18020375812344715265803157 844705116203658528084523)
                    ·
                      rfl

theorem cell22_2467586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2467586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467586 prefixEnd_2467586 := by exact prefixLift 2467586
  have htrace : WordTrace (prefixWord ++ tailWord_2467586) baseStart_2467586 baseEnd_2467586 := by
    simpa [prefixWord, tailWord_2467586, baseEnd_2467586] using wordTrace_append hprefix tailTrace_2467586
  have hstable : (prefixWord ++ tailWord_2467586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467586).length < 2 ^ (prefixWord ++ tailWord_2467586).sum := by decide
  have hdescent : baseEnd_2467586 < baseStart_2467586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467644 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2467644 : Nat := 118140960795 + 2467644 * 2 ^ 59
def prefixEnd_2467644 : Nat := 4983230072969 + 3 ^ 40 * 2467644 * 2
def baseEnd_2467644 : Nat := 844724970788965710134345

theorem tailTrace_2467644 : CollatzResearch.WordTrace tailWord_2467644 prefixEnd_2467644 844724970788965710134345 := by
  unfold tailWord_2467644
  simp only [CollatzResearch.WordTrace]
  refine ⟨45001185336077351443876993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60001580448103135258502657 45001185336077351443876993)
  ·
    refine ⟨33750889002058013582907745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45001185336077351443876993 33750889002058013582907745)
    ·
      refine ⟨25313166751543510187180809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33750889002058013582907745 25313166751543510187180809)
      ·
        refine ⟨18984875063657632640385607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25313166751543510187180809 18984875063657632640385607)
        ·
          refine ⟨28477312595486448960578411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18984875063657632640385607 28477312595486448960578411)
          ·
            refine ⟨42715968893229673440867617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28477312595486448960578411 42715968893229673440867617)
            ·
              refine ⟨32036976669922255080650713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42715968893229673440867617 32036976669922255080650713)
              ·
                refine ⟨24027732502441691310488035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32036976669922255080650713 24027732502441691310488035)
                ·
                  refine ⟨36041598753662536965732053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24027732502441691310488035 36041598753662536965732053)
                  ·
                    refine ⟨844724970788965710134345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36041598753662536965732053 844724970788965710134345)
                    ·
                      rfl

theorem cell22_2467644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2467644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467644 prefixEnd_2467644 := by exact prefixLift 2467644
  have htrace : WordTrace (prefixWord ++ tailWord_2467644) baseStart_2467644 baseEnd_2467644 := by
    simpa [prefixWord, tailWord_2467644, baseEnd_2467644] using wordTrace_append hprefix tailTrace_2467644
  have hstable : (prefixWord ++ tailWord_2467644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467644).length < 2 ^ (prefixWord ++ tailWord_2467644).sum := by decide
  have hdescent : baseEnd_2467644 < baseStart_2467644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467646 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2467646 : Nat := 118140960795 + 2467646 * 2 ^ 59
def prefixEnd_2467646 : Nat := 4983230072969 + 3 ^ 40 * 2467646 * 2
def baseEnd_2467646 : Nat := 281575218476612790528113

theorem tailTrace_2467646 : CollatzResearch.WordTrace tailWord_2467646 prefixEnd_2467646 281575218476612790528113 := by
  unfold tailWord_2467646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11250305452268432153665849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60001629078764971486217861 11250305452268432153665849)
  ·
    refine ⟨8437729089201324115249387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11250305452268432153665849 8437729089201324115249387)
    ·
      refine ⟨12656593633801986172874081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8437729089201324115249387 12656593633801986172874081)
      ·
        refine ⟨9492445225351489629655561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12656593633801986172874081 9492445225351489629655561)
        ·
          refine ⟨7119333919013617222241671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9492445225351489629655561 7119333919013617222241671)
          ·
            refine ⟨10679000878520425833362507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7119333919013617222241671 10679000878520425833362507)
            ·
              refine ⟨16018501317780638750043761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10679000878520425833362507 16018501317780638750043761)
              ·
                refine ⟨12013875988335479062532821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16018501317780638750043761 12013875988335479062532821)
                ·
                  refine ⟨281575218476612790528113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12013875988335479062532821 281575218476612790528113)
                  ·
                    rfl

theorem cell22_2467646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2467646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467646 prefixEnd_2467646 := by exact prefixLift 2467646
  have htrace : WordTrace (prefixWord ++ tailWord_2467646) baseStart_2467646 baseEnd_2467646 := by
    simpa [prefixWord, tailWord_2467646, baseEnd_2467646] using wordTrace_append hprefix tailTrace_2467646
  have hstable : (prefixWord ++ tailWord_2467646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467646).length < 2 ^ (prefixWord ++ tailWord_2467646).sum := by decide
  have hdescent : baseEnd_2467646 < baseStart_2467646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467689 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_2467689 : Nat := 118140960795 + 2467689 * 2 ^ 59
def prefixEnd_2467689 : Nat := 4983230072969 + 3 ^ 40 * 2467689 * 2
def baseEnd_2467689 : Nat := 844740375208600592759207

theorem tailTrace_2467689 : CollatzResearch.WordTrace tailWord_2467689 prefixEnd_2467689 844740375208600592759207 := by
  unfold tailWord_2467689
  simp only [CollatzResearch.WordTrace]
  refine ⟨90004011956991675573142121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60002674637994450382094747 90004011956991675573142121)
  ·
    refine ⟨67503008967743756679856591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90004011956991675573142121 67503008967743756679856591)
    ·
      refine ⟨101254513451615635019784887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67503008967743756679856591 101254513451615635019784887)
      ·
        refine ⟨151881770177423452529677331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101254513451615635019784887 151881770177423452529677331)
        ·
          refine ⟨227822655266135178794515997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151881770177423452529677331 227822655266135178794515997)
          ·
            refine ⟨85433495724800692047943499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227822655266135178794515997 85433495724800692047943499)
            ·
              refine ⟨128150243587201038071915249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85433495724800692047943499 128150243587201038071915249)
              ·
                refine ⟨96112682690400778553936437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128150243587201038071915249 96112682690400778553936437)
                ·
                  refine ⟨9010564002225072989431541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96112682690400778553936437 9010564002225072989431541)
                  ·
                    refine ⟨844740375208600592759207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9010564002225072989431541 844740375208600592759207)
                    ·
                      rfl

theorem cell22_2467689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_2467689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467689 prefixEnd_2467689 := by exact prefixLift 2467689
  have htrace : WordTrace (prefixWord ++ tailWord_2467689) baseStart_2467689 baseEnd_2467689 := by
    simpa [prefixWord, tailWord_2467689, baseEnd_2467689] using wordTrace_append hprefix tailTrace_2467689
  have hstable : (prefixWord ++ tailWord_2467689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467689).length < 2 ^ (prefixWord ++ tailWord_2467689).sum := by decide
  have hdescent : baseEnd_2467689 < baseStart_2467689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467693 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2467693 : Nat := 118140960795 + 2467693 * 2 ^ 59
def prefixEnd_2467693 : Nat := 4983230072969 + 3 ^ 40 * 2467693 * 2
def baseEnd_2467693 : Nat := 844741744490345915659195

theorem tailTrace_2467693 : CollatzResearch.WordTrace tailWord_2467693 prefixEnd_2467693 844741744490345915659195 := by
  unfold tailWord_2467693
  simp only [CollatzResearch.WordTrace]
  refine ⟨90004157848977184256287733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60002771899318122837525155 90004157848977184256287733)
  ·
    refine ⟨8437889798341611024026975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90004157848977184256287733 8437889798341611024026975)
    ·
      refine ⟨12656834697512416536040463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8437889798341611024026975 12656834697512416536040463)
      ·
        refine ⟨18985252046268624804060695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12656834697512416536040463 18985252046268624804060695)
        ·
          refine ⟨28477878069402937206091043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18985252046268624804060695 28477878069402937206091043)
          ·
            refine ⟨42716817104104405809136565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28477878069402937206091043 42716817104104405809136565)
            ·
              refine ⟨4004701603509788044606553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42716817104104405809136565 4004701603509788044606553)
              ·
                refine ⟨3003526202632341033454915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4004701603509788044606553 3003526202632341033454915)
                ·
                  refine ⟨4505289303948511550182373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003526202632341033454915 4505289303948511550182373)
                  ·
                    refine ⟨844741744490345915659195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4505289303948511550182373 844741744490345915659195)
                    ·
                      rfl

theorem cell22_2467693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2467693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467693 prefixEnd_2467693 := by exact prefixLift 2467693
  have htrace : WordTrace (prefixWord ++ tailWord_2467693) baseStart_2467693 baseEnd_2467693 := by
    simpa [prefixWord, tailWord_2467693, baseEnd_2467693] using wordTrace_append hprefix tailTrace_2467693
  have hstable : (prefixWord ++ tailWord_2467693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467693).length < 2 ^ (prefixWord ++ tailWord_2467693).sum := by decide
  have hdescent : baseEnd_2467693 < baseStart_2467693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467704 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_2467704 : Nat := 118140960795 + 2467704 * 2 ^ 59
def prefixEnd_2467704 : Nat := 4983230072969 + 3 ^ 40 * 2467704 * 2
def baseEnd_2467704 : Nat := 844745510015145553634161

theorem tailTrace_2467704 : CollatzResearch.WordTrace tailWord_2467704 prefixEnd_2467704 844745510015145553634161 := by
  unfold tailWord_2467704
  simp only [CollatzResearch.WordTrace]
  refine ⟨45002279525968666567469083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60003039367958222089958777 45002279525968666567469083)
  ·
    refine ⟨67503419288952999851203625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45002279525968666567469083 67503419288952999851203625)
    ·
      refine ⟨50627564466714749888402719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67503419288952999851203625 50627564466714749888402719)
      ·
        refine ⟨75941346700072124832604079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50627564466714749888402719 75941346700072124832604079)
        ·
          refine ⟨113912020050108187248906119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75941346700072124832604079 113912020050108187248906119)
          ·
            refine ⟨170868030075162280873359179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113912020050108187248906119 170868030075162280873359179)
            ·
              refine ⟨256302045112743421310038769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170868030075162280873359179 256302045112743421310038769)
              ·
                refine ⟨192226533834557565982529077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256302045112743421310038769 192226533834557565982529077)
                ·
                  refine ⟨18021237546989771810862101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192226533834557565982529077 18021237546989771810862101)
                  ·
                    refine ⟨844745510015145553634161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18021237546989771810862101 844745510015145553634161)
                    ·
                      rfl

theorem cell22_2467704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_2467704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467704 prefixEnd_2467704 := by exact prefixLift 2467704
  have htrace : WordTrace (prefixWord ++ tailWord_2467704) baseStart_2467704 baseEnd_2467704 := by
    simpa [prefixWord, tailWord_2467704, baseEnd_2467704] using wordTrace_append hprefix tailTrace_2467704
  have hstable : (prefixWord ++ tailWord_2467704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467704).length < 2 ^ (prefixWord ++ tailWord_2467704).sum := by decide
  have hdescent : baseEnd_2467704 < baseStart_2467704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467706 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_2467706 : Nat := 118140960795 + 2467706 * 2 ^ 59
def prefixEnd_2467706 : Nat := 4983230072969 + 3 ^ 40 * 2467706 * 2
def baseEnd_2467706 : Nat := 844746194656018215084155

theorem tailTrace_2467706 : CollatzResearch.WordTrace tailWord_2467706 prefixEnd_2467706 844746194656018215084155 := by
  unfold tailWord_2467706
  simp only [CollatzResearch.WordTrace]
  refine ⟨22501157999482521869127743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60003087998620058317673981 22501157999482521869127743)
  ·
    refine ⟨33751736999223782803691615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22501157999482521869127743 33751736999223782803691615)
    ·
      refine ⟨50627605498835674205537423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33751736999223782803691615 50627605498835674205537423)
      ·
        refine ⟨75941408248253511308306135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50627605498835674205537423 75941408248253511308306135)
        ·
          refine ⟨113912112372380266962459203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75941408248253511308306135 113912112372380266962459203)
          ·
            refine ⟨170868168558570400443688805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113912112372380266962459203 170868168558570400443688805)
            ·
              refine ⟨32037781604731950083191651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170868168558570400443688805 32037781604731950083191651)
              ·
                refine ⟨48056672407097925124787477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32037781604731950083191651 48056672407097925124787477)
                ·
                  refine ⟨2252656519082715240224413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48056672407097925124787477 2252656519082715240224413)
                  ·
                    refine ⟨844746194656018215084155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252656519082715240224413 844746194656018215084155)
                    ·
                      rfl

theorem cell22_2467706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_2467706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467706 prefixEnd_2467706 := by exact prefixLift 2467706
  have htrace : WordTrace (prefixWord ++ tailWord_2467706) baseStart_2467706 baseEnd_2467706 := by
    simpa [prefixWord, tailWord_2467706, baseEnd_2467706] using wordTrace_append hprefix tailTrace_2467706
  have hstable : (prefixWord ++ tailWord_2467706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467706).length < 2 ^ (prefixWord ++ tailWord_2467706).sum := by decide
  have hdescent : baseEnd_2467706 < baseStart_2467706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467719 : List Nat := [1, 1, 4, 2, 14]
def baseStart_2467719 : Nat := 118140960795 + 2467719 * 2 ^ 59
def prefixEnd_2467719 : Nat := 4983230072969 + 3 ^ 40 * 2467719 * 2
def baseEnd_2467719 : Nat := 3476340102146874545305

theorem tailTrace_2467719 : CollatzResearch.WordTrace tailWord_2467719 prefixEnd_2467719 3476340102146874545305 := by
  unfold tailWord_2467719
  simp only [CollatzResearch.WordTrace]
  refine ⟨90005106146882990696734211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60003404097921993797822807 90005106146882990696734211)
  ·
    refine ⟨135007659220324486045101317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90005106146882990696734211 135007659220324486045101317)
    ·
      refine ⟨25313936103810841133456497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135007659220324486045101317 25313936103810841133456497)
      ·
        refine ⟨18985452077858130850092373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25313936103810841133456497 18985452077858130850092373)
        ·
          refine ⟨3476340102146874545305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 18985452077858130850092373 3476340102146874545305)
          ·
            rfl

theorem cell22_2467719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 14].length) (baseStart_2467719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467719 prefixEnd_2467719 := by exact prefixLift 2467719
  have htrace : WordTrace (prefixWord ++ tailWord_2467719) baseStart_2467719 baseEnd_2467719 := by
    simpa [prefixWord, tailWord_2467719, baseEnd_2467719] using wordTrace_append hprefix tailTrace_2467719
  have hstable : (prefixWord ++ tailWord_2467719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467719).length < 2 ^ (prefixWord ++ tailWord_2467719).sum := by decide
  have hdescent : baseEnd_2467719 < baseStart_2467719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467721 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_2467721 : Nat := 118140960795 + 2467721 * 2 ^ 59
def prefixEnd_2467721 : Nat := 4983230072969 + 3 ^ 40 * 2467721 * 2
def baseEnd_2467721 : Nat := 844751329462563175959109

theorem tailTrace_2467721 : CollatzResearch.WordTrace tailWord_2467721 prefixEnd_2467721 844751329462563175959109 := by
  unfold tailWord_2467721
  simp only [CollatzResearch.WordTrace]
  refine ⟨90005179092875745038307017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60003452728583830025538011 90005179092875745038307017)
  ·
    refine ⟨67503884319656808778730263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90005179092875745038307017 67503884319656808778730263)
    ·
      refine ⟨101255826479485213168095395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67503884319656808778730263 101255826479485213168095395)
      ·
        refine ⟨151883739719227819752143093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101255826479485213168095395 151883739719227819752143093)
        ·
          refine ⟨14239100598677608101763415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151883739719227819752143093 14239100598677608101763415)
          ·
            refine ⟨21358650898016412152645123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14239100598677608101763415 21358650898016412152645123)
            ·
              refine ⟨32037976347024618228967685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21358650898016412152645123 32037976347024618228967685)
              ·
                refine ⟨6007120565067115917931441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32037976347024618228967685 6007120565067115917931441)
                ·
                  refine ⟨4505340423800336938448581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6007120565067115917931441 4505340423800336938448581)
                  ·
                    refine ⟨844751329462563175959109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4505340423800336938448581 844751329462563175959109)
                    ·
                      rfl

theorem cell22_2467721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_2467721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467721 prefixEnd_2467721 := by exact prefixLift 2467721
  have htrace : WordTrace (prefixWord ++ tailWord_2467721) baseStart_2467721 baseEnd_2467721 := by
    simpa [prefixWord, tailWord_2467721, baseEnd_2467721] using wordTrace_append hprefix tailTrace_2467721
  have hstable : (prefixWord ++ tailWord_2467721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467721).length < 2 ^ (prefixWord ++ tailWord_2467721).sum := by decide
  have hdescent : baseEnd_2467721 < baseStart_2467721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467740 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2467740 : Nat := 118140960795 + 2467740 * 2 ^ 59
def prefixEnd_2467740 : Nat := 4983230072969 + 3 ^ 40 * 2467740 * 2
def baseEnd_2467740 : Nat := 844757833550853459734051

theorem tailTrace_2467740 : CollatzResearch.WordTrace tailWord_2467740 prefixEnd_2467740 844757833550853459734051 := by
  unfold tailWord_2467740
  simp only [CollatzResearch.WordTrace]
  refine ⟨45002936039903455641624337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60003914719871274188832449 45002936039903455641624337)
  ·
    refine ⟨33752202029927591731218253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45002936039903455641624337 33752202029927591731218253)
    ·
      refine ⟨12657075761222846899206845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33752202029927591731218253 12657075761222846899206845)
      ·
        refine ⟨4746403410458567587202567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12657075761222846899206845 4746403410458567587202567)
        ·
          refine ⟨7119605115687851380803851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4746403410458567587202567 7119605115687851380803851)
          ·
            refine ⟨10679407673531777071205777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7119605115687851380803851 10679407673531777071205777)
            ·
              refine ⟨8009555755148832803404333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10679407673531777071205777 8009555755148832803404333)
              ·
                refine ⟨3003583408180812301276625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8009555755148832803404333 3003583408180812301276625)
                ·
                  refine ⟨2252687556135609225957469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3003583408180812301276625 2252687556135609225957469)
                  ·
                    refine ⟨844757833550853459734051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252687556135609225957469 844757833550853459734051)
                    ·
                      rfl

theorem cell22_2467740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2467740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467740 prefixEnd_2467740 := by exact prefixLift 2467740
  have htrace : WordTrace (prefixWord ++ tailWord_2467740) baseStart_2467740 baseEnd_2467740 := by
    simpa [prefixWord, tailWord_2467740, baseEnd_2467740] using wordTrace_append hprefix tailTrace_2467740
  have hstable : (prefixWord ++ tailWord_2467740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467740).length < 2 ^ (prefixWord ++ tailWord_2467740).sum := by decide
  have hdescent : baseEnd_2467740 < baseStart_2467740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467781 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 5]
def baseStart_2467781 : Nat := 118140960795 + 2467781 * 2 ^ 59
def prefixEnd_2467781 : Nat := 4983230072969 + 3 ^ 40 * 2467781 * 2
def baseEnd_2467781 : Nat := 281590622896247673152975

theorem tailTrace_2467781 : CollatzResearch.WordTrace tailWord_2467781 prefixEnd_2467781 281590622896247673152975 := by
  unfold tailWord_2467781
  simp only [CollatzResearch.WordTrace]
  refine ⟨90007367472658375285491197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60004911648438916856994131 90007367472658375285491197)
  ·
    refine ⟨33752762802246890732059199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90007367472658375285491197 33752762802246890732059199)
    ·
      refine ⟨50629144203370336098088799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33752762802246890732059199 50629144203370336098088799)
      ·
        refine ⟨75943716305055504147133199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50629144203370336098088799 75943716305055504147133199)
        ·
          refine ⟨113915574457583256220699799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75943716305055504147133199 113915574457583256220699799)
          ·
            refine ⟨170873361686374884331049699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113915574457583256220699799 170873361686374884331049699)
            ·
              refine ⟨256310042529562326496574549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170873361686374884331049699 256310042529562326496574549)
              ·
                refine ⟨3003633310893308513631733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 256310042529562326496574549 3003633310893308513631733)
                ·
                  refine ⟨281590622896247673152975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3003633310893308513631733 281590622896247673152975)
                  ·
                    rfl

theorem cell22_2467781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_2467781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467781 prefixEnd_2467781 := by exact prefixLift 2467781
  have htrace : WordTrace (prefixWord ++ tailWord_2467781) baseStart_2467781 baseEnd_2467781 := by
    simpa [prefixWord, tailWord_2467781, baseEnd_2467781] using wordTrace_append hprefix tailTrace_2467781
  have hstable : (prefixWord ++ tailWord_2467781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467781).length < 2 ^ (prefixWord ++ tailWord_2467781).sum := by decide
  have hdescent : baseEnd_2467781 < baseStart_2467781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467804 : List Nat := [2, 2, 6, 1, 1, 2, 2, 6]
def baseStart_2467804 : Nat := 118140960795 + 2467804 * 2 ^ 59
def prefixEnd_2467804 : Nat := 4983230072969 + 3 ^ 40 * 2467804 * 2
def baseEnd_2467804 : Nat := 93864415784308736237095

theorem tailTrace_2467804 : CollatzResearch.WordTrace tailWord_2467804 prefixEnd_2467804 93864415784308736237095 := by
  unfold tailWord_2467804
  simp only [CollatzResearch.WordTrace]
  refine ⟨45004103175787525106789233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60005470901050033475718977 45004103175787525106789233)
  ·
    refine ⟨33753077381840643830091925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45004103175787525106789233 33753077381840643830091925)
    ·
      refine ⟨1582175502273780179535559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33753077381840643830091925 1582175502273780179535559)
      ·
        refine ⟨2373263253410670269303339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582175502273780179535559 2373263253410670269303339)
        ·
          refine ⟨3559894880116005403955009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373263253410670269303339 3559894880116005403955009)
          ·
            refine ⟨2669921160087004052966257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3559894880116005403955009 2669921160087004052966257)
            ·
              refine ⟨2002440870065253039724693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669921160087004052966257 2002440870065253039724693)
              ·
                refine ⟨93864415784308736237095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2002440870065253039724693 93864415784308736237095)
                ·
                  rfl

theorem cell22_2467804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 6].length) (baseStart_2467804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467804 prefixEnd_2467804 := by exact prefixLift 2467804
  have htrace : WordTrace (prefixWord ++ tailWord_2467804) baseStart_2467804 baseEnd_2467804 := by
    simpa [prefixWord, tailWord_2467804, baseEnd_2467804] using wordTrace_append hprefix tailTrace_2467804
  have hstable : (prefixWord ++ tailWord_2467804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467804).length < 2 ^ (prefixWord ++ tailWord_2467804).sum := by decide
  have hdescent : baseEnd_2467804 < baseStart_2467804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467843 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 4]
def baseStart_2467843 : Nat := 118140960795 + 2467843 * 2 ^ 59
def prefixEnd_2467843 : Nat := 4983230072969 + 3 ^ 40 * 2467843 * 2
def baseEnd_2467843 : Nat := 281597697518598508136245

theorem tailTrace_2467843 : CollatzResearch.WordTrace tailWord_2467843 prefixEnd_2467843 281597697518598508136245 := by
  unfold tailWord_2467843
  simp only [CollatzResearch.WordTrace]
  refine ⟨90009628798433759874248183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60006419198955839916165455 90009628798433759874248183)
  ·
    refine ⟨135014443197650639811372275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90009628798433759874248183 135014443197650639811372275)
    ·
      refine ⟨202521664796475959717058413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135014443197650639811372275 202521664796475959717058413)
      ·
        refine ⟨75945624298678484893896905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202521664796475959717058413 75945624298678484893896905)
        ·
          refine ⟨56959218224008863670422679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75945624298678484893896905 56959218224008863670422679)
          ·
            refine ⟨85438827336013295505634019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56959218224008863670422679 85438827336013295505634019)
            ·
              refine ⟨128158241004019943258451029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85438827336013295505634019 128158241004019943258451029)
              ·
                refine ⟨1501854386765858710059973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 128158241004019943258451029 1501854386765858710059973)
                ·
                  refine ⟨281597697518598508136245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501854386765858710059973 281597697518598508136245)
                  ·
                    rfl

theorem cell22_2467843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 4].length) (baseStart_2467843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467843 prefixEnd_2467843 := by exact prefixLift 2467843
  have htrace : WordTrace (prefixWord ++ tailWord_2467843) baseStart_2467843 baseEnd_2467843 := by
    simpa [prefixWord, tailWord_2467843, baseEnd_2467843] using wordTrace_append hprefix tailTrace_2467843
  have hstable : (prefixWord ++ tailWord_2467843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467843).length < 2 ^ (prefixWord ++ tailWord_2467843).sum := by decide
  have hdescent : baseEnd_2467843 < baseStart_2467843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467871 : List Nat := [1, 1, 2, 4, 1, 2, 1, 10]
def baseStart_2467871 : Nat := 118140960795 + 2467871 * 2 ^ 59
def prefixEnd_2467871 : Nat := 4983230072969 + 3 ^ 40 * 2467871 * 2
def baseEnd_2467871 : Nat := 93866964169779198300961

theorem tailTrace_2467871 : CollatzResearch.WordTrace tailWord_2467871 prefixEnd_2467871 93866964169779198300961 := by
  unfold tailWord_2467871
  simp only [CollatzResearch.WordTrace]
  refine ⟨90010650042332320656267467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60007100028221547104178311 90010650042332320656267467)
  ·
    refine ⟨135015975063498480984401201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90010650042332320656267467 135015975063498480984401201)
    ·
      refine ⟨101261981297623860738300901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135015975063498480984401201 101261981297623860738300901)
      ·
        refine ⟨18986621493304473888431419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101261981297623860738300901 18986621493304473888431419)
        ·
          refine ⟨28479932239956710832647129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18986621493304473888431419 28479932239956710832647129)
          ·
            refine ⟨21359949179967533124485347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28479932239956710832647129 21359949179967533124485347)
            ·
              refine ⟨32039923769951299686728021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21359949179967533124485347 32039923769951299686728021)
              ·
                refine ⟨93866964169779198300961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32039923769951299686728021 93866964169779198300961)
                ·
                  rfl

theorem cell22_2467871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 10].length) (baseStart_2467871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467871 prefixEnd_2467871 := by exact prefixLift 2467871
  have htrace : WordTrace (prefixWord ++ tailWord_2467871) baseStart_2467871 baseEnd_2467871 := by
    simpa [prefixWord, tailWord_2467871, baseEnd_2467871] using wordTrace_append hprefix tailTrace_2467871
  have hstable : (prefixWord ++ tailWord_2467871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467871).length < 2 ^ (prefixWord ++ tailWord_2467871).sum := by decide
  have hdescent : baseEnd_2467871 < baseStart_2467871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467879 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2467879 : Nat := 118140960795 + 2467879 * 2 ^ 59
def prefixEnd_2467879 : Nat := 4983230072969 + 3 ^ 40 * 2467879 * 2
def baseEnd_2467879 : Nat := 844805416091503430508625

theorem tailTrace_2467879 : CollatzResearch.WordTrace tailWord_2467879 prefixEnd_2467879 844805416091503430508625 := by
  unfold tailWord_2467879
  simp only [CollatzResearch.WordTrace]
  refine ⟨90010941826303338022558691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60007294550868892015039127 90010941826303338022558691)
  ·
    refine ⟨135016412739455007033838037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90010941826303338022558691 135016412739455007033838037)
    ·
      refine ⟨3164447173580976727355579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 135016412739455007033838037 3164447173580976727355579)
      ·
        refine ⟨4746670760371465091033369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164447173580976727355579 4746670760371465091033369)
        ·
          refine ⟨3560003070278598818275027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4746670760371465091033369 3560003070278598818275027)
          ·
            refine ⟨5340004605417898227412541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560003070278598818275027 5340004605417898227412541)
            ·
              refine ⟨2002501727031711835279703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5340004605417898227412541 2002501727031711835279703)
              ·
                refine ⟨3003752590547567752919555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002501727031711835279703 3003752590547567752919555)
                ·
                  refine ⟨4505628885821351629379333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003752590547567752919555 4505628885821351629379333)
                  ·
                    refine ⟨844805416091503430508625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4505628885821351629379333 844805416091503430508625)
                    ·
                      rfl

theorem cell22_2467879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2467879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467879 prefixEnd_2467879 := by exact prefixLift 2467879
  have htrace : WordTrace (prefixWord ++ tailWord_2467879) baseStart_2467879 baseEnd_2467879 := by
    simpa [prefixWord, tailWord_2467879, baseEnd_2467879] using wordTrace_append hprefix tailTrace_2467879
  have hstable : (prefixWord ++ tailWord_2467879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467879).length < 2 ^ (prefixWord ++ tailWord_2467879).sum := by decide
  have hdescent : baseEnd_2467879 < baseStart_2467879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467905 : List Nat := [1, 2, 5, 1, 2, 3, 1, 7]
def baseStart_2467905 : Nat := 118140960795 + 2467905 * 2 ^ 59
def prefixEnd_2467905 : Nat := 4983230072969 + 3 ^ 40 * 2467905 * 2
def baseEnd_2467905 : Nat := 93868257380316447706505

theorem tailTrace_2467905 : CollatzResearch.WordTrace tailWord_2467905 prefixEnd_2467905 93868257380316447706505 := by
  unfold tailWord_2467905
  simp only [CollatzResearch.WordTrace]
  refine ⟨90011890124209144463005169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60007926749472762975336779 90011890124209144463005169)
  ·
    refine ⟨67508917593156858347253877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90011890124209144463005169 67508917593156858347253877)
    ·
      refine ⟨6328961024358455470055051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67508917593156858347253877 6328961024358455470055051)
      ·
        refine ⟨9493441536537683205082577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6328961024358455470055051 9493441536537683205082577)
        ·
          refine ⟨7120081152403262403811933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9493441536537683205082577 7120081152403262403811933)
          ·
            refine ⟨2670030432151223401429475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7120081152403262403811933 2670030432151223401429475)
            ·
              refine ⟨4005045648226835102144213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670030432151223401429475 4005045648226835102144213)
              ·
                refine ⟨93868257380316447706505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4005045648226835102144213 93868257380316447706505)
                ·
                  rfl

theorem cell22_2467905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 7].length) (baseStart_2467905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467905 prefixEnd_2467905 := by exact prefixLift 2467905
  have htrace : WordTrace (prefixWord ++ tailWord_2467905) baseStart_2467905 baseEnd_2467905 := by
    simpa [prefixWord, tailWord_2467905, baseEnd_2467905] using wordTrace_append hprefix tailTrace_2467905
  have hstable : (prefixWord ++ tailWord_2467905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467905).length < 2 ^ (prefixWord ++ tailWord_2467905).sum := by decide
  have hdescent : baseEnd_2467905 < baseStart_2467905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467948 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2467948 : Nat := 118140960795 + 2467948 * 2 ^ 59
def prefixEnd_2467948 : Nat := 4983230072969 + 3 ^ 40 * 2467948 * 2
def baseEnd_2467948 : Nat := 844829036201610250533413

theorem tailTrace_2467948 : CollatzResearch.WordTrace tailWord_2467948 prefixEnd_2467948 844829036201610250533413 := by
  unfold tailWord_2467948
  simp only [CollatzResearch.WordTrace]
  refine ⟨45006729231526681403410249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60008972308702241871213665 45006729231526681403410249)
  ·
    refine ⟨33755046923645011052557687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45006729231526681403410249 33755046923645011052557687)
    ·
      refine ⟨50632570385467516578836531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33755046923645011052557687 50632570385467516578836531)
      ·
        refine ⟨75948855578201274868254797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50632570385467516578836531 75948855578201274868254797)
        ·
          refine ⟨28480820841825478075595549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75948855578201274868254797 28480820841825478075595549)
          ·
            refine ⟨10680307815684554278348331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28480820841825478075595549 10680307815684554278348331)
            ·
              refine ⟨16020461723526831417522497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10680307815684554278348331 16020461723526831417522497)
              ·
                refine ⟨12015346292645123563141873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16020461723526831417522497 12015346292645123563141873)
                ·
                  refine ⟨9011509719483842672356405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12015346292645123563141873 9011509719483842672356405)
                  ·
                    refine ⟨844829036201610250533413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9011509719483842672356405 844829036201610250533413)
                    ·
                      rfl

theorem cell22_2467948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2467948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467948 prefixEnd_2467948 := by exact prefixLift 2467948
  have htrace : WordTrace (prefixWord ++ tailWord_2467948) baseStart_2467948 baseEnd_2467948 := by
    simpa [prefixWord, tailWord_2467948, baseEnd_2467948] using wordTrace_append hprefix tailTrace_2467948
  have hstable : (prefixWord ++ tailWord_2467948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467948).length < 2 ^ (prefixWord ++ tailWord_2467948).sum := by decide
  have hdescent : baseEnd_2467948 < baseStart_2467948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467988 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2467988 : Nat := 118140960795 + 2467988 * 2 ^ 59
def prefixEnd_2467988 : Nat := 4983230072969 + 3 ^ 40 * 2467988 * 2
def baseEnd_2467988 : Nat := 844842729019063479533291

theorem tailTrace_2467988 : CollatzResearch.WordTrace tailWord_2467988 prefixEnd_2467988 844842729019063479533291 := by
  unfold tailWord_2467988
  simp only [CollatzResearch.WordTrace]
  refine ⟨45007458691454224819138309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60009944921938966425517745 45007458691454224819138309)
  ·
    refine ⟨8438898504647667153588433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45007458691454224819138309 8438898504647667153588433)
    ·
      refine ⟨6329173878485750365191325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8438898504647667153588433 6329173878485750365191325)
      ·
        refine ⟨2373440204432156386946747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6329173878485750365191325 2373440204432156386946747)
        ·
          refine ⟨3560160306648234580420121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373440204432156386946747 3560160306648234580420121)
          ·
            refine ⟨2670120229986175935315091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3560160306648234580420121 2670120229986175935315091)
            ·
              refine ⟨4005180344979263902972637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670120229986175935315091 4005180344979263902972637)
              ·
                refine ⟨1501942629367223963614739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005180344979263902972637 1501942629367223963614739)
                ·
                  refine ⟨2252913944050835945422109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501942629367223963614739 2252913944050835945422109)
                  ·
                    refine ⟨844842729019063479533291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252913944050835945422109 844842729019063479533291)
                    ·
                      rfl

theorem cell22_2467988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2467988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467988 prefixEnd_2467988 := by exact prefixLift 2467988
  have htrace : WordTrace (prefixWord ++ tailWord_2467988) baseStart_2467988 baseEnd_2467988 := by
    simpa [prefixWord, tailWord_2467988, baseEnd_2467988] using wordTrace_append hprefix tailTrace_2467988
  have hstable : (prefixWord ++ tailWord_2467988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467988).length < 2 ^ (prefixWord ++ tailWord_2467988).sum := by decide
  have hdescent : baseEnd_2467988 < baseStart_2467988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2467993 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_2467993 : Nat := 118140960795 + 2467993 * 2 ^ 59
def prefixEnd_2467993 : Nat := 4983230072969 + 3 ^ 40 * 2467993 * 2
def baseEnd_2467993 : Nat := 844844440621245133158275

theorem tailTrace_2467993 : CollatzResearch.WordTrace tailWord_2467993 prefixEnd_2467993 844844440621245133158275 := by
  unfold tailWord_2467993
  simp only [CollatzResearch.WordTrace]
  refine ⟨90015099747890335492208633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60010066498593556994805755 90015099747890335492208633)
  ·
    refine ⟨67511324810917751619156475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90015099747890335492208633 67511324810917751619156475)
    ·
      refine ⟨101266987216376627428734713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67511324810917751619156475 101266987216376627428734713)
      ·
        refine ⟨75950240412282470571551035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101266987216376627428734713 75950240412282470571551035)
        ·
          refine ⟨113925360618423705857326553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75950240412282470571551035 113925360618423705857326553)
          ·
            refine ⟨85444020463817779392994915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113925360618423705857326553 85444020463817779392994915)
            ·
              refine ⟨128166030695726669089492373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85444020463817779392994915 128166030695726669089492373)
              ·
                refine ⟨6007782688862187613569955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128166030695726669089492373 6007782688862187613569955)
                ·
                  refine ⟨9011674033293281420354933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6007782688862187613569955 9011674033293281420354933)
                  ·
                    refine ⟨844844440621245133158275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9011674033293281420354933 844844440621245133158275)
                    ·
                      rfl

theorem cell22_2467993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_2467993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2467993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2467993 prefixEnd_2467993 := by exact prefixLift 2467993
  have htrace : WordTrace (prefixWord ++ tailWord_2467993) baseStart_2467993 baseEnd_2467993 := by
    simpa [prefixWord, tailWord_2467993, baseEnd_2467993] using wordTrace_append hprefix tailTrace_2467993
  have hstable : (prefixWord ++ tailWord_2467993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2467993).length < 2 ^ (prefixWord ++ tailWord_2467993).sum := by decide
  have hdescent : baseEnd_2467993 < baseStart_2467993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2467993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468023 : List Nat := [1, 1, 3, 1, 4, 2, 1, 9]
def baseStart_2468023 : Nat := 118140960795 + 2468023 * 2 ^ 59
def prefixEnd_2468023 : Nat := 4983230072969 + 3 ^ 40 * 2468023 * 2
def baseEnd_2468023 : Nat := 93872745581592783878687

theorem tailTrace_2468023 : CollatzResearch.WordTrace tailWord_2468023 prefixEnd_2468023 93872745581592783878687 := by
  unfold tailWord_2468023
  simp only [CollatzResearch.WordTrace]
  refine ⟨90016193937781650615800723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60010795958521100410533815 90016193937781650615800723)
  ·
    refine ⟨135024290906672475923701085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90016193937781650615800723 135024290906672475923701085)
    ·
      refine ⟨50634109090002178471387907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135024290906672475923701085 50634109090002178471387907)
      ·
        refine ⟨75951163635003267707081861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50634109090002178471387907 75951163635003267707081861)
        ·
          refine ⟨14240843181563112695077849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75951163635003267707081861 14240843181563112695077849)
          ·
            refine ⟨10680632386172334521308387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14240843181563112695077849 10680632386172334521308387)
            ·
              refine ⟨16020948579258501781962581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10680632386172334521308387 16020948579258501781962581)
              ·
                refine ⟨93872745581592783878687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16020948579258501781962581 93872745581592783878687)
                ·
                  rfl

theorem cell22_2468023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 9].length) (baseStart_2468023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468023 prefixEnd_2468023 := by exact prefixLift 2468023
  have htrace : WordTrace (prefixWord ++ tailWord_2468023) baseStart_2468023 baseEnd_2468023 := by
    simpa [prefixWord, tailWord_2468023, baseEnd_2468023] using wordTrace_append hprefix tailTrace_2468023
  have hstable : (prefixWord ++ tailWord_2468023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468023).length < 2 ^ (prefixWord ++ tailWord_2468023).sum := by decide
  have hdescent : baseEnd_2468023 < baseStart_2468023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468177 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2468177 : Nat := 118140960795 + 2468177 * 2 ^ 59
def prefixEnd_2468177 : Nat := 4983230072969 + 3 ^ 40 * 2468177 * 2
def baseEnd_2468177 : Nat := 844907427581529986557711

theorem tailTrace_2468177 : CollatzResearch.WordTrace tailWord_2468177 prefixEnd_2468177 844907427581529986557711 := by
  unfold tailWord_2468177
  simp only [CollatzResearch.WordTrace]
  refine ⟨90021810779223734916906785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60014540519482489944604523 90021810779223734916906785)
  ·
    refine ⟨67516358084417801187680089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90021810779223734916906785 67516358084417801187680089)
    ·
      refine ⟨50637268563313350890760067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67516358084417801187680089 50637268563313350890760067)
      ·
        refine ⟨75955902844970026336140101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50637268563313350890760067 75955902844970026336140101)
        ·
          refine ⟨14241731783431879938026269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75955902844970026336140101 14241731783431879938026269)
          ·
            refine ⟨5340649418786954976759851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14241731783431879938026269 5340649418786954976759851)
            ·
              refine ⟨8010974128180432465139777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5340649418786954976759851 8010974128180432465139777)
              ·
                refine ⟨6008230596135324348854833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8010974128180432465139777 6008230596135324348854833)
                ·
                  refine ⟨4506172947101493261641125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6008230596135324348854833 4506172947101493261641125)
                  ·
                    refine ⟨844907427581529986557711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4506172947101493261641125 844907427581529986557711)
                    ·
                      rfl

theorem cell22_2468177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2468177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468177 prefixEnd_2468177 := by exact prefixLift 2468177
  have htrace : WordTrace (prefixWord ++ tailWord_2468177) baseStart_2468177 baseEnd_2468177 := by
    simpa [prefixWord, tailWord_2468177, baseEnd_2468177] using wordTrace_append hprefix tailTrace_2468177
  have hstable : (prefixWord ++ tailWord_2468177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468177).length < 2 ^ (prefixWord ++ tailWord_2468177).sum := by decide
  have hdescent : baseEnd_2468177 < baseStart_2468177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468181 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 4]
def baseStart_2468181 : Nat := 118140960795 + 2468181 * 2 ^ 59
def prefixEnd_2468181 : Nat := 4983230072969 + 3 ^ 40 * 2468181 * 2
def baseEnd_2468181 : Nat := 281636265621091769819233

theorem tailTrace_2468181 : CollatzResearch.WordTrace tailWord_2468181 prefixEnd_2468181 281636265621091769819233 := by
  unfold tailWord_2468181
  simp only [CollatzResearch.WordTrace]
  refine ⟨90021956671209243600052397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60014637780806162400034931 90021956671209243600052397)
  ·
    refine ⟨33758233751703466350019649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90021956671209243600052397 33758233751703466350019649)
    ·
      refine ⟨25318675313777599762514737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33758233751703466350019649 25318675313777599762514737)
      ·
        refine ⟨18989006485333199821886053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25318675313777599762514737 18989006485333199821886053)
        ·
          refine ⟨3560438715999974966603635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18989006485333199821886053 3560438715999974966603635)
          ·
            refine ⟨5340658073999962449905453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560438715999974966603635 5340658073999962449905453)
            ·
              refine ⟨2002746777749985918714545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5340658073999962449905453 2002746777749985918714545)
              ·
                refine ⟨1502060083312489439035909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002746777749985918714545 1502060083312489439035909)
                ·
                  refine ⟨281636265621091769819233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502060083312489439035909 281636265621091769819233)
                  ·
                    rfl

theorem cell22_2468181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_2468181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468181 prefixEnd_2468181 := by exact prefixLift 2468181
  have htrace : WordTrace (prefixWord ++ tailWord_2468181) baseStart_2468181 baseEnd_2468181 := by
    simpa [prefixWord, tailWord_2468181, baseEnd_2468181] using wordTrace_append hprefix tailTrace_2468181
  have hstable : (prefixWord ++ tailWord_2468181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468181).length < 2 ^ (prefixWord ++ tailWord_2468181).sum := by decide
  have hdescent : baseEnd_2468181 < baseStart_2468181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468192 : List Nat := [2, 1, 1, 3, 5, 1, 2, 7]
def baseStart_2468192 : Nat := 118140960795 + 2468192 * 2 ^ 59
def prefixEnd_2468192 : Nat := 4983230072969 + 3 ^ 40 * 2468192 * 2
def baseEnd_2468192 : Nat := 93879173598674994159185

theorem tailTrace_2468192 : CollatzResearch.WordTrace tailWord_2468192 prefixEnd_2468192 93879173598674994159185 := by
  unfold tailWord_2468192
  simp only [CollatzResearch.WordTrace]
  refine ⟨45011178937084696239351415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60014905249446261652468553 45011178937084696239351415)
  ·
    refine ⟨67516768405627044359027123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45011178937084696239351415 67516768405627044359027123)
    ·
      refine ⟨101275152608440566538540685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67516768405627044359027123 101275152608440566538540685)
      ·
        refine ⟨37978182228165212451952757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101275152608440566538540685 37978182228165212451952757)
        ·
          refine ⟨3560454583890488667370571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37978182228165212451952757 3560454583890488667370571)
          ·
            refine ⟨5340681875835733001055857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560454583890488667370571 5340681875835733001055857)
            ·
              refine ⟨4005511406876799750791893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5340681875835733001055857 4005511406876799750791893)
              ·
                refine ⟨93879173598674994159185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4005511406876799750791893 93879173598674994159185)
                ·
                  rfl

theorem cell22_2468192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_2468192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468192 prefixEnd_2468192 := by exact prefixLift 2468192
  have htrace : WordTrace (prefixWord ++ tailWord_2468192) baseStart_2468192 baseEnd_2468192 := by
    simpa [prefixWord, tailWord_2468192, baseEnd_2468192] using wordTrace_append hprefix tailTrace_2468192
  have hstable : (prefixWord ++ tailWord_2468192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468192).length < 2 ^ (prefixWord ++ tailWord_2468192).sum := by decide
  have hdescent : baseEnd_2468192 < baseStart_2468192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468220 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_2468220 : Nat := 118140960795 + 2468220 * 2 ^ 59
def prefixEnd_2468220 : Nat := 4983230072969 + 3 ^ 40 * 2468220 * 2
def baseEnd_2468220 : Nat := 281640715786764069244193

theorem tailTrace_2468220 : CollatzResearch.WordTrace tailWord_2468220 prefixEnd_2468220 281640715786764069244193 := by
  unfold tailWord_2468220
  simp only [CollatzResearch.WordTrace]
  refine ⟨45011689559033976630361057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60015586078711968840481409 45011689559033976630361057)
  ·
    refine ⟨33758767169275482472770793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45011689559033976630361057 33758767169275482472770793)
    ·
      refine ⟨25319075376956611854578095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33758767169275482472770793 25319075376956611854578095)
      ·
        refine ⟨37978613065434917781867143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25319075376956611854578095 37978613065434917781867143)
        ·
          refine ⟨56967919598152376672800715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37978613065434917781867143 56967919598152376672800715)
          ·
            refine ⟨85451879397228565009201073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56967919598152376672800715 85451879397228565009201073)
            ·
              refine ⟨64088909547921423756900805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85451879397228565009201073 64088909547921423756900805)
              ·
                refine ⟨12016670540235266954418901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64088909547921423756900805 12016670540235266954418901)
                ·
                  refine ⟨281640715786764069244193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12016670540235266954418901 281640715786764069244193)
                  ·
                    rfl

theorem cell22_2468220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_2468220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468220 prefixEnd_2468220 := by exact prefixLift 2468220
  have htrace : WordTrace (prefixWord ++ tailWord_2468220) baseStart_2468220 baseEnd_2468220 := by
    simpa [prefixWord, tailWord_2468220, baseEnd_2468220] using wordTrace_append hprefix tailTrace_2468220
  have hstable : (prefixWord ++ tailWord_2468220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468220).length < 2 ^ (prefixWord ++ tailWord_2468220).sum := by decide
  have hdescent : baseEnd_2468220 < baseStart_2468220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468327 : List Nat := [1, 1, 5, 2, 1, 1, 3, 8]
def baseStart_2468327 : Nat := 118140960795 + 2468327 * 2 ^ 59
def prefixEnd_2468327 : Nat := 4983230072969 + 3 ^ 40 * 2468327 * 2
def baseEnd_2468327 : Nat := 93884308405219955034139

theorem tailTrace_2468327 : CollatzResearch.WordTrace tailWord_2468327 prefixEnd_2468327 93884308405219955034139 := by
  unfold tailWord_2468327
  simp only [CollatzResearch.WordTrace]
  refine ⟨90027281728680310534867235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60018187819120207023244823 90027281728680310534867235)
  ·
    refine ⟨135040922593020465802300853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90027281728680310534867235 135040922593020465802300853)
    ·
      refine ⟨12660086493095668668965705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135040922593020465802300853 12660086493095668668965705)
      ·
        refine ⟨9495064869821751501724279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12660086493095668668965705 9495064869821751501724279)
        ·
          refine ⟨14242597304732627252586419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9495064869821751501724279 14242597304732627252586419)
          ·
            refine ⟨21363895957098940878879629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14242597304732627252586419 21363895957098940878879629)
            ·
              refine ⟨8011460983912102829579861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21363895957098940878879629 8011460983912102829579861)
              ·
                refine ⟨93884308405219955034139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8011460983912102829579861 93884308405219955034139)
                ·
                  rfl

theorem cell22_2468327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 8].length) (baseStart_2468327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468327 prefixEnd_2468327 := by exact prefixLift 2468327
  have htrace : WordTrace (prefixWord ++ tailWord_2468327) baseStart_2468327 baseEnd_2468327 := by
    simpa [prefixWord, tailWord_2468327, baseEnd_2468327] using wordTrace_append hprefix tailTrace_2468327
  have hstable : (prefixWord ++ tailWord_2468327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468327).length < 2 ^ (prefixWord ++ tailWord_2468327).sum := by decide
  have hdescent : baseEnd_2468327 < baseStart_2468327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468333 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2468333 : Nat := 118140960795 + 2468333 * 2 ^ 59
def prefixEnd_2468333 : Nat := 4983230072969 + 3 ^ 40 * 2468333 * 2
def baseEnd_2468333 : Nat := 281653609856532526552411

theorem tailTrace_2468333 : CollatzResearch.WordTrace tailWord_2468333 prefixEnd_2468333 281653609856532526552411 := by
  unfold tailWord_2468333
  simp only [CollatzResearch.WordTrace]
  refine ⟨90027500566658573559585653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60018333711105715706390435 90027500566658573559585653)
  ·
    refine ⟨8440078178124241271211155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90027500566658573559585653 8440078178124241271211155)
    ·
      refine ⟨12660117267186361906816733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8440078178124241271211155 12660117267186361906816733)
      ·
        refine ⟨4747543975194885715056275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12660117267186361906816733 4747543975194885715056275)
        ·
          refine ⟨7121315962792328572584413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4747543975194885715056275 7121315962792328572584413)
          ·
            refine ⟨2670493486047123214719155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7121315962792328572584413 2670493486047123214719155)
            ·
              refine ⟨4005740229070684822078733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670493486047123214719155 4005740229070684822078733)
              ·
                refine ⟨1502152585901506808279525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005740229070684822078733 1502152585901506808279525)
                ·
                  refine ⟨281653609856532526552411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502152585901506808279525 281653609856532526552411)
                  ·
                    rfl

theorem cell22_2468333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2468333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468333 prefixEnd_2468333 := by exact prefixLift 2468333
  have htrace : WordTrace (prefixWord ++ tailWord_2468333) baseStart_2468333 baseEnd_2468333 := by
    simpa [prefixWord, tailWord_2468333, baseEnd_2468333] using wordTrace_append hprefix tailTrace_2468333
  have hstable : (prefixWord ++ tailWord_2468333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468333).length < 2 ^ (prefixWord ++ tailWord_2468333).sum := by decide
  have hdescent : baseEnd_2468333 < baseStart_2468333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468365 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2468365 : Nat := 118140960795 + 2468365 * 2 ^ 59
def prefixEnd_2468365 : Nat := 4983230072969 + 3 ^ 40 * 2468365 * 2
def baseEnd_2468365 : Nat := 844971783823560162857135

theorem tailTrace_2468365 : CollatzResearch.WordTrace tailWord_2468365 prefixEnd_2468365 844971783823560162857135 := by
  unfold tailWord_2468365
  simp only [CollatzResearch.WordTrace]
  refine ⟨90028667702542643024750549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60019111801695095349833699 90028667702542643024750549)
  ·
    refine ⟨2110046899278343195892591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90028667702542643024750549 2110046899278343195892591)
    ·
      refine ⟨3165070348917514793838887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110046899278343195892591 3165070348917514793838887)
      ·
        refine ⟨4747605523376272190758331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3165070348917514793838887 4747605523376272190758331)
        ·
          refine ⟨7121408285064408286137497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4747605523376272190758331 7121408285064408286137497)
          ·
            refine ⟨5341056213798306214603123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7121408285064408286137497 5341056213798306214603123)
            ·
              refine ⟨8011584320697459321904685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341056213798306214603123 8011584320697459321904685)
              ·
                refine ⟨3004344120261547245714257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8011584320697459321904685 3004344120261547245714257)
                ·
                  refine ⟨2253258090196160434285693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004344120261547245714257 2253258090196160434285693)
                  ·
                    refine ⟨844971783823560162857135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253258090196160434285693 844971783823560162857135)
                    ·
                      rfl

theorem cell22_2468365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2468365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468365 prefixEnd_2468365 := by exact prefixLift 2468365
  have htrace : WordTrace (prefixWord ++ tailWord_2468365) baseStart_2468365 baseEnd_2468365 := by
    simpa [prefixWord, tailWord_2468365, baseEnd_2468365] using wordTrace_append hprefix tailTrace_2468365
  have hstable : (prefixWord ++ tailWord_2468365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468365).length < 2 ^ (prefixWord ++ tailWord_2468365).sum := by decide
  have hdescent : baseEnd_2468365 < baseStart_2468365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468406 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_2468406 : Nat := 118140960795 + 2468406 * 2 ^ 59
def prefixEnd_2468406 : Nat := 4983230072969 + 3 ^ 40 * 2468406 * 2
def baseEnd_2468406 : Nat := 281661939653816574194003

theorem tailTrace_2468406 : CollatzResearch.WordTrace tailWord_2468406 prefixEnd_2468406 281661939653816574194003 := by
  unfold tailWord_2468406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626885193462131689187067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60020108730262738017995381 5626885193462131689187067)
  ·
    refine ⟨8440327790193197533780601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5626885193462131689187067 8440327790193197533780601)
    ·
      refine ⟨6330245842644898150335451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8440327790193197533780601 6330245842644898150335451)
      ·
        refine ⟨9495368763967347225503177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6330245842644898150335451 9495368763967347225503177)
        ·
          refine ⟨7121526572975510419127383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9495368763967347225503177 7121526572975510419127383)
          ·
            refine ⟨10682289859463265628691075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7121526572975510419127383 10682289859463265628691075)
            ·
              refine ⟨16023434789194898443036613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10682289859463265628691075 16023434789194898443036613)
              ·
                refine ⟨3004394022974043458069365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16023434789194898443036613 3004394022974043458069365)
                ·
                  refine ⟨281661939653816574194003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3004394022974043458069365 281661939653816574194003)
                  ·
                    rfl

theorem cell22_2468406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_2468406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468406 prefixEnd_2468406 := by exact prefixLift 2468406
  have htrace : WordTrace (prefixWord ++ tailWord_2468406) baseStart_2468406 baseEnd_2468406 := by
    simpa [prefixWord, tailWord_2468406, baseEnd_2468406] using wordTrace_append hprefix tailTrace_2468406
  have hstable : (prefixWord ++ tailWord_2468406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468406).length < 2 ^ (prefixWord ++ tailWord_2468406).sum := by decide
  have hdescent : baseEnd_2468406 < baseStart_2468406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468410 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_2468410 : Nat := 118140960795 + 2468410 * 2 ^ 59
def prefixEnd_2468410 : Nat := 4983230072969 + 3 ^ 40 * 2468410 * 2
def baseEnd_2468410 : Nat := 844987188243195045481997

theorem tailTrace_2468410 : CollatzResearch.WordTrace tailWord_2468410 prefixEnd_2468410 844987188243195045481997 := by
  unfold tailWord_2468410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507577246844903927534671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60020205991586410473425789 22507577246844903927534671)
  ·
    refine ⟨33761365870267355891302007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22507577246844903927534671 33761365870267355891302007)
    ·
      refine ⟨50642048805401033836953011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33761365870267355891302007 50642048805401033836953011)
      ·
        refine ⟨75963073208101550755429517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50642048805401033836953011 75963073208101550755429517)
        ·
          refine ⟨28486152453038081533286069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75963073208101550755429517 28486152453038081533286069)
          ·
            refine ⟨2670576792472320143745569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28486152453038081533286069 2670576792472320143745569)
            ·
              refine ⟨2002932594354240107809177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2670576792472320143745569 2002932594354240107809177)
              ·
                refine ⟨1502199445765680080856883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002932594354240107809177 1502199445765680080856883)
                ·
                  refine ⟨2253299168648520121285325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502199445765680080856883 2253299168648520121285325)
                  ·
                    refine ⟨844987188243195045481997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253299168648520121285325 844987188243195045481997)
                    ·
                      rfl

theorem cell22_2468410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_2468410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468410 prefixEnd_2468410 := by exact prefixLift 2468410
  have htrace : WordTrace (prefixWord ++ tailWord_2468410) baseStart_2468410 baseEnd_2468410 := by
    simpa [prefixWord, tailWord_2468410, baseEnd_2468410] using wordTrace_append hprefix tailTrace_2468410
  have hstable : (prefixWord ++ tailWord_2468410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468410).length < 2 ^ (prefixWord ++ tailWord_2468410).sum := by decide
  have hdescent : baseEnd_2468410 < baseStart_2468410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468434 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_2468434 : Nat := 118140960795 + 2468434 * 2 ^ 59
def prefixEnd_2468434 : Nat := 4983230072969 + 3 ^ 40 * 2468434 * 2
def baseEnd_2468434 : Nat := 281665134644555660960641

theorem tailTrace_2468434 : CollatzResearch.WordTrace tailWord_2468434 prefixEnd_2468434 281665134644555660960641 := by
  unfold tailWord_2468434
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507796084823166952253089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60020789559528445206008237 22507796084823166952253089)
  ·
    refine ⟨16880847063617375214189817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22507796084823166952253089 16880847063617375214189817)
    ·
      refine ⟨12660635297713031410642363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16880847063617375214189817 12660635297713031410642363)
      ·
        refine ⟨18990952946569547115963545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12660635297713031410642363 18990952946569547115963545)
        ·
          refine ⟨14243214709927160336972659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18990952946569547115963545 14243214709927160336972659)
          ·
            refine ⟨21364822064890740505458989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14243214709927160336972659 21364822064890740505458989)
            ·
              refine ⟨8011808274334027689547121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21364822064890740505458989 8011808274334027689547121)
              ·
                refine ⟨6008856205750520767160341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8011808274334027689547121 6008856205750520767160341)
                ·
                  refine ⟨281665134644555660960641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6008856205750520767160341 281665134644555660960641)
                  ·
                    rfl

theorem cell22_2468434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_2468434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468434 prefixEnd_2468434 := by exact prefixLift 2468434
  have htrace : WordTrace (prefixWord ++ tailWord_2468434) baseStart_2468434 baseEnd_2468434 := by
    simpa [prefixWord, tailWord_2468434, baseEnd_2468434] using wordTrace_append hprefix tailTrace_2468434
  have hstable : (prefixWord ++ tailWord_2468434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468434).length < 2 ^ (prefixWord ++ tailWord_2468434).sum := by decide
  have hdescent : baseEnd_2468434 < baseStart_2468434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468449 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2468449 : Nat := 118140960795 + 2468449 * 2 ^ 59
def prefixEnd_2468449 : Nat := 4983230072969 + 3 ^ 40 * 2468449 * 2
def baseEnd_2468449 : Nat := 845000538740211943756877

theorem tailTrace_2468449 : CollatzResearch.WordTrace tailWord_2468449 prefixEnd_2468449 845000538740211943756877 := by
  unfold tailWord_2468449
  simp only [CollatzResearch.WordTrace]
  refine ⟨90031731434238325370808401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60021154289492216913872267 90031731434238325370808401)
  ·
    refine ⟨67523798575678744028106301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90031731434238325370808401 67523798575678744028106301)
    ·
      refine ⟨25321424465879529010539863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67523798575678744028106301 25321424465879529010539863)
      ·
        refine ⟨37982136698819293515809795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25321424465879529010539863 37982136698819293515809795)
        ·
          refine ⟨56973205048228940273714693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37982136698819293515809795 56973205048228940273714693)
          ·
            refine ⟨10682475946542926301321505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56973205048228940273714693 10682475946542926301321505)
            ·
              refine ⟨8011856959907194725991129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10682475946542926301321505 8011856959907194725991129)
              ·
                refine ⟨6008892719930396044493347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8011856959907194725991129 6008892719930396044493347)
                ·
                  refine ⟨9013339079895594066740021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6008892719930396044493347 9013339079895594066740021)
                  ·
                    refine ⟨845000538740211943756877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9013339079895594066740021 845000538740211943756877)
                    ·
                      rfl

theorem cell22_2468449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2468449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468449 prefixEnd_2468449 := by exact prefixLift 2468449
  have htrace : WordTrace (prefixWord ++ tailWord_2468449) baseStart_2468449 baseEnd_2468449 := by
    simpa [prefixWord, tailWord_2468449, baseEnd_2468449] using wordTrace_append hprefix tailTrace_2468449
  have hstable : (prefixWord ++ tailWord_2468449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468449).length < 2 ^ (prefixWord ++ tailWord_2468449).sum := by decide
  have hdescent : baseEnd_2468449 < baseStart_2468449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468451 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 4]
def baseStart_2468451 : Nat := 118140960795 + 2468451 * 2 ^ 59
def prefixEnd_2468451 : Nat := 4983230072969 + 3 ^ 40 * 2468451 * 2
def baseEnd_2468451 : Nat := 281667074460361535068957

theorem tailTrace_2468451 : CollatzResearch.WordTrace tailWord_2468451 prefixEnd_2468451 281667074460361535068957 := by
  unfold tailWord_2468451
  simp only [CollatzResearch.WordTrace]
  refine ⟨90031804380231079712381207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60021202920154053141587471 90031804380231079712381207)
  ·
    refine ⟨135047706570346619568571811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90031804380231079712381207 135047706570346619568571811)
    ·
      refine ⟨202571559855519929352857717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135047706570346619568571811 202571559855519929352857717)
      ·
        refine ⟨18991083736454993376830411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202571559855519929352857717 18991083736454993376830411)
        ·
          refine ⟨28486625604682490065245617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18991083736454993376830411 28486625604682490065245617)
          ·
            refine ⟨21364969203511867548934213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28486625604682490065245617 21364969203511867548934213)
            ·
              refine ⟨4005931725658475165425165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21364969203511867548934213 4005931725658475165425165)
              ·
                refine ⟨1502224397121928187034437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005931725658475165425165 1502224397121928187034437)
                ·
                  refine ⟨281667074460361535068957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502224397121928187034437 281667074460361535068957)
                  ·
                    rfl

theorem cell22_2468451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 4].length) (baseStart_2468451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468451 prefixEnd_2468451 := by exact prefixLift 2468451
  have htrace : WordTrace (prefixWord ++ tailWord_2468451) baseStart_2468451 baseEnd_2468451 := by
    simpa [prefixWord, tailWord_2468451, baseEnd_2468451] using wordTrace_append hprefix tailTrace_2468451
  have hstable : (prefixWord ++ tailWord_2468451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468451).length < 2 ^ (prefixWord ++ tailWord_2468451).sum := by decide
  have hdescent : baseEnd_2468451 < baseStart_2468451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468494 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2468494 : Nat := 118140960795 + 2468494 * 2 ^ 59
def prefixEnd_2468494 : Nat := 4983230072969 + 3 ^ 40 * 2468494 * 2
def baseEnd_2468494 : Nat := 845015943159846826381739

theorem tailTrace_2468494 : CollatzResearch.WordTrace tailWord_2468494 prefixEnd_2468494 845015943159846826381739 := by
  unfold tailWord_2468494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11254171589884412257024567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60022248479383532037464357 11254171589884412257024567)
  ·
    refine ⟨16881257384826618385536851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11254171589884412257024567 16881257384826618385536851)
    ·
      refine ⟨25321886077239927578305277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16881257384826618385536851 25321886077239927578305277)
      ·
        refine ⟨9495707278964972841864479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25321886077239927578305277 9495707278964972841864479)
        ·
          refine ⟨14243560918447459262796719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9495707278964972841864479 14243560918447459262796719)
          ·
            refine ⟨21365341377671188894195079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14243560918447459262796719 21365341377671188894195079)
            ·
              refine ⟨32048012066506783341292619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21365341377671188894195079 32048012066506783341292619)
              ·
                refine ⟨48072018099760175011938929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32048012066506783341292619 48072018099760175011938929)
                ·
                  refine ⟨36054013574820131258954197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48072018099760175011938929 36054013574820131258954197)
                  ·
                    refine ⟨845015943159846826381739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36054013574820131258954197 845015943159846826381739)
                    ·
                      rfl

theorem cell22_2468494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2468494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468494 prefixEnd_2468494 := by exact prefixLift 2468494
  have htrace : WordTrace (prefixWord ++ tailWord_2468494) baseStart_2468494 baseEnd_2468494 := by
    simpa [prefixWord, tailWord_2468494, baseEnd_2468494] using wordTrace_append hprefix tailTrace_2468494
  have hstable : (prefixWord ++ tailWord_2468494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468494).length < 2 ^ (prefixWord ++ tailWord_2468494).sum := by decide
  have hdescent : baseEnd_2468494 < baseStart_2468494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468534 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2468534 : Nat := 118140960795 + 2468534 * 2 ^ 59
def prefixEnd_2468534 : Nat := 4983230072969 + 3 ^ 40 * 2468534 * 2
def baseEnd_2468534 : Nat := 845029635977300055381617

theorem tailTrace_2468534 : CollatzResearch.WordTrace tailWord_2468534 prefixEnd_2468534 845029635977300055381617 := by
  unfold tailWord_2468534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627176977433149055478291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60023221092620256591768437 5627176977433149055478291)
  ·
    refine ⟨8440765466149723583217437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5627176977433149055478291 8440765466149723583217437)
    ·
      refine ⟨3165287049806146343706539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8440765466149723583217437 3165287049806146343706539)
      ·
        refine ⟨4747930574709219515559809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3165287049806146343706539 4747930574709219515559809)
        ·
          refine ⟨3560947931031914636669857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4747930574709219515559809 3560947931031914636669857)
          ·
            refine ⟨2670710948273935977502393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3560947931031914636669857 2670710948273935977502393)
            ·
              refine ⟨2003033211205451983126795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2670710948273935977502393 2003033211205451983126795)
              ·
                refine ⟨3004549816808177974690193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003033211205451983126795 3004549816808177974690193)
                ·
                  refine ⟨2253412362606133481017645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004549816808177974690193 2253412362606133481017645)
                  ·
                    refine ⟨845029635977300055381617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253412362606133481017645 845029635977300055381617)
                    ·
                      rfl

theorem cell22_2468534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2468534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468534 prefixEnd_2468534 := by exact prefixLift 2468534
  have htrace : WordTrace (prefixWord ++ tailWord_2468534) baseStart_2468534 baseEnd_2468534 := by
    simpa [prefixWord, tailWord_2468534, baseEnd_2468534] using wordTrace_append hprefix tailTrace_2468534
  have hstable : (prefixWord ++ tailWord_2468534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468534).length < 2 ^ (prefixWord ++ tailWord_2468534).sum := by decide
  have hdescent : baseEnd_2468534 < baseStart_2468534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468541 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2468541 : Nat := 118140960795 + 2468541 * 2 ^ 59
def prefixEnd_2468541 : Nat := 4983230072969 + 3 ^ 40 * 2468541 * 2
def baseEnd_2468541 : Nat := 281677344073451456818865

theorem tailTrace_2468541 : CollatzResearch.WordTrace tailWord_2468541 prefixEnd_2468541 281677344073451456818865 := by
  unfold tailWord_2468541
  simp only [CollatzResearch.WordTrace]
  refine ⟨90035086949905025083157477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60023391299936683388771651 90035086949905025083157477)
  ·
    refine ⟨16881578803107192203092027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90035086949905025083157477 16881578803107192203092027)
    ·
      refine ⟨25322368204660788304638041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16881578803107192203092027 25322368204660788304638041)
      ·
        refine ⟨18991776153495591228478531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25322368204660788304638041 18991776153495591228478531)
        ·
          refine ⟨28487664230243386842717797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18991776153495591228478531 28487664230243386842717797)
          ·
            refine ⟨5341437043170635033009587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28487664230243386842717797 5341437043170635033009587)
            ·
              refine ⟨8012155564755952549514381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341437043170635033009587 8012155564755952549514381)
              ·
                refine ⟨3004558336783482206067893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8012155564755952549514381 3004558336783482206067893)
                ·
                  refine ⟨281677344073451456818865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3004558336783482206067893 281677344073451456818865)
                  ·
                    rfl

theorem cell22_2468541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2468541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468541 prefixEnd_2468541 := by exact prefixLift 2468541
  have htrace : WordTrace (prefixWord ++ tailWord_2468541) baseStart_2468541 baseEnd_2468541 := by
    simpa [prefixWord, tailWord_2468541, baseEnd_2468541] using wordTrace_append hprefix tailTrace_2468541
  have hstable : (prefixWord ++ tailWord_2468541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468541).length < 2 ^ (prefixWord ++ tailWord_2468541).sum := by decide
  have hdescent : baseEnd_2468541 < baseStart_2468541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468599 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2468599 : Nat := 118140960795 + 2468599 * 2 ^ 59
def prefixEnd_2468599 : Nat := 4983230072969 + 3 ^ 40 * 2468599 * 2
def baseEnd_2468599 : Nat := 845051886805661552506417

theorem tailTrace_2468599 : CollatzResearch.WordTrace tailWord_2468599 prefixEnd_2468599 845051886805661552506417 := by
  unfold tailWord_2468599
  simp only [CollatzResearch.WordTrace]
  refine ⟨90037202383694900988768851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60024801589129933992512567 90037202383694900988768851)
  ·
    refine ⟨135055803575542351483153277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90037202383694900988768851 135055803575542351483153277)
    ·
      refine ⟨50645926340828381806182479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135055803575542351483153277 50645926340828381806182479)
      ·
        refine ⟨75968889511242572709273719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50645926340828381806182479 75968889511242572709273719)
        ·
          refine ⟨113953334266863859063910579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75968889511242572709273719 113953334266863859063910579)
          ·
            refine ⟨170930001400295788595865869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113953334266863859063910579 170930001400295788595865869)
            ·
              refine ⟨64098750525110920723449701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170930001400295788595865869 64098750525110920723449701)
              ·
                refine ⟨12018515723458297635646819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64098750525110920723449701 12018515723458297635646819)
                ·
                  refine ⟨18027773585187446453470229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12018515723458297635646819 18027773585187446453470229)
                  ·
                    refine ⟨845051886805661552506417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18027773585187446453470229 845051886805661552506417)
                    ·
                      rfl

theorem cell22_2468599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2468599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468599 prefixEnd_2468599 := by exact prefixLift 2468599
  have htrace : WordTrace (prefixWord ++ tailWord_2468599) baseStart_2468599 baseEnd_2468599 := by
    simpa [prefixWord, tailWord_2468599, baseEnd_2468599] using wordTrace_append hprefix tailTrace_2468599
  have hstable : (prefixWord ++ tailWord_2468599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468599).length < 2 ^ (prefixWord ++ tailWord_2468599).sum := by decide
  have hdescent : baseEnd_2468599 < baseStart_2468599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468616 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_2468616 : Nat := 118140960795 + 2468616 * 2 ^ 59
def prefixEnd_2468616 : Nat := 4983230072969 + 3 ^ 40 * 2468616 * 2
def baseEnd_2468616 : Nat := 845057706253079174831365

theorem tailTrace_2468616 : CollatzResearch.WordTrace tailWord_2468616 prefixEnd_2468616 845057706253079174831365 := by
  unfold tailWord_2468616
  simp only [CollatzResearch.WordTrace]
  refine ⟨45018911212316656446068851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60025214949755541928091801 45018911212316656446068851)
  ·
    refine ⟨67528366818474984669103277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45018911212316656446068851 67528366818474984669103277)
    ·
      refine ⟨25323137556928119250913729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67528366818474984669103277 25323137556928119250913729)
      ·
        refine ⟨18992353167696089438185297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25323137556928119250913729 18992353167696089438185297)
        ·
          refine ⟨14244264875772067078638973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18992353167696089438185297 14244264875772067078638973)
          ·
            refine ⟨5341599328414525154489615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14244264875772067078638973 5341599328414525154489615)
            ·
              refine ⟨8012398992621787731734423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341599328414525154489615 8012398992621787731734423)
              ·
                refine ⟨12018598488932681597601635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012398992621787731734423 12018598488932681597601635)
                ·
                  refine ⟨18027897733399022396402453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12018598488932681597601635 18027897733399022396402453)
                  ·
                    refine ⟨845057706253079174831365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18027897733399022396402453 845057706253079174831365)
                    ·
                      rfl

theorem cell22_2468616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_2468616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468616 prefixEnd_2468616 := by exact prefixLift 2468616
  have htrace : WordTrace (prefixWord ++ tailWord_2468616) baseStart_2468616 baseEnd_2468616 := by
    simpa [prefixWord, tailWord_2468616, baseEnd_2468616] using wordTrace_append hprefix tailTrace_2468616
  have hstable : (prefixWord ++ tailWord_2468616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468616).length < 2 ^ (prefixWord ++ tailWord_2468616).sum := by decide
  have hdescent : baseEnd_2468616 < baseStart_2468616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468631 : List Nat := [1, 1, 3, 4, 3, 1, 9]
def baseStart_2468631 : Nat := 118140960795 + 2468631 * 2 ^ 59
def prefixEnd_2468631 : Nat := 4983230072969 + 3 ^ 40 * 2468631 * 2
def baseEnd_2468631 : Nat := 31298623742949042063197

theorem tailTrace_2468631 : CollatzResearch.WordTrace tailWord_2468631 prefixEnd_2468631 31298623742949042063197 := by
  unfold tailWord_2468631
  simp only [CollatzResearch.WordTrace]
  refine ⟨90038369519578970453933747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60025579679719313635955831 90038369519578970453933747)
  ·
    refine ⟨135057554279368455680900621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90038369519578970453933747 135057554279368455680900621)
    ·
      refine ⟨50646582854763170880337733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135057554279368455680900621 50646582854763170880337733)
      ·
        refine ⟨9496234285268094540063325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50646582854763170880337733 9496234285268094540063325)
        ·
          refine ⟨3561087856975535452523747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9496234285268094540063325 3561087856975535452523747)
          ·
            refine ⟨5341631785463303178785621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561087856975535452523747 5341631785463303178785621)
            ·
              refine ⟨31298623742949042063197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5341631785463303178785621 31298623742949042063197)
              ·
                rfl

theorem cell22_2468631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 9].length) (baseStart_2468631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468631 prefixEnd_2468631 := by exact prefixLift 2468631
  have htrace : WordTrace (prefixWord ++ tailWord_2468631) baseStart_2468631 baseEnd_2468631 := by
    simpa [prefixWord, tailWord_2468631, baseEnd_2468631] using wordTrace_append hprefix tailTrace_2468631
  have hstable : (prefixWord ++ tailWord_2468631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468631).length < 2 ^ (prefixWord ++ tailWord_2468631).sum := by decide
  have hdescent : baseEnd_2468631 < baseStart_2468631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468697 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 1, 3]
def baseStart_2468697 : Nat := 118140960795 + 2468697 * 2 ^ 59
def prefixEnd_2468697 : Nat := 4983230072969 + 3 ^ 40 * 2468697 * 2
def baseEnd_2468697 : Nat := 845085434208421963556117

theorem tailTrace_2468697 : CollatzResearch.WordTrace tailWord_2468697 prefixEnd_2468697 845085434208421963556117 := by
  unfold tailWord_2468697
  simp only [CollatzResearch.WordTrace]
  refine ⟨90040776737339863725836345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60027184491559909150557563 90040776737339863725836345)
  ·
    refine ⟨67530582553004897794377259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90040776737339863725836345 67530582553004897794377259)
    ·
      refine ⟨101295873829507346691565889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67530582553004897794377259 101295873829507346691565889)
      ·
        refine ⟨75971905372130510018674417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101295873829507346691565889 75971905372130510018674417)
        ·
          refine ⟨56978929029097882514005813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75971905372130510018674417 56978929029097882514005813)
          ·
            refine ⟨5341774596477926485688045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56978929029097882514005813 5341774596477926485688045)
            ·
              refine ⟨2003165473679222432133017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5341774596477926485688045 2003165473679222432133017)
              ·
                refine ⟨1502374105259416824099763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003165473679222432133017 1502374105259416824099763)
                ·
                  refine ⟨2253561157889125236149645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502374105259416824099763 2253561157889125236149645)
                  ·
                    refine ⟨845085434208421963556117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253561157889125236149645 845085434208421963556117)
                    ·
                      rfl

theorem cell22_2468697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_2468697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468697 prefixEnd_2468697 := by exact prefixLift 2468697
  have htrace : WordTrace (prefixWord ++ tailWord_2468697) baseStart_2468697 baseEnd_2468697 := by
    simpa [prefixWord, tailWord_2468697, baseEnd_2468697] using wordTrace_append hprefix tailTrace_2468697
  have hstable : (prefixWord ++ tailWord_2468697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468697).length < 2 ^ (prefixWord ++ tailWord_2468697).sum := by decide
  have hdescent : baseEnd_2468697 < baseStart_2468697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468723 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 1, 4]
def baseStart_2468723 : Nat := 118140960795 + 2468723 * 2 ^ 59
def prefixEnd_2468723 : Nat := 4983230072969 + 3 ^ 40 * 2468723 * 2
def baseEnd_2468723 : Nat := 845094334539766562406037

theorem tailTrace_2468723 : CollatzResearch.WordTrace tailWord_2468723 prefixEnd_2468723 845094334539766562406037 := by
  unfold tailWord_2468723
  simp only [CollatzResearch.WordTrace]
  refine ⟨90041725035245670166282823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60027816690163780110855215 90041725035245670166282823)
  ·
    refine ⟨135062587552868505249424235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90041725035245670166282823 135062587552868505249424235)
    ·
      refine ⟨202593881329302757874136353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135062587552868505249424235 202593881329302757874136353)
      ·
        refine ⟨151945410996977068405602265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202593881329302757874136353 151945410996977068405602265)
        ·
          refine ⟨113959058247732801304201699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151945410996977068405602265 113959058247732801304201699)
          ·
            refine ⟨170938587371599201956302549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113959058247732801304201699 170938587371599201956302549)
            ·
              refine ⟨4006373141521856295850841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 170938587371599201956302549 4006373141521856295850841)
              ·
                refine ⟨3004779856141392221888131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006373141521856295850841 3004779856141392221888131)
                ·
                  refine ⟨4507169784212088332832197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004779856141392221888131 4507169784212088332832197)
                  ·
                    refine ⟨845094334539766562406037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4507169784212088332832197 845094334539766562406037)
                    ·
                      rfl

theorem cell22_2468723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 4].length) (baseStart_2468723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468723 prefixEnd_2468723 := by exact prefixLift 2468723
  have htrace : WordTrace (prefixWord ++ tailWord_2468723) baseStart_2468723 baseEnd_2468723 := by
    simpa [prefixWord, tailWord_2468723, baseEnd_2468723] using wordTrace_append hprefix tailTrace_2468723
  have hstable : (prefixWord ++ tailWord_2468723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468723).length < 2 ^ (prefixWord ++ tailWord_2468723).sum := by decide
  have hdescent : baseEnd_2468723 < baseStart_2468723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468770 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2468770 : Nat := 118140960795 + 2468770 * 2 ^ 59
def prefixEnd_2468770 : Nat := 4983230072969 + 3 ^ 40 * 2468770 * 2
def baseEnd_2468770 : Nat := 845110423600274106480893

theorem tailTrace_2468770 : CollatzResearch.WordTrace tailWord_2468770 prefixEnd_2468770 845110423600274106480893 := by
  unfold tailWord_2468770
  simp only [CollatzResearch.WordTrace]
  refine ⟨22510859816518849298310941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60028959510716931462162509 22510859816518849298310941)
  ·
    refine ⟨8441572431194568486866603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22510859816518849298310941 8441572431194568486866603)
    ·
      refine ⟨12662358646791852730299905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441572431194568486866603 12662358646791852730299905)
      ·
        refine ⟨9496768985093889547724929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12662358646791852730299905 9496768985093889547724929)
        ·
          refine ⟨7122576738820417160793697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9496768985093889547724929 7122576738820417160793697)
          ·
            refine ⟨5341932554115312870595273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7122576738820417160793697 5341932554115312870595273)
            ·
              refine ⟨4006449415586484652946455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5341932554115312870595273 4006449415586484652946455)
              ·
                refine ⟨6009674123379726979419683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006449415586484652946455 6009674123379726979419683)
                ·
                  refine ⟨9014511185069590469129525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009674123379726979419683 9014511185069590469129525)
                  ·
                    refine ⟨845110423600274106480893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9014511185069590469129525 845110423600274106480893)
                    ·
                      rfl

theorem cell22_2468770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2468770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468770 prefixEnd_2468770 := by exact prefixLift 2468770
  have htrace : WordTrace (prefixWord ++ tailWord_2468770) baseStart_2468770 baseEnd_2468770 := by
    simpa [prefixWord, tailWord_2468770, baseEnd_2468770] using wordTrace_append hprefix tailTrace_2468770
  have hstable : (prefixWord ++ tailWord_2468770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468770).length < 2 ^ (prefixWord ++ tailWord_2468770).sum := by decide
  have hdescent : baseEnd_2468770 < baseStart_2468770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468806 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2468806 : Nat := 118140960795 + 2468806 * 2 ^ 59
def prefixEnd_2468806 : Nat := 4983230072969 + 3 ^ 40 * 2468806 * 2
def baseEnd_2468806 : Nat := 281707582378660670860261

theorem tailTrace_2468806 : CollatzResearch.WordTrace tailWord_2468806 prefixEnd_2468806 281707582378660670860261 := by
  unfold tailWord_2468806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813898509185780479423571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60029834862629983561036181 2813898509185780479423571)
  ·
    refine ⟨4220847763778670719135357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2813898509185780479423571 4220847763778670719135357)
    ·
      refine ⟨1582817911417001519675759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4220847763778670719135357 1582817911417001519675759)
      ·
        refine ⟨2374226867125502279513639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582817911417001519675759 2374226867125502279513639)
        ·
          refine ⟨3561340300688253419270459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374226867125502279513639 3561340300688253419270459)
          ·
            refine ⟨5342010451032380128905689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561340300688253419270459 5342010451032380128905689)
            ·
              refine ⟨4006507838274285096679267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342010451032380128905689 4006507838274285096679267)
              ·
                refine ⟨6009761757411427645018901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006507838274285096679267 6009761757411427645018901)
                ·
                  refine ⟨281707582378660670860261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6009761757411427645018901 281707582378660670860261)
                  ·
                    rfl

theorem cell22_2468806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2468806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468806 prefixEnd_2468806 := by exact prefixLift 2468806
  have htrace : WordTrace (prefixWord ++ tailWord_2468806) baseStart_2468806 baseEnd_2468806 := by
    simpa [prefixWord, tailWord_2468806, baseEnd_2468806] using wordTrace_append hprefix tailTrace_2468806
  have hstable : (prefixWord ++ tailWord_2468806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468806).length < 2 ^ (prefixWord ++ tailWord_2468806).sum := by decide
  have hdescent : baseEnd_2468806 < baseStart_2468806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468815 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 3, 3]
def baseStart_2468815 : Nat := 118140960795 + 2468815 * 2 ^ 59
def prefixEnd_2468815 : Nat := 4983230072969 + 3 ^ 40 * 2468815 * 2
def baseEnd_2468815 : Nat := 845125828019908989105755

theorem tailTrace_2468815 : CollatzResearch.WordTrace tailWord_2468815 prefixEnd_2468815 845125828019908989105755 := by
  unfold tailWord_2468815
  simp only [CollatzResearch.WordTrace]
  refine ⟨90045080550912369878631899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60030053700608246585754599 90045080550912369878631899)
  ·
    refine ⟨135067620826368554817947849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90045080550912369878631899 135067620826368554817947849)
    ·
      refine ⟨101300715619776416113460887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135067620826368554817947849 101300715619776416113460887)
      ·
        refine ⟨151951073429664624170191331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101300715619776416113460887 151951073429664624170191331)
        ·
          refine ⟨227926610144496936255286997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151951073429664624170191331 227926610144496936255286997)
          ·
            refine ⟨5342029925261646943483289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 227926610144496936255286997 5342029925261646943483289)
            ·
              refine ⟨4006522443946235207612467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342029925261646943483289 4006522443946235207612467)
              ·
                refine ⟨6009783665919352811418701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006522443946235207612467 6009783665919352811418701)
                ·
                  refine ⟨2253668874719757304282013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6009783665919352811418701 2253668874719757304282013)
                  ·
                    refine ⟨845125828019908989105755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253668874719757304282013 845125828019908989105755)
                    ·
                      rfl

theorem cell22_2468815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_2468815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468815 prefixEnd_2468815 := by exact prefixLift 2468815
  have htrace : WordTrace (prefixWord ++ tailWord_2468815) baseStart_2468815 baseEnd_2468815 := by
    simpa [prefixWord, tailWord_2468815, baseEnd_2468815] using wordTrace_append hprefix tailTrace_2468815
  have hstable : (prefixWord ++ tailWord_2468815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468815).length < 2 ^ (prefixWord ++ tailWord_2468815).sum := by decide
  have hdescent : baseEnd_2468815 < baseStart_2468815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
