import V185TrunkScan23Chunk1159

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6872267 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4]
def baseStart_6872267 : Nat := 118140960795 + 6872267 * 2 ^ 59
def prefixEnd_6872267 : Nat := 4983230072969 + 3 ^ 40 * 6872267 * 2
def baseEnd_6872267 : Nat := 3528776157031968957457525

theorem tailTrace_6872267 : CollatzResearch.WordTrace tailWord_6872267 prefixEnd_6872267 3528776157031968957457525 := by
  unfold tailWord_6872267
  simp only [CollatzResearch.WordTrace]
  refine ⟨250652169393957823606495055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167101446262638549070996703 250652169393957823606495055)
  ·
    refine ⟨375978254090936735409742583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250652169393957823606495055 375978254090936735409742583)
    ·
      refine ⟨563967381136405103114613875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375978254090936735409742583 563967381136405103114613875)
      ·
        refine ⟨845951071704607654671920813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563967381136405103114613875 845951071704607654671920813)
        ·
          refine ⟨317231651889227870501970305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 845951071704607654671920813 317231651889227870501970305)
          ·
            refine ⟨237923738916920902876477729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317231651889227870501970305 237923738916920902876477729)
            ·
              refine ⟨178442804187690677157358297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237923738916920902876477729 178442804187690677157358297)
              ·
                refine ⟨133832103140768007868018723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178442804187690677157358297 133832103140768007868018723)
                ·
                  refine ⟨200748154711152011802028085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133832103140768007868018723 200748154711152011802028085)
                  ·
                    refine ⟨18820139504170501106440133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200748154711152011802028085 18820139504170501106440133)
                    ·
                      refine ⟨3528776157031968957457525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18820139504170501106440133 3528776157031968957457525)
                      ·
                        rfl

theorem cell23_6872267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_6872267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872267 prefixEnd_6872267 := by exact prefixLift 6872267
  have htrace : WordTrace (prefixWord ++ tailWord_6872267) baseStart_6872267 baseEnd_6872267 := by
    simpa [prefixWord, tailWord_6872267, baseEnd_6872267] using wordTrace_append hprefix tailTrace_6872267
  have hstable : (prefixWord ++ tailWord_6872267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872267).length < 2 ^ (prefixWord ++ tailWord_6872267).sum := by decide
  have hdescent : baseEnd_6872267 < baseStart_6872267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872295 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6872295 : Nat := 118140960795 + 6872295 * 2 ^ 59
def prefixEnd_6872295 : Nat := 4983230072969 + 3 ^ 40 * 6872295 * 2
def baseEnd_6872295 : Nat := 3528790534490294847907397

theorem tailTrace_6872295 : CollatzResearch.WordTrace tailWord_6872295 prefixEnd_6872295 3528790534490294847907397 := by
  unfold tailWord_6872295
  simp only [CollatzResearch.WordTrace]
  refine ⟨250653190637856384388514339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167102127091904256259009559 250653190637856384388514339)
  ·
    refine ⟨375979785956784576582771509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250653190637856384388514339 375979785956784576582771509)
    ·
      refine ⟨35248104933448554054634829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 375979785956784576582771509 35248104933448554054634829)
      ·
        refine ⟨13218039350043207770488061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35248104933448554054634829 13218039350043207770488061)
        ·
          refine ⟨4956764756266202913933023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13218039350043207770488061 4956764756266202913933023)
          ·
            refine ⟨7435147134399304370899535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956764756266202913933023 7435147134399304370899535)
            ·
              refine ⟨11152720701598956556349303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435147134399304370899535 11152720701598956556349303)
              ·
                refine ⟨16729081052398434834523955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152720701598956556349303 16729081052398434834523955)
                ·
                  refine ⟨25093621578597652251785933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16729081052398434834523955 25093621578597652251785933)
                  ·
                    refine ⟨9410108091974119594419725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25093621578597652251785933 9410108091974119594419725)
                    ·
                      refine ⟨3528790534490294847907397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410108091974119594419725 3528790534490294847907397)
                      ·
                        rfl

theorem cell23_6872295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6872295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872295 prefixEnd_6872295 := by exact prefixLift 6872295
  have htrace : WordTrace (prefixWord ++ tailWord_6872295) baseStart_6872295 baseEnd_6872295 := by
    simpa [prefixWord, tailWord_6872295, baseEnd_6872295] using wordTrace_append hprefix tailTrace_6872295
  have hstable : (prefixWord ++ tailWord_6872295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872295).length < 2 ^ (prefixWord ++ tailWord_6872295).sum := by decide
  have hdescent : baseEnd_6872295 < baseStart_6872295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872371 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 2, 5]
def baseStart_6872371 : Nat := 118140960795 + 6872371 * 2 ^ 59
def prefixEnd_6872371 : Nat := 4983230072969 + 3 ^ 40 * 6872371 * 2
def baseEnd_6872371 : Nat := 1176276519673345516852349

theorem tailTrace_6872371 : CollatzResearch.WordTrace tailWord_6872371 prefixEnd_6872371 1176276519673345516852349 := by
  unfold tailWord_6872371
  simp only [CollatzResearch.WordTrace]
  refine ⟨250655962585581049368280967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167103975057054032912187311 250655962585581049368280967)
  ·
    refine ⟨375983943878371574052421451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250655962585581049368280967 375983943878371574052421451)
    ·
      refine ⟨563975915817557361078632177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375983943878371574052421451 563975915817557361078632177)
      ·
        refine ⟨422981936863168020808974133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563975915817557361078632177 422981936863168020808974133)
        ·
          refine ⟨39654556580922001950841325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 422981936863168020808974133 39654556580922001950841325)
          ·
            refine ⟨14870458717845750731565497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39654556580922001950841325 14870458717845750731565497)
            ·
              refine ⟨11152844038384313048674123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14870458717845750731565497 11152844038384313048674123)
              ·
                refine ⟨16729266057576469573011185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152844038384313048674123 16729266057576469573011185)
                ·
                  refine ⟨12546949543182352179758389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16729266057576469573011185 12546949543182352179758389)
                  ·
                    refine ⟨1176276519673345516852349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12546949543182352179758389 1176276519673345516852349)
                    ·
                      rfl

theorem cell23_6872371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 5].length) (baseStart_6872371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872371 prefixEnd_6872371 := by exact prefixLift 6872371
  have htrace : WordTrace (prefixWord ++ tailWord_6872371) baseStart_6872371 baseEnd_6872371 := by
    simpa [prefixWord, tailWord_6872371, baseEnd_6872371] using wordTrace_append hprefix tailTrace_6872371
  have hstable : (prefixWord ++ tailWord_6872371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872371).length < 2 ^ (prefixWord ++ tailWord_6872371).sum := by decide
  have hdescent : baseEnd_6872371 < baseStart_6872371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872388 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6872388 : Nat := 118140960795 + 6872388 * 2 ^ 59
def prefixEnd_6872388 : Nat := 4983230072969 + 3 ^ 40 * 6872388 * 2
def baseEnd_6872388 : Nat := 1176279429397054328014823

theorem tailTrace_6872388 : CollatzResearch.WordTrace tailWord_6872388 prefixEnd_6872388 1176279429397054328014823 := by
  unfold tailWord_6872388
  simp only [CollatzResearch.WordTrace]
  refine ⟨125328291313259730635824909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167104388417679640847766545 125328291313259730635824909)
  ·
    refine ⟨46998109242472398988434341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125328291313259730635824909 46998109242472398988434341)
    ·
      refine ⟨8812145482963574810331439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46998109242472398988434341 8812145482963574810331439)
      ·
        refine ⟨13218218224445362215497159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812145482963574810331439 13218218224445362215497159)
        ·
          refine ⟨19827327336668043323245739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13218218224445362215497159 19827327336668043323245739)
          ·
            refine ⟨29740991005002064984868609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19827327336668043323245739 29740991005002064984868609)
            ·
              refine ⟨22305743253751548738651457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29740991005002064984868609 22305743253751548738651457)
              ·
                refine ⟨16729307440313661553988593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22305743253751548738651457 16729307440313661553988593)
                ·
                  refine ⟨12546980580235246165491445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16729307440313661553988593 12546980580235246165491445)
                  ·
                    refine ⟨1176279429397054328014823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12546980580235246165491445 1176279429397054328014823)
                    ·
                      rfl

theorem cell23_6872388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6872388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872388 prefixEnd_6872388 := by exact prefixLift 6872388
  have htrace : WordTrace (prefixWord ++ tailWord_6872388) baseStart_6872388 baseEnd_6872388 := by
    simpa [prefixWord, tailWord_6872388, baseEnd_6872388] using wordTrace_append hprefix tailTrace_6872388
  have hstable : (prefixWord ++ tailWord_6872388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872388).length < 2 ^ (prefixWord ++ tailWord_6872388).sum := by decide
  have hdescent : baseEnd_6872388 < baseStart_6872388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872391 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_6872391 : Nat := 118140960795 + 6872391 * 2 ^ 59
def prefixEnd_6872391 : Nat := 4983230072969 + 3 ^ 40 * 6872391 * 2
def baseEnd_6872391 : Nat := 3528839828633126472306955

theorem tailTrace_6872391 : CollatzResearch.WordTrace tailWord_6872391 prefixEnd_6872391 3528839828633126472306955 := by
  unfold tailWord_6872391
  simp only [CollatzResearch.WordTrace]
  refine ⟨250656692045508592784009027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167104461363672395189339351 250656692045508592784009027)
  ·
    refine ⟨375985038068262889176013541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250656692045508592784009027 375985038068262889176013541)
    ·
      refine ⟨70497194637799291720502539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375985038068262889176013541 70497194637799291720502539)
      ·
        refine ⟨105745791956698937580753809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70497194637799291720502539 105745791956698937580753809)
        ·
          refine ⟨79309343967524203185565357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105745791956698937580753809 79309343967524203185565357)
          ·
            refine ⟨29741003987821576194587009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79309343967524203185565357 29741003987821576194587009)
            ·
              refine ⟨22305752990866182145940257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29741003987821576194587009 22305752990866182145940257)
              ·
                refine ⟨16729314743149636609455193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22305752990866182145940257 16729314743149636609455193)
                ·
                  refine ⟨12546986057362227457091395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16729314743149636609455193 12546986057362227457091395)
                  ·
                    refine ⟨18820479086043341185637093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12546986057362227457091395 18820479086043341185637093)
                    ·
                      refine ⟨3528839828633126472306955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18820479086043341185637093 3528839828633126472306955)
                      ·
                        rfl

theorem cell23_6872391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_6872391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872391 prefixEnd_6872391 := by exact prefixLift 6872391
  have htrace : WordTrace (prefixWord ++ tailWord_6872391) baseStart_6872391 baseEnd_6872391 := by
    simpa [prefixWord, tailWord_6872391, baseEnd_6872391] using wordTrace_append hprefix tailTrace_6872391
  have hstable : (prefixWord ++ tailWord_6872391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872391).length < 2 ^ (prefixWord ++ tailWord_6872391).sum := by decide
  have hdescent : baseEnd_6872391 < baseStart_6872391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872401 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 3, 4]
def baseStart_6872401 : Nat := 118140960795 + 6872401 * 2 ^ 59
def prefixEnd_6872401 : Nat := 4983230072969 + 3 ^ 40 * 6872401 * 2
def baseEnd_6872401 : Nat := 1176281654479890477727303

theorem tailTrace_6872401 : CollatzResearch.WordTrace tailWord_6872401 prefixEnd_6872401 1176281654479890477727303 := by
  unfold tailWord_6872401
  simp only [CollatzResearch.WordTrace]
  refine ⟨250657056775472364491873057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167104704516981576327915371 250657056775472364491873057)
  ·
    refine ⟨187992792581604273368904793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250657056775472364491873057 187992792581604273368904793)
    ·
      refine ⟨140994594436203205026678595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187992792581604273368904793 140994594436203205026678595)
      ·
        refine ⟨211491891654304807540017893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140994594436203205026678595 211491891654304807540017893)
        ·
          refine ⟨39654729685182151413753355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211491891654304807540017893 39654729685182151413753355)
          ·
            refine ⟨59482094527773227120630033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39654729685182151413753355 59482094527773227120630033)
            ·
              refine ⟨44611570895829920340472525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59482094527773227120630033 44611570895829920340472525)
              ·
                refine ⟨16729339085936220127677197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44611570895829920340472525 16729339085936220127677197)
                ·
                  refine ⟨6273502157226082547878949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16729339085936220127677197 6273502157226082547878949)
                  ·
                    refine ⟨1176281654479890477727303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273502157226082547878949 1176281654479890477727303)
                    ·
                      rfl

theorem cell23_6872401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_6872401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872401 prefixEnd_6872401 := by exact prefixLift 6872401
  have htrace : WordTrace (prefixWord ++ tailWord_6872401) baseStart_6872401 baseEnd_6872401 := by
    simpa [prefixWord, tailWord_6872401, baseEnd_6872401] using wordTrace_append hprefix tailTrace_6872401
  have hstable : (prefixWord ++ tailWord_6872401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872401).length < 2 ^ (prefixWord ++ tailWord_6872401).sum := by decide
  have hdescent : baseEnd_6872401 < baseStart_6872401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872418 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_6872418 : Nat := 118140960795 + 6872418 * 2 ^ 59
def prefixEnd_6872418 : Nat := 4983230072969 + 3 ^ 40 * 6872418 * 2
def baseEnd_6872418 : Nat := 1176284564203599288889777

theorem tailTrace_6872418 : CollatzResearch.WordTrace tailWord_6872418 prefixEnd_6872418 1176284564203599288889777 := by
  unfold tailWord_6872418
  simp only [CollatzResearch.WordTrace]
  refine ⟨62664419204102694098810477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167105117877607184263494605 62664419204102694098810477)
  ·
    refine ⟨23499157201538510287053929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62664419204102694098810477 23499157201538510287053929)
    ·
      refine ⟨17624367901153882715290447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23499157201538510287053929 17624367901153882715290447)
      ·
        refine ⟨26436551851730824072935671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17624367901153882715290447 26436551851730824072935671)
        ·
          refine ⟨39654827777596236109403507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26436551851730824072935671 39654827777596236109403507)
          ·
            refine ⟨59482241666394354164105261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39654827777596236109403507 59482241666394354164105261)
            ·
              refine ⟨22305840624897882811539473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59482241666394354164105261 22305840624897882811539473)
              ·
                refine ⟨16729380468673412108654605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22305840624897882811539473 16729380468673412108654605)
                ·
                  refine ⟨6273517675752529540745477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16729380468673412108654605 6273517675752529540745477)
                  ·
                    refine ⟨1176284564203599288889777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273517675752529540745477 1176284564203599288889777)
                    ·
                      rfl

theorem cell23_6872418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_6872418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872418 prefixEnd_6872418 := by exact prefixLift 6872418
  have htrace : WordTrace (prefixWord ++ tailWord_6872418) baseStart_6872418 baseEnd_6872418 := by
    simpa [prefixWord, tailWord_6872418, baseEnd_6872418] using wordTrace_append hprefix tailTrace_6872418
  have hstable : (prefixWord ++ tailWord_6872418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872418).length < 2 ^ (prefixWord ++ tailWord_6872418).sum := by decide
  have hdescent : baseEnd_6872418 < baseStart_6872418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872428 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_6872428 : Nat := 118140960795 + 6872428 * 2 ^ 59
def prefixEnd_6872428 : Nat := 4983230072969 + 3 ^ 40 * 6872428 * 2
def baseEnd_6872428 : Nat := 3528858827417342827544285

theorem tailTrace_6872428 : CollatzResearch.WordTrace tailWord_6872428 prefixEnd_6872428 3528858827417342827544285 := by
  unfold tailWord_6872428
  simp only [CollatzResearch.WordTrace]
  refine ⟨125329020773187274051552969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167105361030916365402070625 125329020773187274051552969)
  ·
    refine ⟨93996765579890455538664727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125329020773187274051552969 93996765579890455538664727)
    ·
      refine ⟨140995148369835683307997091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93996765579890455538664727 140995148369835683307997091)
      ·
        refine ⟨211492722554753524961995637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140995148369835683307997091 211492722554753524961995637)
        ·
          refine ⟨19827442739508142965187091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211492722554753524961995637 19827442739508142965187091)
          ·
            refine ⟨29741164109262214447780637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19827442739508142965187091 29741164109262214447780637)
            ·
              refine ⟨11152936540973330417917739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29741164109262214447780637 11152936540973330417917739)
              ·
                refine ⟨16729404811459995626876609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152936540973330417917739 16729404811459995626876609)
                ·
                  refine ⟨12547053608594996720157457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16729404811459995626876609 12547053608594996720157457)
                  ·
                    refine ⟨9410290206446247540118093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12547053608594996720157457 9410290206446247540118093)
                    ·
                      refine ⟨3528858827417342827544285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410290206446247540118093 3528858827417342827544285)
                      ·
                        rfl

theorem cell23_6872428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_6872428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872428 prefixEnd_6872428 := by exact prefixLift 6872428
  have htrace : WordTrace (prefixWord ++ tailWord_6872428) baseStart_6872428 baseEnd_6872428 := by
    simpa [prefixWord, tailWord_6872428, baseEnd_6872428] using wordTrace_append hprefix tailTrace_6872428
  have hstable : (prefixWord ++ tailWord_6872428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872428).length < 2 ^ (prefixWord ++ tailWord_6872428).sum := by decide
  have hdescent : baseEnd_6872428 < baseStart_6872428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872504 : List Nat := [2, 1, 2, 1, 2, 2, 13]
def baseStart_6872504 : Nat := 118140960795 + 6872504 * 2 ^ 59
def prefixEnd_6872504 : Nat := 4983230072969 + 3 ^ 40 * 6872504 * 2
def baseEnd_6872504 : Nat := 43566640147494870743135

theorem tailTrace_6872504 : CollatzResearch.WordTrace tailWord_6872504 prefixEnd_6872504 43566640147494870743135 := by
  unfold tailWord_6872504
  simp only [CollatzResearch.WordTrace]
  refine ⟨125330406747049606541436283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167107208996066142055248377 125330406747049606541436283)
  ·
    refine ⟨187995610120574409812154425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125330406747049606541436283 187995610120574409812154425)
    ·
      refine ⟨140996707590430807359115819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187995610120574409812154425 140996707590430807359115819)
      ·
        refine ⟨211495061385646211038673729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140996707590430807359115819 211495061385646211038673729)
        ·
          refine ⟨158621296039234658279005297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211495061385646211038673729 158621296039234658279005297)
          ·
            refine ⟨118965972029425993709253973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158621296039234658279005297 118965972029425993709253973)
            ·
              refine ⟨43566640147494870743135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 118965972029425993709253973 43566640147494870743135)
              ·
                rfl

theorem cell23_6872504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 13].length) (baseStart_6872504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872504 prefixEnd_6872504 := by exact prefixLift 6872504
  have htrace : WordTrace (prefixWord ++ tailWord_6872504) baseStart_6872504 baseEnd_6872504 := by
    simpa [prefixWord, tailWord_6872504, baseEnd_6872504] using wordTrace_append hprefix tailTrace_6872504
  have hstable : (prefixWord ++ tailWord_6872504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872504).length < 2 ^ (prefixWord ++ tailWord_6872504).sum := by decide
  have hdescent : baseEnd_6872504 < baseStart_6872504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872515 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 3, 2, 2]
def baseStart_6872515 : Nat := 118140960795 + 6872515 * 2 ^ 59
def prefixEnd_6872515 : Nat := 4983230072969 + 3 ^ 40 * 6872515 * 2
def baseEnd_6872515 : Nat := 3528903500234283987156385

theorem tailTrace_6872515 : CollatzResearch.WordTrace tailWord_6872515 prefixEnd_6872515 3528903500234283987156385 := by
  unfold tailWord_6872515
  simp only [CollatzResearch.WordTrace]
  refine ⟨250661214697059361961522999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167107476464706241307681999 250661214697059361961522999)
  ·
    refine ⟨375991822045589042942284499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250661214697059361961522999 375991822045589042942284499)
    ·
      refine ⟨563987733068383564413426749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375991822045589042942284499 563987733068383564413426749)
      ·
        refine ⟨211495399900643836655035031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563987733068383564413426749 211495399900643836655035031)
        ·
          refine ⟨317243099850965754982552547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211495399900643836655035031 317243099850965754982552547)
          ·
            refine ⟨475864649776448632473828821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317243099850965754982552547 475864649776448632473828821)
            ·
              refine ⟨11153077729135514823605363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 475864649776448632473828821 11153077729135514823605363)
              ·
                refine ⟨16729616593703272235408045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153077729135514823605363 16729616593703272235408045)
                ·
                  refine ⟨6273606222638727088278017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16729616593703272235408045 6273606222638727088278017)
                  ·
                    refine ⟨4705204666979045316208513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273606222638727088278017 4705204666979045316208513)
                    ·
                      refine ⟨3528903500234283987156385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705204666979045316208513 3528903500234283987156385)
                      ·
                        rfl

theorem cell23_6872515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_6872515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872515 prefixEnd_6872515 := by exact prefixLift 6872515
  have htrace : WordTrace (prefixWord ++ tailWord_6872515) baseStart_6872515 baseEnd_6872515 := by
    simpa [prefixWord, tailWord_6872515, baseEnd_6872515] using wordTrace_append hprefix tailTrace_6872515
  have hstable : (prefixWord ++ tailWord_6872515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872515).length < 2 ^ (prefixWord ++ tailWord_6872515).sum := by decide
  have hdescent : baseEnd_6872515 < baseStart_6872515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872532 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_6872532 : Nat := 118140960795 + 6872532 * 2 ^ 59
def prefixEnd_6872532 : Nat := 4983230072969 + 3 ^ 40 * 6872532 * 2
def baseEnd_6872532 : Nat := 3528912229405410420643807

theorem tailTrace_6872532 : CollatzResearch.WordTrace tailWord_6872532 prefixEnd_6872532 3528912229405410420643807 := by
  unfold tailWord_6872532
  simp only [CollatzResearch.WordTrace]
  refine ⟨125330917368998886932445925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167107889825331849243261233 125330917368998886932445925)
  ·
    refine ⟨23499547006687291299833611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125330917368998886932445925 23499547006687291299833611)
    ·
      refine ⟨35249320510030936949750417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23499547006687291299833611 35249320510030936949750417)
      ·
        refine ⟨26436990382523202712312813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35249320510030936949750417 26436990382523202712312813)
        ·
          refine ⟨9913871393446201017117305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26436990382523202712312813 9913871393446201017117305)
          ·
            refine ⟨7435403545084650762837979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913871393446201017117305 7435403545084650762837979)
            ·
              refine ⟨11153105317626976144256969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435403545084650762837979 11153105317626976144256969)
              ·
                refine ⟨8364828988220232108192727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11153105317626976144256969 8364828988220232108192727)
                ·
                  refine ⟨12547243482330348162289091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364828988220232108192727 12547243482330348162289091)
                  ·
                    refine ⟨18820865223495522243433637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12547243482330348162289091 18820865223495522243433637)
                    ·
                      refine ⟨3528912229405410420643807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18820865223495522243433637 3528912229405410420643807)
                      ·
                        rfl

theorem cell23_6872532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_6872532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872532 prefixEnd_6872532 := by exact prefixLift 6872532
  have htrace : WordTrace (prefixWord ++ tailWord_6872532) baseStart_6872532 baseEnd_6872532 := by
    simpa [prefixWord, tailWord_6872532, baseEnd_6872532] using wordTrace_append hprefix tailTrace_6872532
  have hstable : (prefixWord ++ tailWord_6872532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872532).length < 2 ^ (prefixWord ++ tailWord_6872532).sum := by decide
  have hdescent : baseEnd_6872532 < baseStart_6872532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872548 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_6872548 : Nat := 118140960795 + 6872548 * 2 ^ 59
def prefixEnd_6872548 : Nat := 4983230072969 + 3 ^ 40 * 6872548 * 2
def baseEnd_6872548 : Nat := 3528920445095882358043733

theorem tailTrace_6872548 : CollatzResearch.WordTrace tailWord_6872548 prefixEnd_6872548 3528920445095882358043733 := by
  unfold tailWord_6872548
  simp only [CollatzResearch.WordTrace]
  refine ⟨125331209152969904298737149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167108278870626539064982865 125331209152969904298737149)
  ·
    refine ⟨46999203432363714112026431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125331209152969904298737149 46999203432363714112026431)
    ·
      refine ⟨70498805148545571168039647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46999203432363714112026431 70498805148545571168039647)
      ·
        refine ⟨105748207722818356752059471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70498805148545571168039647 105748207722818356752059471)
        ·
          refine ⟨158622311584227535128089207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105748207722818356752059471 158622311584227535128089207)
          ·
            refine ⟨237933467376341302692133811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158622311584227535128089207 237933467376341302692133811)
            ·
              refine ⟨356900201064511954038200717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237933467376341302692133811 356900201064511954038200717)
              ·
                refine ⟨133837575399191982764325269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356900201064511954038200717 133837575399191982764325269)
                ·
                  refine ⟨6273636346837124192077747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133837575399191982764325269 6273636346837124192077747)
                  ·
                    refine ⟨9410454520255686288116621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273636346837124192077747 9410454520255686288116621)
                    ·
                      refine ⟨3528920445095882358043733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410454520255686288116621 3528920445095882358043733)
                      ·
                        rfl

theorem cell23_6872548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_6872548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872548 prefixEnd_6872548 := by exact prefixLift 6872548
  have htrace : WordTrace (prefixWord ++ tailWord_6872548) baseStart_6872548 baseEnd_6872548 := by
    simpa [prefixWord, tailWord_6872548, baseEnd_6872548] using wordTrace_append hprefix tailTrace_6872548
  have hstable : (prefixWord ++ tailWord_6872548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872548).length < 2 ^ (prefixWord ++ tailWord_6872548).sum := by decide
  have hdescent : baseEnd_6872548 < baseStart_6872548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872566 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_6872566 : Nat := 118140960795 + 6872566 * 2 ^ 59
def prefixEnd_6872566 : Nat := 4983230072969 + 3 ^ 40 * 6872566 * 2
def baseEnd_6872566 : Nat := 3528929687747663287618651

theorem tailTrace_6872566 : CollatzResearch.WordTrace tailWord_6872566 prefixEnd_6872566 3528929687747663287618651 := by
  unfold tailWord_6872566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15666442176242162354476847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167108716546583065114419701 15666442176242162354476847)
  ·
    refine ⟨23499663264363243531715271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15666442176242162354476847 23499663264363243531715271)
    ·
      refine ⟨35249494896544865297572907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23499663264363243531715271 35249494896544865297572907)
      ·
        refine ⟨52874242344817297946359361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35249494896544865297572907 52874242344817297946359361)
        ·
          refine ⟨39655681758612973459769521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52874242344817297946359361 39655681758612973459769521)
          ·
            refine ⟨29741761318959730094827141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39655681758612973459769521 29741761318959730094827141)
            ·
              refine ⟨5576580247304949392780089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29741761318959730094827141 5576580247304949392780089)
              ·
                refine ⟨4182435185478712044585067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5576580247304949392780089 4182435185478712044585067)
                ·
                  refine ⟨6273652778218068066877601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182435185478712044585067 6273652778218068066877601)
                  ·
                    refine ⟨4705239583663551050158201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273652778218068066877601 4705239583663551050158201)
                    ·
                      refine ⟨3528929687747663287618651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705239583663551050158201 3528929687747663287618651)
                      ·
                        rfl

theorem cell23_6872566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_6872566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872566 prefixEnd_6872566 := by exact prefixLift 6872566
  have htrace : WordTrace (prefixWord ++ tailWord_6872566) baseStart_6872566 baseEnd_6872566 := by
    simpa [prefixWord, tailWord_6872566, baseEnd_6872566] using wordTrace_append hprefix tailTrace_6872566
  have hstable : (prefixWord ++ tailWord_6872566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872566).length < 2 ^ (prefixWord ++ tailWord_6872566).sum := by decide
  have hdescent : baseEnd_6872566 < baseStart_6872566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872591 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_6872591 : Nat := 118140960795 + 6872591 * 2 ^ 59
def prefixEnd_6872591 : Nat := 4983230072969 + 3 ^ 40 * 6872591 * 2
def baseEnd_6872591 : Nat := 3528942524764025689806035

theorem tailTrace_6872591 : CollatzResearch.WordTrace tailWord_6872591 prefixEnd_6872591 3528942524764025689806035 := by
  unfold tailWord_6872591
  simp only [CollatzResearch.WordTrace]
  refine ⟨250663986644784026941289627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167109324429856017960859751 250663986644784026941289627)
  ·
    refine ⟨375995979967176040411934441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250663986644784026941289627 375995979967176040411934441)
    ·
      refine ⟨281996984975382030308950831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375995979967176040411934441 281996984975382030308950831)
      ·
        refine ⟨422995477463073045463426247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281996984975382030308950831 422995477463073045463426247)
        ·
          refine ⟨634493216194609568195139371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422995477463073045463426247 634493216194609568195139371)
          ·
            refine ⟨951739824291914352292709057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634493216194609568195139371 951739824291914352292709057)
            ·
              refine ⟨713804868218935764219531793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951739824291914352292709057 713804868218935764219531793)
              ·
                refine ⟨535353651164201823164648845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713804868218935764219531793 535353651164201823164648845)
                ·
                  refine ⟨200757619186575683686743317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535353651164201823164648845 200757619186575683686743317)
                  ·
                    refine ⟨9410513399370735172816093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 200757619186575683686743317 9410513399370735172816093)
                    ·
                      refine ⟨3528942524764025689806035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410513399370735172816093 3528942524764025689806035)
                      ·
                        rfl

theorem cell23_6872591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_6872591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872591 prefixEnd_6872591 := by exact prefixLift 6872591
  have htrace : WordTrace (prefixWord ++ tailWord_6872591) baseStart_6872591 baseEnd_6872591 := by
    simpa [prefixWord, tailWord_6872591, baseEnd_6872591] using wordTrace_append hprefix tailTrace_6872591
  have hstable : (prefixWord ++ tailWord_6872591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872591).length < 2 ^ (prefixWord ++ tailWord_6872591).sum := by decide
  have hdescent : baseEnd_6872591 < baseStart_6872591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872601 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_6872601 : Nat := 118140960795 + 6872601 * 2 ^ 59
def prefixEnd_6872601 : Nat := 4983230072969 + 3 ^ 40 * 6872601 * 2
def baseEnd_6872601 : Nat := 3528947659570570650680989

theorem tailTrace_6872601 : CollatzResearch.WordTrace tailWord_6872601 prefixEnd_6872601 3528947659570570650680989 := by
  unfold tailWord_6872601
  simp only [CollatzResearch.WordTrace]
  refine ⟨250664351374747798649153657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167109567583165199099435771 250664351374747798649153657)
  ·
    refine ⟨187998263531060848986865243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250664351374747798649153657 187998263531060848986865243)
    ·
      refine ⟨281997395296591273480297865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187998263531060848986865243 281997395296591273480297865)
      ·
        refine ⟨211498046472443455110223399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281997395296591273480297865 211498046472443455110223399)
        ·
          refine ⟨317247069708665182665335099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211498046472443455110223399 317247069708665182665335099)
          ·
            refine ⟨475870604562997773998002649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317247069708665182665335099 475870604562997773998002649)
            ·
              refine ⟨356902953422248330498501987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475870604562997773998002649 356902953422248330498501987)
              ·
                refine ⟨535354430133372495747752981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356902953422248330498501987 535354430133372495747752981)
                ·
                  refine ⟨25094738912501835738175921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 535354430133372495747752981 25094738912501835738175921)
                  ·
                    refine ⟨18821054184376376803631941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25094738912501835738175921 18821054184376376803631941)
                    ·
                      refine ⟨3528947659570570650680989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18821054184376376803631941 3528947659570570650680989)
                      ·
                        rfl

theorem cell23_6872601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_6872601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872601 prefixEnd_6872601 := by exact prefixLift 6872601
  have htrace : WordTrace (prefixWord ++ tailWord_6872601) baseStart_6872601 baseEnd_6872601 := by
    simpa [prefixWord, tailWord_6872601, baseEnd_6872601] using wordTrace_append hprefix tailTrace_6872601
  have hstable : (prefixWord ++ tailWord_6872601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872601).length < 2 ^ (prefixWord ++ tailWord_6872601).sum := by decide
  have hdescent : baseEnd_6872601 < baseStart_6872601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872605 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_6872605 : Nat := 118140960795 + 6872605 * 2 ^ 59
def prefixEnd_6872605 : Nat := 4983230072969 + 3 ^ 40 * 6872605 * 2
def baseEnd_6872605 : Nat := 3528949713493188635030971

theorem tailTrace_6872605 : CollatzResearch.WordTrace tailWord_6872605 prefixEnd_6872605 3528949713493188635030971 := by
  unfold tailWord_6872605
  simp only [CollatzResearch.WordTrace]
  refine ⟨250664497266733307332299269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167109664844488871554866179 250664497266733307332299269)
  ·
    refine ⟨46999593237512495124806113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250664497266733307332299269 46999593237512495124806113)
    ·
      refine ⟨35249694928134371343604585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46999593237512495124806113 35249694928134371343604585)
      ·
        refine ⟨26437271196100778507703439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35249694928134371343604585 26437271196100778507703439)
        ·
          refine ⟨39655906794151167761555159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26437271196100778507703439 39655906794151167761555159)
          ·
            refine ⟨59483860191226751642332739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39655906794151167761555159 59483860191226751642332739)
            ·
              refine ⟨89225790286840127463499109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59483860191226751642332739 89225790286840127463499109)
              ·
                refine ⟨16729835678782523899406083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89225790286840127463499109 16729835678782523899406083)
                ·
                  refine ⟨25094753518173785849109125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16729835678782523899406083 25094753518173785849109125)
                  ·
                    refine ⟨4705266284657584846707961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25094753518173785849109125 4705266284657584846707961)
                    ·
                      refine ⟨3528949713493188635030971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705266284657584846707961 3528949713493188635030971)
                      ·
                        rfl

theorem cell23_6872605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_6872605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872605 prefixEnd_6872605 := by exact prefixLift 6872605
  have htrace : WordTrace (prefixWord ++ tailWord_6872605) baseStart_6872605 baseEnd_6872605 := by
    simpa [prefixWord, tailWord_6872605, baseEnd_6872605] using wordTrace_append hprefix tailTrace_6872605
  have hstable : (prefixWord ++ tailWord_6872605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872605).length < 2 ^ (prefixWord ++ tailWord_6872605).sum := by decide
  have hdescent : baseEnd_6872605 < baseStart_6872605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872609 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6872609 : Nat := 118140960795 + 6872609 * 2 ^ 59
def prefixEnd_6872609 : Nat := 4983230072969 + 3 ^ 40 * 6872609 * 2
def baseEnd_6872609 : Nat := 3528951767415806619380953

theorem tailTrace_6872609 : CollatzResearch.WordTrace tailWord_6872609 prefixEnd_6872609 3528951767415806619380953 := by
  unfold tailWord_6872609
  simp only [CollatzResearch.WordTrace]
  refine ⟨250664643158718816015444881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167109762105812544010296587 250664643158718816015444881)
  ·
    refine ⟨187998482369039112011583661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250664643158718816015444881 187998482369039112011583661)
    ·
      refine ⟨70499430888389667004343873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187998482369039112011583661 70499430888389667004343873)
      ·
        refine ⟨52874573166292250253257905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70499430888389667004343873 52874573166292250253257905)
        ·
          refine ⟨39655929874719187689943429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52874573166292250253257905 39655929874719187689943429)
          ·
            refine ⟨7435486851509847691864393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39655929874719187689943429 7435486851509847691864393)
            ·
              refine ⟨5576615138632385768898295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7435486851509847691864393 5576615138632385768898295)
              ·
                refine ⟨8364922707948578653347443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576615138632385768898295 8364922707948578653347443)
                ·
                  refine ⟨12547384061922867980021165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364922707948578653347443 12547384061922867980021165)
                  ·
                    refine ⟨4705269023221075492507937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12547384061922867980021165 4705269023221075492507937)
                    ·
                      refine ⟨3528951767415806619380953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705269023221075492507937 3528951767415806619380953)
                      ·
                        rfl

theorem cell23_6872609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6872609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872609 prefixEnd_6872609 := by exact prefixLift 6872609
  have htrace : WordTrace (prefixWord ++ tailWord_6872609) baseStart_6872609 baseEnd_6872609 := by
    simpa [prefixWord, tailWord_6872609, baseEnd_6872609] using wordTrace_append hprefix tailTrace_6872609
  have hstable : (prefixWord ++ tailWord_6872609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872609).length < 2 ^ (prefixWord ++ tailWord_6872609).sum := by decide
  have hdescent : baseEnd_6872609 < baseStart_6872609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872616 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6872616 : Nat := 118140960795 + 6872616 * 2 ^ 59
def prefixEnd_6872616 : Nat := 4983230072969 + 3 ^ 40 * 6872616 * 2
def baseEnd_6872616 : Nat := 3528955361780388091993421

theorem tailTrace_6872616 : CollatzResearch.WordTrace tailWord_6872616 prefixEnd_6872616 3528955361780388091993421 := by
  unfold tailWord_6872616
  simp only [CollatzResearch.WordTrace]
  refine ⟨125332449234846728105474851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167109932313128970807299801 125332449234846728105474851)
  ·
    refine ⟨187998673852270092158212277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125332449234846728105474851 187998673852270092158212277)
    ·
      refine ⟨17624875673650321139832401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187998673852270092158212277 17624875673650321139832401)
      ·
        refine ⟨13218656755237740854874301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17624875673650321139832401 13218656755237740854874301)
        ·
          refine ⟨4956996283214152820577863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13218656755237740854874301 4956996283214152820577863)
          ·
            refine ⟨7435494424821229230866795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956996283214152820577863 7435494424821229230866795)
            ·
              refine ⟨11153241637231843846300193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435494424821229230866795 11153241637231843846300193)
              ·
                refine ⟨8364931227923882884725145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11153241637231843846300193 8364931227923882884725145)
                ·
                  refine ⟨6273698420942912163543859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364931227923882884725145 6273698420942912163543859)
                  ·
                    refine ⟨9410547631414368245315789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273698420942912163543859 9410547631414368245315789)
                    ·
                      refine ⟨3528955361780388091993421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410547631414368245315789 3528955361780388091993421)
                      ·
                        rfl

theorem cell23_6872616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6872616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872616 prefixEnd_6872616 := by exact prefixLift 6872616
  have htrace : WordTrace (prefixWord ++ tailWord_6872616) baseStart_6872616 baseEnd_6872616 := by
    simpa [prefixWord, tailWord_6872616, baseEnd_6872616] using wordTrace_append hprefix tailTrace_6872616
  have hstable : (prefixWord ++ tailWord_6872616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872616).length < 2 ^ (prefixWord ++ tailWord_6872616).sum := by decide
  have hdescent : baseEnd_6872616 < baseStart_6872616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872618 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6872618 : Nat := 118140960795 + 6872618 * 2 ^ 59
def prefixEnd_6872618 : Nat := 4983230072969 + 3 ^ 40 * 6872618 * 2
def baseEnd_6872618 : Nat := 3528956388741697084168411

theorem tailTrace_6872618 : CollatzResearch.WordTrace tailWord_6872618 prefixEnd_6872618 3528956388741697084168411 := by
  unfold tailWord_6872618
  simp only [CollatzResearch.WordTrace]
  refine ⟨62666242853921552638130627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167109980943790807035015005 62666242853921552638130627)
  ·
    refine ⟨93999364280882328957195941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62666242853921552638130627 93999364280882328957195941)
    ·
      refine ⟨17624880802665436679474239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93999364280882328957195941 17624880802665436679474239)
      ·
        refine ⟨26437321203998155019211359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17624880802665436679474239 26437321203998155019211359)
        ·
          refine ⟨39655981805997232528817039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26437321203998155019211359 39655981805997232528817039)
          ·
            refine ⟨59483972708995848793225559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39655981805997232528817039 59483972708995848793225559)
            ·
              refine ⟨89225959063493773189838339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59483972708995848793225559 89225959063493773189838339)
              ·
                refine ⟨133838938595240659784757509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89225959063493773189838339 133838938595240659784757509)
                ·
                  refine ⟨25094800986607623709642033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133838938595240659784757509 25094800986607623709642033)
                  ·
                    refine ⟨18821100739955717782231525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25094800986607623709642033 18821100739955717782231525)
                    ·
                      refine ⟨3528956388741697084168411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18821100739955717782231525 3528956388741697084168411)
                      ·
                        rfl

theorem cell23_6872618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6872618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872618 prefixEnd_6872618 := by exact prefixLift 6872618
  have htrace : WordTrace (prefixWord ++ tailWord_6872618) baseStart_6872618 baseEnd_6872618 := by
    simpa [prefixWord, tailWord_6872618, baseEnd_6872618] using wordTrace_append hprefix tailTrace_6872618
  have hstable : (prefixWord ++ tailWord_6872618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872618).length < 2 ^ (prefixWord ++ tailWord_6872618).sum := by decide
  have hdescent : baseEnd_6872618 < baseStart_6872618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872639 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 2, 2, 2]
def baseStart_6872639 : Nat := 118140960795 + 6872639 * 2 ^ 59
def prefixEnd_6872639 : Nat := 4983230072969 + 3 ^ 40 * 6872639 * 2
def baseEnd_6872639 : Nat := 3528967171835441502005815

theorem tailTrace_6872639 : CollatzResearch.WordTrace tailWord_6872639 prefixEnd_6872639 3528967171835441502005815 := by
  unfold tailWord_6872639
  simp only [CollatzResearch.WordTrace]
  refine ⟨250665737348610131139036971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167110491565740087426024647 250665737348610131139036971)
  ·
    refine ⟨375998606022915196708555457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250665737348610131139036971 375998606022915196708555457)
    ·
      refine ⟨281998954517186397531416593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375998606022915196708555457 281998954517186397531416593)
      ·
        refine ⟨211499215887889798148562445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281998954517186397531416593 211499215887889798148562445)
        ·
          refine ⟨79312205957958674305710917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211499215887889798148562445 79312205957958674305710917)
          ·
            refine ⟨14871038617117251432320797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79312205957958674305710917 14871038617117251432320797)
            ·
              refine ⟨5576639481418969287120299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14871038617117251432320797 5576639481418969287120299)
              ·
                refine ⟨8364959222128453930680449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576639481418969287120299 8364959222128453930680449)
                ·
                  refine ⟨6273719416596340448010337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364959222128453930680449 6273719416596340448010337)
                  ·
                    refine ⟨4705289562447255336007753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273719416596340448010337 4705289562447255336007753)
                    ·
                      refine ⟨3528967171835441502005815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705289562447255336007753 3528967171835441502005815)
                      ·
                        rfl

theorem cell23_6872639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_6872639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872639 prefixEnd_6872639 := by exact prefixLift 6872639
  have htrace : WordTrace (prefixWord ++ tailWord_6872639) baseStart_6872639 baseEnd_6872639 := by
    simpa [prefixWord, tailWord_6872639, baseEnd_6872639] using wordTrace_append hprefix tailTrace_6872639
  have hstable : (prefixWord ++ tailWord_6872639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872639).length < 2 ^ (prefixWord ++ tailWord_6872639).sum := by decide
  have hdescent : baseEnd_6872639 < baseStart_6872639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872651 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_6872651 : Nat := 118140960795 + 6872651 * 2 ^ 59
def prefixEnd_6872651 : Nat := 4983230072969 + 3 ^ 40 * 6872651 * 2
def baseEnd_6872651 : Nat := 3528973333603295455055759

theorem tailTrace_6872651 : CollatzResearch.WordTrace tailWord_6872651 prefixEnd_6872651 3528973333603295455055759 := by
  unfold tailWord_6872651
  simp only [CollatzResearch.WordTrace]
  refine ⟨250666175024566657188473807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167110783349711104792315871 250666175024566657188473807)
  ·
    refine ⟨375999262536849985782710711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250666175024566657188473807 375999262536849985782710711)
    ·
      refine ⟨563998893805274978674066067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375999262536849985782710711 563998893805274978674066067)
      ·
        refine ⟨845998340707912468011099101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563998893805274978674066067 845998340707912468011099101)
        ·
          refine ⟨317249377765467175504162163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 845998340707912468011099101 317249377765467175504162163)
          ·
            refine ⟨475874066648200763256243245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317249377765467175504162163 475874066648200763256243245)
            ·
              refine ⟨178452774993075286221091217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475874066648200763256243245 178452774993075286221091217)
              ·
                refine ⟨133839581244806464665818413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178452774993075286221091217 133839581244806464665818413)
                ·
                  refine ⟨50189842966802424249681905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133839581244806464665818413 50189842966802424249681905)
                  ·
                    refine ⟨37642382225101818187261429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50189842966802424249681905 37642382225101818187261429)
                    ·
                      refine ⟨3528973333603295455055759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37642382225101818187261429 3528973333603295455055759)
                      ·
                        rfl

theorem cell23_6872651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_6872651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872651 prefixEnd_6872651 := by exact prefixLift 6872651
  have htrace : WordTrace (prefixWord ++ tailWord_6872651) baseStart_6872651 baseEnd_6872651 := by
    simpa [prefixWord, tailWord_6872651, baseEnd_6872651] using wordTrace_append hprefix tailTrace_6872651
  have hstable : (prefixWord ++ tailWord_6872651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872651).length < 2 ^ (prefixWord ++ tailWord_6872651).sum := by decide
  have hdescent : baseEnd_6872651 < baseStart_6872651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872658 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_6872658 : Nat := 118140960795 + 6872658 * 2 ^ 59
def prefixEnd_6872658 : Nat := 4983230072969 + 3 ^ 40 * 6872658 * 2
def baseEnd_6872658 : Nat := 1176325642655958975889409

theorem tailTrace_6872658 : CollatzResearch.WordTrace tailWord_6872658 prefixEnd_6872658 1176325642655958975889409 := by
  unfold tailWord_6872658
  simp only [CollatzResearch.WordTrace]
  refine ⟨62666607583885324345994657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167110953557027531589319085 62666607583885324345994657)
  ·
    refine ⟨46999955687913993259495993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62666607583885324345994657 46999955687913993259495993)
    ·
      refine ⟨35249966765935494944621995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46999955687913993259495993 35249966765935494944621995)
      ·
        refine ⟨52874950148903242416932993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35249966765935494944621995 52874950148903242416932993)
        ·
          refine ⟨39656212611677431812699745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52874950148903242416932993 39656212611677431812699745)
          ·
            refine ⟨29742159458758073859524809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39656212611677431812699745 29742159458758073859524809)
            ·
              refine ⟨22306619594068555394643607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29742159458758073859524809 22306619594068555394643607)
              ·
                refine ⟨33459929391102833091965411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22306619594068555394643607 33459929391102833091965411)
                ·
                  refine ⟨50189894086654249637948117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33459929391102833091965411 50189894086654249637948117)
                  ·
                    refine ⟨1176325642655958975889409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50189894086654249637948117 1176325642655958975889409)
                    ·
                      rfl

theorem cell23_6872658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_6872658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872658 prefixEnd_6872658 := by exact prefixLift 6872658
  have htrace : WordTrace (prefixWord ++ tailWord_6872658) baseStart_6872658 baseEnd_6872658 := by
    simpa [prefixWord, tailWord_6872658, baseEnd_6872658] using wordTrace_append hprefix tailTrace_6872658
  have hstable : (prefixWord ++ tailWord_6872658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872658).length < 2 ^ (prefixWord ++ tailWord_6872658).sum := by decide
  have hdescent : baseEnd_6872658 < baseStart_6872658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872685 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_6872685 : Nat := 118140960795 + 6872685 * 2 ^ 59
def prefixEnd_6872685 : Nat := 4983230072969 + 3 ^ 40 * 6872685 * 2
def baseEnd_6872685 : Nat := 3528990791945548322030603

theorem tailTrace_6872685 : CollatzResearch.WordTrace tailWord_6872685 prefixEnd_6872685 3528990791945548322030603 := by
  unfold tailWord_6872685
  simp only [CollatzResearch.WordTrace]
  refine ⟨250667415106443480995211509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167111610070962320663474339 250667415106443480995211509)
  ·
    refine ⟨23500070166229076343301079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250667415106443480995211509 23500070166229076343301079)
    ·
      refine ⟨35250105249343614514951619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23500070166229076343301079 35250105249343614514951619)
      ·
        refine ⟨52875157874015421772427429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35250105249343614514951619 52875157874015421772427429)
        ·
          refine ⟨9914092101377891582330143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52875157874015421772427429 9914092101377891582330143)
          ·
            refine ⟨14871138152066837373495215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914092101377891582330143 14871138152066837373495215)
            ·
              refine ⟨22306707228100256060242823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871138152066837373495215 22306707228100256060242823)
              ·
                refine ⟨33460060842150384090364235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22306707228100256060242823 33460060842150384090364235)
                ·
                  refine ⟨50190091263225576135546353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33460060842150384090364235 50190091263225576135546353)
                  ·
                    refine ⟨37642568447419182101659765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50190091263225576135546353 37642568447419182101659765)
                    ·
                      refine ⟨3528990791945548322030603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37642568447419182101659765 3528990791945548322030603)
                      ·
                        rfl

theorem cell23_6872685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_6872685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872685 prefixEnd_6872685 := by exact prefixLift 6872685
  have htrace : WordTrace (prefixWord ++ tailWord_6872685) baseStart_6872685 baseEnd_6872685 := by
    simpa [prefixWord, tailWord_6872685, baseEnd_6872685] using wordTrace_append hprefix tailTrace_6872685
  have hstable : (prefixWord ++ tailWord_6872685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872685).length < 2 ^ (prefixWord ++ tailWord_6872685).sum := by decide
  have hdescent : baseEnd_6872685 < baseStart_6872685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872691 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_6872691 : Nat := 118140960795 + 6872691 * 2 ^ 59
def prefixEnd_6872691 : Nat := 4983230072969 + 3 ^ 40 * 6872691 * 2
def baseEnd_6872691 : Nat := 3528993872829475298555575

theorem tailTrace_6872691 : CollatzResearch.WordTrace tailWord_6872691 prefixEnd_6872691 3528993872829475298555575 := by
  unfold tailWord_6872691
  simp only [CollatzResearch.WordTrace]
  refine ⟨250667633944421744019929927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167111755962947829346619951 250667633944421744019929927)
  ·
    refine ⟨376001450916632616029894891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250667633944421744019929927 376001450916632616029894891)
    ·
      refine ⟨564002176374948924044842337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376001450916632616029894891 564002176374948924044842337)
      ·
        refine ⟨423001632281211693033631753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564002176374948924044842337 423001632281211693033631753)
        ·
          refine ⟨317251224210908769775223815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423001632281211693033631753 317251224210908769775223815)
          ·
            refine ⟨475876836316363154662835723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317251224210908769775223815 475876836316363154662835723)
            ·
              refine ⟨713815254474544731994253585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475876836316363154662835723 713815254474544731994253585)
              ·
                refine ⟨535361440855908548995690189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713815254474544731994253585 535361440855908548995690189)
                ·
                  refine ⟨200760540320965705873383821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535361440855908548995690189 200760540320965705873383821)
                  ·
                    refine ⟨75285202620362139702518933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200760540320965705873383821 75285202620362139702518933)
                    ·
                      refine ⟨3528993872829475298555575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75285202620362139702518933 3528993872829475298555575)
                      ·
                        rfl

theorem cell23_6872691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_6872691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872691 prefixEnd_6872691 := by exact prefixLift 6872691
  have htrace : WordTrace (prefixWord ++ tailWord_6872691) baseStart_6872691 baseEnd_6872691 := by
    simpa [prefixWord, tailWord_6872691, baseEnd_6872691] using wordTrace_append hprefix tailTrace_6872691
  have hstable : (prefixWord ++ tailWord_6872691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872691).length < 2 ^ (prefixWord ++ tailWord_6872691).sum := by decide
  have hdescent : baseEnd_6872691 < baseStart_6872691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872698 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_6872698 : Nat := 118140960795 + 6872698 * 2 ^ 59
def prefixEnd_6872698 : Nat := 4983230072969 + 3 ^ 40 * 6872698 * 2
def baseEnd_6872698 : Nat := 3528997467194056771168043

theorem tailTrace_6872698 : CollatzResearch.WordTrace tailWord_6872698 prefixEnd_6872698 3528997467194056771168043 := by
  unfold tailWord_6872698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62666972313849096053858687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167111926170264256143623165 62666972313849096053858687)
  ·
    refine ⟨94000458470773644080788031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62666972313849096053858687 94000458470773644080788031)
    ·
      refine ⟨141000687706160466121182047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94000458470773644080788031 141000687706160466121182047)
      ·
        refine ⟨211501031559240699181773071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141000687706160466121182047 211501031559240699181773071)
        ·
          refine ⟨317251547338861048772659607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211501031559240699181773071 317251547338861048772659607)
          ·
            refine ⟨475877321008291573158989411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317251547338861048772659607 475877321008291573158989411)
            ·
              refine ⟨713815981512437359738484117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475877321008291573158989411 713815981512437359738484117)
              ·
                refine ⟨33460124133395501237741443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 713815981512437359738484117 33460124133395501237741443)
                ·
                  refine ⟨50190186200093251856612165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33460124133395501237741443 50190186200093251856612165)
                  ·
                    refine ⟨9410659912517484723114781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50190186200093251856612165 9410659912517484723114781)
                    ·
                      refine ⟨3528997467194056771168043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410659912517484723114781 3528997467194056771168043)
                      ·
                        rfl

theorem cell23_6872698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_6872698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872698 prefixEnd_6872698 := by exact prefixLift 6872698
  have htrace : WordTrace (prefixWord ++ tailWord_6872698) baseStart_6872698 baseEnd_6872698 := by
    simpa [prefixWord, tailWord_6872698, baseEnd_6872698] using wordTrace_append hprefix tailTrace_6872698
  have hstable : (prefixWord ++ tailWord_6872698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872698).length < 2 ^ (prefixWord ++ tailWord_6872698).sum := by decide
  have hdescent : baseEnd_6872698 < baseStart_6872698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872715 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 3]
def baseStart_6872715 : Nat := 118140960795 + 6872715 * 2 ^ 59
def prefixEnd_6872715 : Nat := 4983230072969 + 3 ^ 40 * 6872715 * 2
def baseEnd_6872715 : Nat := 3529006196365183204655465

theorem tailTrace_6872715 : CollatzResearch.WordTrace tailWord_6872715 prefixEnd_6872715 3529006196365183204655465 := by
  unfold tailWord_6872715
  simp only [CollatzResearch.WordTrace]
  refine ⟨250668509296334796118803599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167112339530889864079202399 250668509296334796118803599)
  ·
    refine ⟨376002763944502194178205399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250668509296334796118803599 376002763944502194178205399)
    ·
      refine ⟨564004145916753291267308099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376002763944502194178205399 564004145916753291267308099)
      ·
        refine ⟨846006218875129936900962149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564004145916753291267308099 846006218875129936900962149)
        ·
          refine ⟨158626166039086863168930403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 846006218875129936900962149 158626166039086863168930403)
          ·
            refine ⟨237939249058630294753395605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158626166039086863168930403 237939249058630294753395605)
            ·
              refine ⟨11153402299623295066565419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237939249058630294753395605 11153402299623295066565419)
              ·
                refine ⟨16730103449434942599848129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153402299623295066565419 16730103449434942599848129)
                ·
                  refine ⟨12547577587076206949886097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16730103449434942599848129 12547577587076206949886097)
                  ·
                    refine ⟨9410683190307155212414573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12547577587076206949886097 9410683190307155212414573)
                    ·
                      refine ⟨3529006196365183204655465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410683190307155212414573 3529006196365183204655465)
                      ·
                        rfl

theorem cell23_6872715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 3].length) (baseStart_6872715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872715 prefixEnd_6872715 := by exact prefixLift 6872715
  have htrace : WordTrace (prefixWord ++ tailWord_6872715) baseStart_6872715 baseEnd_6872715 := by
    simpa [prefixWord, tailWord_6872715, baseEnd_6872715] using wordTrace_append hprefix tailTrace_6872715
  have hstable : (prefixWord ++ tailWord_6872715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872715).length < 2 ^ (prefixWord ++ tailWord_6872715).sum := by decide
  have hdescent : baseEnd_6872715 < baseStart_6872715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872755 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 1, 5, 2]
def baseStart_6872755 : Nat := 118140960795 + 6872755 * 2 ^ 59
def prefixEnd_6872755 : Nat := 4983230072969 + 3 ^ 40 * 6872755 * 2
def baseEnd_6872755 : Nat := 3529026735591363048155281

theorem tailTrace_6872755 : CollatzResearch.WordTrace tailWord_6872755 prefixEnd_6872755 3529026735591363048155281 := by
  unfold tailWord_6872755
  simp only [CollatzResearch.WordTrace]
  refine ⟨250669968216189882950259719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167113312144126588633506479 250669968216189882950259719)
  ·
    refine ⟨376004952324284824425389579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250669968216189882950259719 376004952324284824425389579)
    ·
      refine ⟨564007428486427236638084369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376004952324284824425389579 564007428486427236638084369)
      ·
        refine ⟨423005571364820427478563277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564007428486427236638084369 423005571364820427478563277)
        ·
          refine ⟨158627089261807660304461229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423005571364820427478563277 158627089261807660304461229)
          ·
            refine ⟨59485158473177872614172961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158627089261807660304461229 59485158473177872614172961)
            ·
              refine ⟨44613868854883404460629721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59485158473177872614172961 44613868854883404460629721)
              ·
                refine ⟨33460401641162553345472291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44613868854883404460629721 33460401641162553345472291)
                ·
                  refine ⟨50190602461743830018208437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33460401641162553345472291 50190602461743830018208437)
                  ·
                    refine ⟨4705368980788484064207041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50190602461743830018208437 4705368980788484064207041)
                    ·
                      refine ⟨3529026735591363048155281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705368980788484064207041 3529026735591363048155281)
                      ·
                        rfl

theorem cell23_6872755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5, 2].length) (baseStart_6872755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872755 prefixEnd_6872755 := by exact prefixLift 6872755
  have htrace : WordTrace (prefixWord ++ tailWord_6872755) baseStart_6872755 baseEnd_6872755 := by
    simpa [prefixWord, tailWord_6872755, baseEnd_6872755] using wordTrace_append hprefix tailTrace_6872755
  have hstable : (prefixWord ++ tailWord_6872755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872755).length < 2 ^ (prefixWord ++ tailWord_6872755).sum := by decide
  have hdescent : baseEnd_6872755 < baseStart_6872755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872762 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_6872762 : Nat := 118140960795 + 6872762 * 2 ^ 59
def prefixEnd_6872762 : Nat := 4983230072969 + 3 ^ 40 * 6872762 * 2
def baseEnd_6872762 : Nat := 3529030329955944520767749

theorem tailTrace_6872762 : CollatzResearch.WordTrace tailWord_6872762 prefixEnd_6872762 3529030329955944520767749 := by
  unfold tailWord_6872762
  simp only [CollatzResearch.WordTrace]
  refine ⟨62667555881791130786441135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167113482351443015430509693 62667555881791130786441135)
  ·
    refine ⟨94001333822686696179661703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62667555881791130786441135 94001333822686696179661703)
    ·
      refine ⟨141002000734030044269492555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94001333822686696179661703 141002000734030044269492555)
      ·
        refine ⟨211503001101045066404238833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141002000734030044269492555 211503001101045066404238833)
        ·
          refine ⟨158627250825783799803179125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211503001101045066404238833 158627250825783799803179125)
          ·
            refine ⟨14871304764917231231548043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158627250825783799803179125 14871304764917231231548043)
            ·
              refine ⟨22306957147375846847322065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871304764917231231548043 22306957147375846847322065)
              ·
                refine ⟨16730217860531885135491549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22306957147375846847322065 16730217860531885135491549)
                ·
                  refine ⟨6273831697699456925809331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16730217860531885135491549 6273831697699456925809331)
                  ·
                    refine ⟨9410747546549185388713997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273831697699456925809331 9410747546549185388713997)
                    ·
                      refine ⟨3529030329955944520767749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410747546549185388713997 3529030329955944520767749)
                      ·
                        rfl

theorem cell23_6872762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_6872762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872762 prefixEnd_6872762 := by exact prefixLift 6872762
  have htrace : WordTrace (prefixWord ++ tailWord_6872762) baseStart_6872762 baseEnd_6872762 := by
    simpa [prefixWord, tailWord_6872762, baseEnd_6872762] using wordTrace_append hprefix tailTrace_6872762
  have hstable : (prefixWord ++ tailWord_6872762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872762).length < 2 ^ (prefixWord ++ tailWord_6872762).sum := by decide
  have hdescent : baseEnd_6872762 < baseStart_6872762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872765 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_6872765 : Nat := 118140960795 + 6872765 * 2 ^ 59
def prefixEnd_6872765 : Nat := 4983230072969 + 3 ^ 40 * 6872765 * 2
def baseEnd_6872765 : Nat := 1176343956799302669676745

theorem tailTrace_6872765 : CollatzResearch.WordTrace tailWord_6872765 prefixEnd_6872765 1176343956799302669676745 := by
  unfold tailWord_6872765
  simp only [CollatzResearch.WordTrace]
  refine ⟨250670332946153654658123749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167113555297435769772082499 250670332946153654658123749)
  ·
    refine ⟨47000687427403810248398203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250670332946153654658123749 47000687427403810248398203)
    ·
      refine ⟨70501031141105715372597305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47000687427403810248398203 70501031141105715372597305)
      ·
        refine ⟨52875773355829286529447979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70501031141105715372597305 52875773355829286529447979)
        ·
          refine ⟨79313660033743929794171969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52875773355829286529447979 79313660033743929794171969)
          ·
            refine ⟨59485245025307947345628977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79313660033743929794171969 59485245025307947345628977)
            ·
              refine ⟨44613933768980960509221733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59485245025307947345628977 44613933768980960509221733)
              ·
                refine ⟨8365112581683930095479075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44613933768980960509221733 8365112581683930095479075)
                ·
                  refine ⟨12547668872525895143218613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8365112581683930095479075 12547668872525895143218613)
                  ·
                    refine ⟨1176343956799302669676745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12547668872525895143218613 1176343956799302669676745)
                    ·
                      rfl

theorem cell23_6872765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_6872765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872765 prefixEnd_6872765 := by exact prefixLift 6872765
  have htrace : WordTrace (prefixWord ++ tailWord_6872765) baseStart_6872765 baseEnd_6872765 := by
    simpa [prefixWord, tailWord_6872765, baseEnd_6872765] using wordTrace_append hprefix tailTrace_6872765
  have hstable : (prefixWord ++ tailWord_6872765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872765).length < 2 ^ (prefixWord ++ tailWord_6872765).sum := by decide
  have hdescent : baseEnd_6872765 < baseStart_6872765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872772 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_6872772 : Nat := 118140960795 + 6872772 * 2 ^ 59
def prefixEnd_6872772 : Nat := 4983230072969 + 3 ^ 40 * 6872772 * 2
def baseEnd_6872772 : Nat := 3529035464762489481642703

theorem tailTrace_6872772 : CollatzResearch.WordTrace tailWord_6872772 prefixEnd_6872772 3529035464762489481642703 := by
  unfold tailWord_6872772
  simp only [CollatzResearch.WordTrace]
  refine ⟨125335294128564147426814285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167113725504752196569085713 125335294128564147426814285)
  ·
    refine ⟨47000735298211555285055357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125335294128564147426814285 47000735298211555285055357)
    ·
      refine ⟨17625275736829333231895759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47000735298211555285055357 17625275736829333231895759)
      ·
        refine ⟨26437913605243999847843639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625275736829333231895759 26437913605243999847843639)
        ·
          refine ⟨39656870407865999771765459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26437913605243999847843639 39656870407865999771765459)
          ·
            refine ⟨59485305611798999657648189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39656870407865999771765459 59485305611798999657648189)
            ·
              refine ⟨22306989604424624871618071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59485305611798999657648189 22306989604424624871618071)
              ·
                refine ⟨33460484406636937307427107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22306989604424624871618071 33460484406636937307427107)
                ·
                  refine ⟨50190726609955405961140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33460484406636937307427107 50190726609955405961140661)
                  ·
                    refine ⟨4705380619683319308856937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50190726609955405961140661 4705380619683319308856937)
                    ·
                      refine ⟨3529035464762489481642703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705380619683319308856937 3529035464762489481642703)
                      ·
                        rfl

theorem cell23_6872772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_6872772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872772 prefixEnd_6872772 := by exact prefixLift 6872772
  have htrace : WordTrace (prefixWord ++ tailWord_6872772) baseStart_6872772 baseEnd_6872772 := by
    simpa [prefixWord, tailWord_6872772, baseEnd_6872772] using wordTrace_append hprefix tailTrace_6872772
  have hstable : (prefixWord ++ tailWord_6872772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872772).length < 2 ^ (prefixWord ++ tailWord_6872772).sum := by decide
  have hdescent : baseEnd_6872772 < baseStart_6872772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872796 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6872796 : Nat := 118140960795 + 6872796 * 2 ^ 59
def prefixEnd_6872796 : Nat := 4983230072969 + 3 ^ 40 * 6872796 * 2
def baseEnd_6872796 : Nat := 3529047788298197387742593

theorem tailTrace_6872796 : CollatzResearch.WordTrace tailWord_6872796 prefixEnd_6872796 3529047788298197387742593 := by
  unfold tailWord_6872796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125335731804520673476251121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167114309072694231301668161 125335731804520673476251121)
  ·
    refine ⟨94001798853390505107188341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125335731804520673476251121 94001798853390505107188341)
    ·
      refine ⟨8812668642505359853798907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94001798853390505107188341 8812668642505359853798907)
      ·
        refine ⟨13219002963758039780698361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812668642505359853798907 13219002963758039780698361)
        ·
          refine ⟨9914252222818529835523771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13219002963758039780698361 9914252222818529835523771)
          ·
            refine ⟨14871378334227794753285657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914252222818529835523771 14871378334227794753285657)
            ·
              refine ⟨11153533750670846064964243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14871378334227794753285657 11153533750670846064964243)
              ·
                refine ⟨16730300626006269097446365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153533750670846064964243 16730300626006269097446365)
                ·
                  refine ⟨6273862734752350911542387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16730300626006269097446365 6273862734752350911542387)
                  ·
                    refine ⟨9410794102128526367313581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273862734752350911542387 9410794102128526367313581)
                    ·
                      refine ⟨3529047788298197387742593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410794102128526367313581 3529047788298197387742593)
                      ·
                        rfl

theorem cell23_6872796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6872796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872796 prefixEnd_6872796 := by exact prefixLift 6872796
  have htrace : WordTrace (prefixWord ++ tailWord_6872796) baseStart_6872796 baseEnd_6872796 := by
    simpa [prefixWord, tailWord_6872796, baseEnd_6872796] using wordTrace_append hprefix tailTrace_6872796
  have hstable : (prefixWord ++ tailWord_6872796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872796).length < 2 ^ (prefixWord ++ tailWord_6872796).sum := by decide
  have hdescent : baseEnd_6872796 < baseStart_6872796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872805 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6872805 : Nat := 118140960795 + 6872805 * 2 ^ 59
def prefixEnd_6872805 : Nat := 4983230072969 + 3 ^ 40 * 6872805 * 2
def baseEnd_6872805 : Nat := 3529052409624087852530051

theorem tailTrace_6872805 : CollatzResearch.WordTrace tailWord_6872805 prefixEnd_6872805 3529052409624087852530051 := by
  unfold tailWord_6872805
  simp only [CollatzResearch.WordTrace]
  refine ⟨250671791866008741489579869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167114527910672494326386579 250671791866008741489579869)
  ·
    refine ⟨94001921949753278058592451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250671791866008741489579869 94001921949753278058592451)
    ·
      refine ⟨141002882924629917087888677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94001921949753278058592451 141002882924629917087888677)
      ·
        refine ⟨26438040548368109453979127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141002882924629917087888677 26438040548368109453979127)
        ·
          refine ⟨39657060822552164180968691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26438040548368109453979127 39657060822552164180968691)
          ·
            refine ⟨59485591233828246271453037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39657060822552164180968691 59485591233828246271453037)
            ·
              refine ⟨22307096712685592351794889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59485591233828246271453037 22307096712685592351794889)
              ·
                refine ⟨16730322534514194263846167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22307096712685592351794889 16730322534514194263846167)
                ·
                  refine ⟨25095483801771291395769251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16730322534514194263846167 25095483801771291395769251)
                  ·
                    refine ⟨37643225702656937093653877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25095483801771291395769251 37643225702656937093653877)
                    ·
                      refine ⟨3529052409624087852530051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37643225702656937093653877 3529052409624087852530051)
                      ·
                        rfl

theorem cell23_6872805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6872805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872805 prefixEnd_6872805 := by exact prefixLift 6872805
  have htrace : WordTrace (prefixWord ++ tailWord_6872805) baseStart_6872805 baseEnd_6872805 := by
    simpa [prefixWord, tailWord_6872805, baseEnd_6872805] using wordTrace_append hprefix tailTrace_6872805
  have hstable : (prefixWord ++ tailWord_6872805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872805).length < 2 ^ (prefixWord ++ tailWord_6872805).sum := by decide
  have hdescent : baseEnd_6872805 < baseStart_6872805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872830 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6872830 : Nat := 118140960795 + 6872830 * 2 ^ 59
def prefixEnd_6872830 : Nat := 4983230072969 + 3 ^ 40 * 6872830 * 2
def baseEnd_6872830 : Nat := 3529065246640450254717437

theorem tailTrace_6872830 : CollatzResearch.WordTrace tailWord_6872830 prefixEnd_6872830 3529065246640450254717437 := by
  unfold tailWord_6872830
  simp only [CollatzResearch.WordTrace]
  refine ⟨31334087961364771344904993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167115135793945447172826629 31334087961364771344904993)
  ·
    refine ⟨23500565971023578508678745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31334087961364771344904993 23500565971023578508678745)
    ·
      refine ⟨17625424478267683881509059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23500565971023578508678745 17625424478267683881509059)
      ·
        refine ⟨26438136717401525822263589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625424478267683881509059 26438136717401525822263589)
        ·
          refine ⟨4957150634512786091674423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26438136717401525822263589 4957150634512786091674423)
          ·
            refine ⟨7435725951769179137511635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957150634512786091674423 7435725951769179137511635)
            ·
              refine ⟨11153588927653768706267453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435725951769179137511635 11153588927653768706267453)
              ·
                refine ⟨4182595847870163264850295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11153588927653768706267453 4182595847870163264850295)
                ·
                  refine ⟨6273893771805244897275443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182595847870163264850295 6273893771805244897275443)
                  ·
                    refine ⟨9410840657707867345913165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273893771805244897275443 9410840657707867345913165)
                    ·
                      refine ⟨3529065246640450254717437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410840657707867345913165 3529065246640450254717437)
                      ·
                        rfl

theorem cell23_6872830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6872830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872830 prefixEnd_6872830 := by exact prefixLift 6872830
  have htrace : WordTrace (prefixWord ++ tailWord_6872830) baseStart_6872830 baseEnd_6872830 := by
    simpa [prefixWord, tailWord_6872830, baseEnd_6872830] using wordTrace_append hprefix tailTrace_6872830
  have hstable : (prefixWord ++ tailWord_6872830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872830).length < 2 ^ (prefixWord ++ tailWord_6872830).sum := by decide
  have hdescent : baseEnd_6872830 < baseStart_6872830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872835 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 3]
def baseStart_6872835 : Nat := 118140960795 + 6872835 * 2 ^ 59
def prefixEnd_6872835 : Nat := 4983230072969 + 3 ^ 40 * 6872835 * 2
def baseEnd_6872835 : Nat := 3529067814043722735154913

theorem tailTrace_6872835 : CollatzResearch.WordTrace tailWord_6872835 prefixEnd_6872835 3529067814043722735154913 := by
  unfold tailWord_6872835
  simp only [CollatzResearch.WordTrace]
  refine ⟨250672886055900056613171959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167115257370600037742114639 250672886055900056613171959)
  ·
    refine ⟨376009329083850084919757939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250672886055900056613171959 376009329083850084919757939)
    ·
      refine ⟨564013993625775127379636909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376009329083850084919757939 564013993625775127379636909)
      ·
        refine ⟨211505247609665672767363841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564013993625775127379636909 211505247609665672767363841)
        ·
          refine ⟨158628935707249254575522881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211505247609665672767363841 158628935707249254575522881)
          ·
            refine ⟨118971701780436940931642161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158628935707249254575522881 118971701780436940931642161)
            ·
              refine ⟨89228776335327705698731621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118971701780436940931642161 89228776335327705698731621)
              ·
                refine ⟨16730395562873944818512179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89228776335327705698731621 16730395562873944818512179)
                ·
                  refine ⟨25095593344310917227768269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16730395562873944818512179 25095593344310917227768269)
                  ·
                    refine ⟨9410847504116593960413101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25095593344310917227768269 9410847504116593960413101)
                    ·
                      refine ⟨3529067814043722735154913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410847504116593960413101 3529067814043722735154913)
                      ·
                        rfl

theorem cell23_6872835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_6872835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872835 prefixEnd_6872835 := by exact prefixLift 6872835
  have htrace : WordTrace (prefixWord ++ tailWord_6872835) baseStart_6872835 baseEnd_6872835 := by
    simpa [prefixWord, tailWord_6872835, baseEnd_6872835] using wordTrace_append hprefix tailTrace_6872835
  have hstable : (prefixWord ++ tailWord_6872835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872835).length < 2 ^ (prefixWord ++ tailWord_6872835).sum := by decide
  have hdescent : baseEnd_6872835 < baseStart_6872835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872853 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_6872853 : Nat := 118140960795 + 6872853 * 2 ^ 59
def prefixEnd_6872853 : Nat := 4983230072969 + 3 ^ 40 * 6872853 * 2
def baseEnd_6872853 : Nat := 3529077056695503664729831

theorem tailTrace_6872853 : CollatzResearch.WordTrace tailWord_6872853 prefixEnd_6872853 3529077056695503664729831 := by
  unfold tailWord_6872853
  simp only [CollatzResearch.WordTrace]
  refine ⟨250673542569834845687327213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167115695046556563791551475 250673542569834845687327213)
  ·
    refine ⟨94002578463688067132747705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250673542569834845687327213 94002578463688067132747705)
    ·
      refine ⟨70501933847766050349560779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94002578463688067132747705 70501933847766050349560779)
      ·
        refine ⟨105752900771649075524341169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70501933847766050349560779 105752900771649075524341169)
        ·
          refine ⟨79314675578736806643255877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105752900771649075524341169 79314675578736806643255877)
          ·
            refine ⟨14871501671013151245610477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79314675578736806643255877 14871501671013151245610477)
            ·
              refine ⟨5576813126629931717103929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14871501671013151245610477 5576813126629931717103929)
              ·
                refine ⟨4182609844972448787827947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5576813126629931717103929 4182609844972448787827947)
                ·
                  refine ⟨6273914767458673181741921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182609844972448787827947 6273914767458673181741921)
                  ·
                    refine ⟨4705436075594004886306441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273914767458673181741921 4705436075594004886306441)
                    ·
                      refine ⟨3529077056695503664729831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705436075594004886306441 3529077056695503664729831)
                      ·
                        rfl

theorem cell23_6872853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_6872853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872853 prefixEnd_6872853 := by exact prefixLift 6872853
  have htrace : WordTrace (prefixWord ++ tailWord_6872853) baseStart_6872853 baseEnd_6872853 := by
    simpa [prefixWord, tailWord_6872853, baseEnd_6872853] using wordTrace_append hprefix tailTrace_6872853
  have hstable : (prefixWord ++ tailWord_6872853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872853).length < 2 ^ (prefixWord ++ tailWord_6872853).sum := by decide
  have hdescent : baseEnd_6872853 < baseStart_6872853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872869 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_6872869 : Nat := 118140960795 + 6872869 * 2 ^ 59
def prefixEnd_6872869 : Nat := 4983230072969 + 3 ^ 40 * 6872869 * 2
def baseEnd_6872869 : Nat := 3529085272385975602129757

theorem tailTrace_6872869 : CollatzResearch.WordTrace tailWord_6872869 prefixEnd_6872869 3529085272385975602129757 := by
  unfold tailWord_6872869
  simp only [CollatzResearch.WordTrace]
  refine ⟨250674126137776880419909661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167116084091851253613273107 250674126137776880419909661)
  ·
    refine ⟨94002797301666330157466123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250674126137776880419909661 94002797301666330157466123)
    ·
      refine ⟨141004195952499495236199185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94002797301666330157466123 141004195952499495236199185)
      ·
        refine ⟨105753146964374621427149389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141004195952499495236199185 105753146964374621427149389)
        ·
          refine ⟨39657430111640483035181021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105753146964374621427149389 39657430111640483035181021)
          ·
            refine ⟨14871536291865181138192883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39657430111640483035181021 14871536291865181138192883)
            ·
              refine ⟨22307304437797771707289325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871536291865181138192883 22307304437797771707289325)
              ·
                refine ⟨8365239164174164390233497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22307304437797771707289325 8365239164174164390233497)
                ·
                  refine ⟨6273929373130623292675123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365239164174164390233497 6273929373130623292675123)
                  ·
                    refine ⟨9410894059695934939012685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273929373130623292675123 9410894059695934939012685)
                    ·
                      refine ⟨3529085272385975602129757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410894059695934939012685 3529085272385975602129757)
                      ·
                        rfl

theorem cell23_6872869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_6872869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872869 prefixEnd_6872869 := by exact prefixLift 6872869
  have htrace : WordTrace (prefixWord ++ tailWord_6872869) baseStart_6872869 baseEnd_6872869 := by
    simpa [prefixWord, tailWord_6872869, baseEnd_6872869] using wordTrace_append hprefix tailTrace_6872869
  have hstable : (prefixWord ++ tailWord_6872869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872869).length < 2 ^ (prefixWord ++ tailWord_6872869).sum := by decide
  have hdescent : baseEnd_6872869 < baseStart_6872869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872892 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_6872892 : Nat := 118140960795 + 6872892 * 2 ^ 59
def prefixEnd_6872892 : Nat := 4983230072969 + 3 ^ 40 * 6872892 * 2
def baseEnd_6872892 : Nat := 3529097082441029012142151

theorem tailTrace_6872892 : CollatzResearch.WordTrace tailWord_6872892 prefixEnd_6872892 3529097082441029012142151 := by
  unfold tailWord_6872892
  simp only [CollatzResearch.WordTrace]
  refine ⟨125337482508346777673998465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167116643344462370231997953 125337482508346777673998465)
  ·
    refine ⟨94003111881260083255498849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125337482508346777673998465 94003111881260083255498849)
    ·
      refine ⟨70502333910945062441624137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94003111881260083255498849 70502333910945062441624137)
      ·
        refine ⟨52876750433208796831218103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70502333910945062441624137 52876750433208796831218103)
        ·
          refine ⟨79315125649813195246827155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52876750433208796831218103 79315125649813195246827155)
          ·
            refine ⟨118972688474719792870240733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79315125649813195246827155 118972688474719792870240733)
            ·
              refine ⟨44614758178019922326340275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118972688474719792870240733 44614758178019922326340275)
              ·
                refine ⟨66922137267029883489510413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44614758178019922326340275 66922137267029883489510413)
                ·
                  refine ⟨25095801475136206308566405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66922137267029883489510413 25095801475136206308566405)
                  ·
                    refine ⟨4705462776588038682856201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25095801475136206308566405 4705462776588038682856201)
                    ·
                      refine ⟨3529097082441029012142151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705462776588038682856201 3529097082441029012142151)
                      ·
                        rfl

theorem cell23_6872892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_6872892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872892 prefixEnd_6872892 := by exact prefixLift 6872892
  have htrace : WordTrace (prefixWord ++ tailWord_6872892) baseStart_6872892 baseEnd_6872892 := by
    simpa [prefixWord, tailWord_6872892, baseEnd_6872892] using wordTrace_append hprefix tailTrace_6872892
  have hstable : (prefixWord ++ tailWord_6872892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872892).length < 2 ^ (prefixWord ++ tailWord_6872892).sum := by decide
  have hdescent : baseEnd_6872892 < baseStart_6872892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872905 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_6872905 : Nat := 118140960795 + 6872905 * 2 ^ 59
def prefixEnd_6872905 : Nat := 4983230072969 + 3 ^ 40 * 6872905 * 2
def baseEnd_6872905 : Nat := 3529103757689537461279591

theorem tailTrace_6872905 : CollatzResearch.WordTrace tailWord_6872905 prefixEnd_6872905 3529103757689537461279591 := by
  unfold tailWord_6872905
  simp only [CollatzResearch.WordTrace]
  refine ⟨250675439165646458568220169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167116959443764305712146779 250675439165646458568220169)
  ·
    refine ⟨188006579374234843926165127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250675439165646458568220169 188006579374234843926165127)
    ·
      refine ⟨282009869061352265889247691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188006579374234843926165127 282009869061352265889247691)
      ·
        refine ⟨423014803592028398833871537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282009869061352265889247691 423014803592028398833871537)
        ·
          refine ⟨317261102694021299125403653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423014803592028398833871537 317261102694021299125403653)
          ·
            refine ⟨59486456755128993586013185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317261102694021299125403653 59486456755128993586013185)
            ·
              refine ⟨44614842566346745189509889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59486456755128993586013185 44614842566346745189509889)
              ·
                refine ⟨33461131924760058892132417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44614842566346745189509889 33461131924760058892132417)
                ·
                  refine ⟨25095848943570044169099313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33461131924760058892132417 25095848943570044169099313)
                  ·
                    refine ⟨18821886707677533126824485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25095848943570044169099313 18821886707677533126824485)
                    ·
                      refine ⟨3529103757689537461279591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18821886707677533126824485 3529103757689537461279591)
                      ·
                        rfl

theorem cell23_6872905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_6872905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872905 prefixEnd_6872905 := by exact prefixLift 6872905
  have htrace : WordTrace (prefixWord ++ tailWord_6872905) baseStart_6872905 baseEnd_6872905 := by
    simpa [prefixWord, tailWord_6872905, baseEnd_6872905] using wordTrace_append hprefix tailTrace_6872905
  have hstable : (prefixWord ++ tailWord_6872905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872905).length < 2 ^ (prefixWord ++ tailWord_6872905).sum := by decide
  have hdescent : baseEnd_6872905 < baseStart_6872905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872932 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 7]
def baseStart_6872932 : Nat := 118140960795 + 6872932 * 2 ^ 59
def prefixEnd_6872932 : Nat := 4983230072969 + 3 ^ 40 * 6872932 * 2
def baseEnd_6872932 : Nat := 392124180185245428404663

theorem tailTrace_6872932 : CollatzResearch.WordTrace tailWord_6872932 prefixEnd_6872932 392124180185245428404663 := by
  unfold tailWord_6872932
  simp only [CollatzResearch.WordTrace]
  refine ⟨125338211968274321089726525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167117615957699094786302033 125338211968274321089726525)
  ·
    refine ⟨47001829488102870408647447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125338211968274321089726525 47001829488102870408647447)
    ·
      refine ⟨70502744232154305612971171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47001829488102870408647447 70502744232154305612971171)
      ·
        refine ⟨105754116348231458419456757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70502744232154305612971171 105754116348231458419456757)
        ·
          refine ⟨9914448407646699226824071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105754116348231458419456757 9914448407646699226824071)
          ·
            refine ⟨14871672611470048840236107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914448407646699226824071 14871672611470048840236107)
            ·
              refine ⟨22307508917205073260354161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871672611470048840236107 22307508917205073260354161)
              ·
                refine ⟨16730631687903804945265621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22307508917205073260354161 16730631687903804945265621)
                ·
                  refine ⟨392124180185245428404663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16730631687903804945265621 392124180185245428404663)
                  ·
                    rfl

theorem cell23_6872932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_6872932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872932 prefixEnd_6872932 := by exact prefixLift 6872932
  have htrace : WordTrace (prefixWord ++ tailWord_6872932) baseStart_6872932 baseEnd_6872932 := by
    simpa [prefixWord, tailWord_6872932, baseEnd_6872932] using wordTrace_append hprefix tailTrace_6872932
  have hstable : (prefixWord ++ tailWord_6872932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872932).length < 2 ^ (prefixWord ++ tailWord_6872932).sum := by decide
  have hdescent : baseEnd_6872932 < baseStart_6872932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872945 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_6872945 : Nat := 118140960795 + 6872945 * 2 ^ 59
def prefixEnd_6872945 : Nat := 4983230072969 + 3 ^ 40 * 6872945 * 2
def baseEnd_6872945 : Nat := 1176374765638572434926469

theorem tailTrace_6872945 : CollatzResearch.WordTrace tailWord_6872945 prefixEnd_6872945 1176374765638572434926469 := by
  unfold tailWord_6872945
  simp only [CollatzResearch.WordTrace]
  refine ⟨250676898085501545399676289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167117932057001030266450859 250676898085501545399676289)
  ·
    refine ⟨188007673564126159049757217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250676898085501545399676289 188007673564126159049757217)
    ·
      refine ⟨141005755173094619287317913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188007673564126159049757217 141005755173094619287317913)
      ·
        refine ⟨105754316379820964465488435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141005755173094619287317913 105754316379820964465488435)
        ·
          refine ⟨158631474569731446698232653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105754316379820964465488435 158631474569731446698232653)
          ·
            refine ⟨59486802963649292511837245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158631474569731446698232653 59486802963649292511837245)
            ·
              refine ⟨22307551111368484691938967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59486802963649292511837245 22307551111368484691938967)
              ·
                refine ⟨33461326667052727037908451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22307551111368484691938967 33461326667052727037908451)
                ·
                  refine ⟨50191990000579090556862677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33461326667052727037908451 50191990000579090556862677)
                  ·
                    refine ⟨1176374765638572434926469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50191990000579090556862677 1176374765638572434926469)
                    ·
                      rfl

theorem cell23_6872945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_6872945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872945 prefixEnd_6872945 := by exact prefixLift 6872945
  have htrace : WordTrace (prefixWord ++ tailWord_6872945) baseStart_6872945 baseEnd_6872945 := by
    simpa [prefixWord, tailWord_6872945, baseEnd_6872945] using wordTrace_append hprefix tailTrace_6872945
  have hstable : (prefixWord ++ tailWord_6872945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872945).length < 2 ^ (prefixWord ++ tailWord_6872945).sum := by decide
  have hdescent : baseEnd_6872945 < baseStart_6872945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872949 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 5]
def baseStart_6872949 : Nat := 118140960795 + 6872949 * 2 ^ 59
def prefixEnd_6872949 : Nat := 4983230072969 + 3 ^ 40 * 6872949 * 2
def baseEnd_6872949 : Nat := 392125150093148365458821

theorem tailTrace_6872949 : CollatzResearch.WordTrace tailWord_6872949 prefixEnd_6872949 392125150093148365458821 := by
  unfold tailWord_6872949
  simp only [CollatzResearch.WordTrace]
  refine ⟨250677043977487054082821901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167118029318324702721881267 250677043977487054082821901)
  ·
    refine ⟨94003891491557645281058213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250677043977487054082821901 94003891491557645281058213)
    ·
      refine ⟨17625729654667058490198415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94003891491557645281058213 17625729654667058490198415)
      ·
        refine ⟨26438594482000587735297623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625729654667058490198415 26438594482000587735297623)
        ·
          refine ⟨39657891723000881602946435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26438594482000587735297623 39657891723000881602946435)
          ·
            refine ⟨59486837584501322404419653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39657891723000881602946435 59486837584501322404419653)
            ·
              refine ⟨11153782047093997950828685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59486837584501322404419653 11153782047093997950828685)
              ·
                refine ⟨4182668267660249231560757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11153782047093997950828685 4182668267660249231560757)
                ·
                  refine ⟨392125150093148365458821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182668267660249231560757 392125150093148365458821)
                  ·
                    rfl

theorem cell23_6872949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_6872949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872949 prefixEnd_6872949 := by exact prefixLift 6872949
  have htrace : WordTrace (prefixWord ++ tailWord_6872949) baseStart_6872949 baseEnd_6872949 := by
    simpa [prefixWord, tailWord_6872949, baseEnd_6872949] using wordTrace_append hprefix tailTrace_6872949
  have hstable : (prefixWord ++ tailWord_6872949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872949).length < 2 ^ (prefixWord ++ tailWord_6872949).sum := by decide
  have hdescent : baseEnd_6872949 < baseStart_6872949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872995 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4]
def baseStart_6872995 : Nat := 118140960795 + 6872995 * 2 ^ 59
def prefixEnd_6872995 : Nat := 4983230072969 + 3 ^ 40 * 6872995 * 2
def baseEnd_6872995 : Nat := 3529149970948442109154177

theorem tailTrace_6872995 : CollatzResearch.WordTrace tailWord_6872995 prefixEnd_6872995 3529149970948442109154177 := by
  unfold tailWord_6872995
  simp only [CollatzResearch.WordTrace]
  refine ⟨250678721735320403938996439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167119147823546935959330959 250678721735320403938996439)
  ·
    refine ⟨376018082602980605908494659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250678721735320403938996439 376018082602980605908494659)
    ·
      refine ⟨564027123904470908862741989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376018082602980605908494659 564027123904470908862741989)
      ·
        refine ⟨105755085732088295411764123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 564027123904470908862741989 105755085732088295411764123)
        ·
          refine ⟨158632628598132443117646185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105755085732088295411764123 158632628598132443117646185)
          ·
            refine ⟨118974471448599332338234639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158632628598132443117646185 118974471448599332338234639)
            ·
              refine ⟨178461707172898998507351959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118974471448599332338234639 178461707172898998507351959)
              ·
                refine ⟨267692560759348497761027939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178461707172898998507351959 267692560759348497761027939)
                ·
                  refine ⟨401538841139022746641541909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267692560759348497761027939 401538841139022746641541909)
                  ·
                    refine ⟨18822133178391691248822277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 401538841139022746641541909 18822133178391691248822277)
                    ·
                      refine ⟨3529149970948442109154177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18822133178391691248822277 3529149970948442109154177)
                      ·
                        rfl

theorem cell23_6872995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_6872995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872995 prefixEnd_6872995 := by exact prefixLift 6872995
  have htrace : WordTrace (prefixWord ++ tailWord_6872995) baseStart_6872995 baseEnd_6872995 := by
    simpa [prefixWord, tailWord_6872995, baseEnd_6872995] using wordTrace_append hprefix tailTrace_6872995
  have hstable : (prefixWord ++ tailWord_6872995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872995).length < 2 ^ (prefixWord ++ tailWord_6872995).sum := by decide
  have hdescent : baseEnd_6872995 < baseStart_6872995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873000 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 5]
def baseStart_6873000 : Nat := 118140960795 + 6873000 * 2 ^ 59
def prefixEnd_6873000 : Nat := 4983230072969 + 3 ^ 40 * 6873000 * 2
def baseEnd_6873000 : Nat := 392128059816857176621295

theorem tailTrace_6873000 : CollatzResearch.WordTrace tailWord_6873000 prefixEnd_6873000 392128059816857176621295 := by
  unfold tailWord_6873000
  simp only [CollatzResearch.WordTrace]
  refine ⟨125339452050151144896464227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167119269400201526528618969 125339452050151144896464227)
  ·
    refine ⟨188009178075226717344696341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125339452050151144896464227 188009178075226717344696341)
    ·
      refine ⟨8812930222276252375532641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188009178075226717344696341 8812930222276252375532641)
      ·
        refine ⟨6609697666707189281649481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8812930222276252375532641 6609697666707189281649481)
        ·
          refine ⟨4957273250030391961237111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6609697666707189281649481 4957273250030391961237111)
          ·
            refine ⟨7435909875045587941855667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957273250030391961237111 7435909875045587941855667)
            ·
              refine ⟨11153864812568381912783501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435909875045587941855667 11153864812568381912783501)
              ·
                refine ⟨4182699304713143217293813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11153864812568381912783501 4182699304713143217293813)
                ·
                  refine ⟨392128059816857176621295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182699304713143217293813 392128059816857176621295)
                  ·
                    rfl

theorem cell23_6873000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 5].length) (baseStart_6873000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873000 prefixEnd_6873000 := by exact prefixLift 6873000
  have htrace : WordTrace (prefixWord ++ tailWord_6873000) baseStart_6873000 baseEnd_6873000 := by
    simpa [prefixWord, tailWord_6873000, baseEnd_6873000] using wordTrace_append hprefix tailTrace_6873000
  have hstable : (prefixWord ++ tailWord_6873000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873000).length < 2 ^ (prefixWord ++ tailWord_6873000).sum := by decide
  have hdescent : baseEnd_6873000 < baseStart_6873000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873022 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_6873022 : Nat := 118140960795 + 6873022 * 2 ^ 59
def prefixEnd_6873022 : Nat := 4983230072969 + 3 ^ 40 * 6873022 * 2
def baseEnd_6873022 : Nat := 392129314991790389279617

theorem tailTrace_6873022 : CollatzResearch.WordTrace tailWord_6873022 prefixEnd_6873022 392129314991790389279617 := by
  unfold tailWord_6873022
  simp only [CollatzResearch.WordTrace]
  refine ⟨31334963313277823443778665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167119804337481725033486213 31334963313277823443778665)
  ·
    refine ⟨23501222484958367582833999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31334963313277823443778665 23501222484958367582833999)
    ·
      refine ⟨35251833727437551374250999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23501222484958367582833999 35251833727437551374250999)
      ·
        refine ⟨52877750591156327061376499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35251833727437551374250999 52877750591156327061376499)
        ·
          refine ⟨79316625886734490592064749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52877750591156327061376499 79316625886734490592064749)
          ·
            refine ⟨29743734707525433972024281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79316625886734490592064749 29743734707525433972024281)
            ·
              refine ⟨22307801030644075479018211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29743734707525433972024281 22307801030644075479018211)
              ·
                refine ⟨33461701545966113218527317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22307801030644075479018211 33461701545966113218527317)
                ·
                  refine ⟨392129314991790389279617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33461701545966113218527317 392129314991790389279617)
                  ·
                    rfl

theorem cell23_6873022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_6873022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873022 prefixEnd_6873022 := by exact prefixLift 6873022
  have htrace : WordTrace (prefixWord ++ tailWord_6873022) baseStart_6873022 baseEnd_6873022 := by
    simpa [prefixWord, tailWord_6873022, baseEnd_6873022] using wordTrace_append hprefix tailTrace_6873022
  have hstable : (prefixWord ++ tailWord_6873022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873022).length < 2 ^ (prefixWord ++ tailWord_6873022).sum := by decide
  have hdescent : baseEnd_6873022 < baseStart_6873022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873083 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 1, 1, 3]
def baseStart_6873083 : Nat := 118140960795 + 6873083 * 2 ^ 59
def prefixEnd_6873083 : Nat := 4983230072969 + 3 ^ 40 * 6873083 * 2
def baseEnd_6873083 : Nat := 3529195157246037764853773

theorem tailTrace_6873083 : CollatzResearch.WordTrace tailWord_6873083 prefixEnd_6873083 3529195157246037764853773 := by
  unfold tailWord_6873083
  simp only [CollatzResearch.WordTrace]
  refine ⟨250681931359001594968199903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167121287572667729978799935 250681931359001594968199903)
  ·
    refine ⟨376022897038502392452299855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250681931359001594968199903 376022897038502392452299855)
    ·
      refine ⟨564034345557753588678449783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376022897038502392452299855 564034345557753588678449783)
      ·
        refine ⟨846051518336630383017674675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564034345557753588678449783 846051518336630383017674675)
        ·
          refine ⟨1269077277504945574526512013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846051518336630383017674675 1269077277504945574526512013)
          ·
            refine ⟨475903979064354590447442005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1269077277504945574526512013 475903979064354590447442005)
            ·
              refine ⟨5576999754660405356805961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 475903979064354590447442005 5576999754660405356805961)
              ·
                refine ⟨4182749815995304017604471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5576999754660405356805961 4182749815995304017604471)
                ·
                  refine ⟨6274124723992956026406707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182749815995304017604471 6274124723992956026406707)
                  ·
                    refine ⟨9411187085989434039610061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6274124723992956026406707 9411187085989434039610061)
                    ·
                      refine ⟨3529195157246037764853773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9411187085989434039610061 3529195157246037764853773)
                      ·
                        rfl

theorem cell23_6873083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 1, 1, 3].length) (baseStart_6873083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873083 prefixEnd_6873083 := by exact prefixLift 6873083
  have htrace : WordTrace (prefixWord ++ tailWord_6873083) baseStart_6873083 baseEnd_6873083 := by
    simpa [prefixWord, tailWord_6873083, baseEnd_6873083] using wordTrace_append hprefix tailTrace_6873083
  have hstable : (prefixWord ++ tailWord_6873083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873083).length < 2 ^ (prefixWord ++ tailWord_6873083).sum := by decide
  have hdescent : baseEnd_6873083 < baseStart_6873083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873099 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 2, 4]
def baseStart_6873099 : Nat := 118140960795 + 6873099 * 2 ^ 59
def prefixEnd_6873099 : Nat := 4983230072969 + 3 ^ 40 * 6873099 * 2
def baseEnd_6873099 : Nat := 1176401124312169900751233

theorem tailTrace_6873099 : CollatzResearch.WordTrace tailWord_6873099 prefixEnd_6873099 1176401124312169900751233 := by
  unfold tailWord_6873099
  simp only [CollatzResearch.WordTrace]
  refine ⟨250682514926943629700782351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167121676617962419800521567 250682514926943629700782351)
  ·
    refine ⟨376023772390415444551173527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250682514926943629700782351 376023772390415444551173527)
    ·
      refine ⟨564035658585623166826760291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376023772390415444551173527 564035658585623166826760291)
      ·
        refine ⟨846053487878434750240140437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564035658585623166826760291 846053487878434750240140437)
        ·
          refine ⟨39658757244301628917506583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 846053487878434750240140437 39658757244301628917506583)
          ·
            refine ⟨59488135866452443376259875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39658757244301628917506583 59488135866452443376259875)
            ·
              refine ⟨89232203799678665064389813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59488135866452443376259875 89232203799678665064389813)
              ·
                refine ⟨8365519106219874849786545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89232203799678665064389813 8365519106219874849786545)
                ·
                  refine ⟨6274139329664906137339909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365519106219874849786545 6274139329664906137339909)
                  ·
                    refine ⟨1176401124312169900751233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6274139329664906137339909 1176401124312169900751233)
                    ·
                      rfl

theorem cell23_6873099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 4].length) (baseStart_6873099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873099 prefixEnd_6873099 := by exact prefixLift 6873099
  have htrace : WordTrace (prefixWord ++ tailWord_6873099) baseStart_6873099 baseEnd_6873099 := by
    simpa [prefixWord, tailWord_6873099, baseEnd_6873099] using wordTrace_append hprefix tailTrace_6873099
  have hstable : (prefixWord ++ tailWord_6873099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873099).length < 2 ^ (prefixWord ++ tailWord_6873099).sum := by decide
  have hdescent : baseEnd_6873099 < baseStart_6873099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873150 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_6873150 : Nat := 118140960795 + 6873150 * 2 ^ 59
def prefixEnd_6873150 : Nat := 4983230072969 + 3 ^ 40 * 6873150 * 2
def baseEnd_6873150 : Nat := 1176409853483296334238655

theorem tailTrace_6873150 : CollatzResearch.WordTrace tailWord_6873150 prefixEnd_6873150 1176409853483296334238655 := by
  unfold tailWord_6873150
  simp only [CollatzResearch.WordTrace]
  refine ⟨31335546881219858176361113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167122916699839243607259269 31335546881219858176361113)
  ·
    refine ⟨23501660160914893632270835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31335546881219858176361113 23501660160914893632270835)
    ·
      refine ⟨35252490241372340448406253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23501660160914893632270835 35252490241372340448406253)
      ·
        refine ⟨13219683840514627668152345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35252490241372340448406253 13219683840514627668152345)
        ·
          refine ⟨9914762880385970751114259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13219683840514627668152345 9914762880385970751114259)
          ·
            refine ⟨14872144320578956126671389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914762880385970751114259 14872144320578956126671389)
            ·
              refine ⟨5577054120217108547501771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14872144320578956126671389 5577054120217108547501771)
              ·
                refine ⟨8365581180325662821252657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577054120217108547501771 8365581180325662821252657)
                ·
                  refine ⟨6274185885244247115939493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365581180325662821252657 6274185885244247115939493)
                  ·
                    refine ⟨1176409853483296334238655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6274185885244247115939493 1176409853483296334238655)
                    ·
                      rfl

theorem cell23_6873150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_6873150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873150 prefixEnd_6873150 := by exact prefixLift 6873150
  have htrace : WordTrace (prefixWord ++ tailWord_6873150) baseStart_6873150 baseEnd_6873150 := by
    simpa [prefixWord, tailWord_6873150, baseEnd_6873150] using wordTrace_append hprefix tailTrace_6873150
  have hstable : (prefixWord ++ tailWord_6873150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873150).length < 2 ^ (prefixWord ++ tailWord_6873150).sum := by decide
  have hdescent : baseEnd_6873150 < baseStart_6873150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873174 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6873174 : Nat := 118140960795 + 6873174 * 2 ^ 59
def prefixEnd_6873174 : Nat := 4983230072969 + 3 ^ 40 * 6873174 * 2
def baseEnd_6873174 : Nat := 3529241883985596908815855

theorem tailTrace_6873174 : CollatzResearch.WordTrace tailWord_6873174 prefixEnd_6873174 3529241883985596908815855 := by
  unfold tailWord_6873174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667828150104494844360161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167123500267781278339841717 15667828150104494844360161)
  ·
    refine ⟨11750871112578371133270121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15667828150104494844360161 11750871112578371133270121)
    ·
      refine ⟨8813153334433778349952591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11750871112578371133270121 8813153334433778349952591)
      ·
        refine ⟨13219730001650667524928887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8813153334433778349952591 13219730001650667524928887)
        ·
          refine ⟨19829595002476001287393331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13219730001650667524928887 19829595002476001287393331)
          ·
            refine ⟨29744392503714001931089997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19829595002476001287393331 29744392503714001931089997)
            ·
              refine ⟨11154147188892750724158749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29744392503714001931089997 11154147188892750724158749)
              ·
                refine ⟨4182805195834781521559531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11154147188892750724158749 4182805195834781521559531)
                ·
                  refine ⟨6274207793752172282339297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182805195834781521559531 6274207793752172282339297)
                  ·
                    refine ⟨4705655845314129211754473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6274207793752172282339297 4705655845314129211754473)
                    ·
                      refine ⟨3529241883985596908815855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705655845314129211754473 3529241883985596908815855)
                      ·
                        rfl

theorem cell23_6873174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6873174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873174 prefixEnd_6873174 := by exact prefixLift 6873174
  have htrace : WordTrace (prefixWord ++ tailWord_6873174) baseStart_6873174 baseEnd_6873174 := by
    simpa [prefixWord, tailWord_6873174, baseEnd_6873174] using wordTrace_append hprefix tailTrace_6873174
  have hstable : (prefixWord ++ tailWord_6873174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873174).length < 2 ^ (prefixWord ++ tailWord_6873174).sum := by decide
  have hdescent : baseEnd_6873174 < baseStart_6873174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873217 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6873217 : Nat := 118140960795 + 6873217 * 2 ^ 59
def prefixEnd_6873217 : Nat := 4983230072969 + 3 ^ 40 * 6873217 * 2
def baseEnd_6873217 : Nat := 3529263963653740240578157

theorem tailTrace_6873217 : CollatzResearch.WordTrace tailWord_6873217 prefixEnd_6873217 3529263963653740240578157 := by
  unfold tailWord_6873217
  simp only [CollatzResearch.WordTrace]
  refine ⟨250686818740516135853577905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167124545827010757235718603 250686818740516135853577905)
  ·
    refine ⟨188015114055387101890183429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250686818740516135853577905 188015114055387101890183429)
    ·
      refine ⟨35252833885385081604409393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188015114055387101890183429 35252833885385081604409393)
      ·
        refine ⟨26439625414038811203307045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35252833885385081604409393 26439625414038811203307045)
        ·
          refine ⟨4957429765132277100620071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26439625414038811203307045 4957429765132277100620071)
          ·
            refine ⟨7436144647698415650930107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957429765132277100620071 7436144647698415650930107)
            ·
              refine ⟨11154216971547623476395161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436144647698415650930107 11154216971547623476395161)
              ·
                refine ⟨8365662728660717607296371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11154216971547623476395161 8365662728660717607296371)
                ·
                  refine ⟨12548494092991076410944557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8365662728660717607296371 12548494092991076410944557)
                  ·
                    refine ⟨4705685284871653654104209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12548494092991076410944557 4705685284871653654104209)
                    ·
                      refine ⟨3529263963653740240578157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705685284871653654104209 3529263963653740240578157)
                      ·
                        rfl

theorem cell23_6873217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6873217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873217 prefixEnd_6873217 := by exact prefixLift 6873217
  have htrace : WordTrace (prefixWord ++ tailWord_6873217) baseStart_6873217 baseEnd_6873217 := by
    simpa [prefixWord, tailWord_6873217, baseEnd_6873217] using wordTrace_append hprefix tailTrace_6873217
  have hstable : (prefixWord ++ tailWord_6873217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873217).length < 2 ^ (prefixWord ++ tailWord_6873217).sum := by decide
  have hdescent : baseEnd_6873217 < baseStart_6873217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873306 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_6873306 : Nat := 118140960795 + 6873306 * 2 ^ 59
def prefixEnd_6873306 : Nat := 4983230072969 + 3 ^ 40 * 6873306 * 2
def baseEnd_6873306 : Nat := 3529309663431990392365247

theorem tailTrace_6873306 : CollatzResearch.WordTrace tailWord_6873306 prefixEnd_6873306 3529309663431990392365247 := by
  unfold tailWord_6873306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62672516209298426013391943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167126709891462469369045181 62672516209298426013391943)
  ·
    refine ⟨94008774313947639020087915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62672516209298426013391943 94008774313947639020087915)
    ·
      refine ⟨141013161470921458530131873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94008774313947639020087915 141013161470921458530131873)
      ·
        refine ⟨105759871103191093897598905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141013161470921458530131873 105759871103191093897598905)
        ·
          refine ⟨79319903327393320423199179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105759871103191093897598905 79319903327393320423199179)
          ·
            refine ⟨118979854991089980634798769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79319903327393320423199179 118979854991089980634798769)
            ·
              refine ⟨89234891243317485476099077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118979854991089980634798769 89234891243317485476099077)
              ·
                refine ⟨16731542108122028526768577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89234891243317485476099077 16731542108122028526768577)
                ·
                  refine ⟨12548656581091521395076433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16731542108122028526768577 12548656581091521395076433)
                  ·
                    refine ⟨9411492435818641046307325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12548656581091521395076433 9411492435818641046307325)
                    ·
                      refine ⟨3529309663431990392365247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9411492435818641046307325 3529309663431990392365247)
                      ·
                        rfl

theorem cell23_6873306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_6873306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873306 prefixEnd_6873306 := by exact prefixLift 6873306
  have htrace : WordTrace (prefixWord ++ tailWord_6873306) baseStart_6873306 baseEnd_6873306 := by
    simpa [prefixWord, tailWord_6873306, baseEnd_6873306] using wordTrace_append hprefix tailTrace_6873306
  have hstable : (prefixWord ++ tailWord_6873306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873306).length < 2 ^ (prefixWord ++ tailWord_6873306).sum := by decide
  have hdescent : baseEnd_6873306 < baseStart_6873306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873313 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 1, 4]
def baseStart_6873313 : Nat := 118140960795 + 6873313 * 2 ^ 59
def prefixEnd_6873313 : Nat := 4983230072969 + 3 ^ 40 * 6873313 * 2
def baseEnd_6873313 : Nat := 1176437752598857288325905

theorem tailTrace_6873313 : CollatzResearch.WordTrace tailWord_6873313 prefixEnd_6873313 1176437752598857288325905 := by
  unfold tailWord_6873313
  simp only [CollatzResearch.WordTrace]
  refine ⟨250690320148168344249072593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167126880098778896166048395 250690320148168344249072593)
  ·
    refine ⟨188017740111126258186804445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250690320148168344249072593 188017740111126258186804445)
    ·
      refine ⟨70506652541672346820051667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188017740111126258186804445 70506652541672346820051667)
      ·
        refine ⟨105759978812508520230077501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70506652541672346820051667 105759978812508520230077501)
        ·
          refine ⟨39659992054690695086279063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105759978812508520230077501 39659992054690695086279063)
          ·
            refine ⟨59489988082036042629418595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39659992054690695086279063 59489988082036042629418595)
            ·
              refine ⟨89234982123054063944127893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59489988082036042629418595 89234982123054063944127893)
              ·
                refine ⟨4182889787018159247380995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89234982123054063944127893 4182889787018159247380995)
                ·
                  refine ⟨6274334680527238871071493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182889787018159247380995 6274334680527238871071493)
                  ·
                    refine ⟨1176437752598857288325905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6274334680527238871071493 1176437752598857288325905)
                    ·
                      rfl

theorem cell23_6873313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_6873313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873313 prefixEnd_6873313 := by exact prefixLift 6873313
  have htrace : WordTrace (prefixWord ++ tailWord_6873313) baseStart_6873313 baseEnd_6873313 := by
    simpa [prefixWord, tailWord_6873313, baseEnd_6873313] using wordTrace_append hprefix tailTrace_6873313
  have hstable : (prefixWord ++ tailWord_6873313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873313).length < 2 ^ (prefixWord ++ tailWord_6873313).sum := by decide
  have hdescent : baseEnd_6873313 < baseStart_6873313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873356 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_6873356 : Nat := 118140960795 + 6873356 * 2 ^ 59
def prefixEnd_6873356 : Nat := 4983230072969 + 3 ^ 40 * 6873356 * 2
def baseEnd_6873356 : Nat := 1176445112488238398913339

theorem tailTrace_6873356 : CollatzResearch.WordTrace tailWord_6873356 prefixEnd_6873356 1176445112488238398913339 := by
  unfold tailWord_6873356
  simp only [CollatzResearch.WordTrace]
  refine ⟨125345944243506281296443961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167127925658008375061925281 125345944243506281296443961)
  ·
    refine ⟨94009458182629710972332971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125345944243506281296443961 94009458182629710972332971)
    ·
      refine ⟨141014187273944566458499457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94009458182629710972332971 141014187273944566458499457)
      ·
        refine ⟨105760640455458424843874593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141014187273944566458499457 105760640455458424843874593)
        ·
          refine ⟨79320480341593818632905945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105760640455458424843874593 79320480341593818632905945)
          ·
            refine ⟨59490360256195363974679459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79320480341593818632905945 59490360256195363974679459)
            ·
              refine ⟨89235540384293045962019189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59490360256195363974679459 89235540384293045962019189)
              ·
                refine ⟨8365831911027473058939299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89235540384293045962019189 8365831911027473058939299)
                ·
                  refine ⟨12548747866541209588408949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8365831911027473058939299 12548747866541209588408949)
                  ·
                    refine ⟨1176445112488238398913339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12548747866541209588408949 1176445112488238398913339)
                    ·
                      rfl

theorem cell23_6873356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_6873356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873356 prefixEnd_6873356 := by exact prefixLift 6873356
  have htrace : WordTrace (prefixWord ++ tailWord_6873356) baseStart_6873356 baseEnd_6873356 := by
    simpa [prefixWord, tailWord_6873356, baseEnd_6873356] using wordTrace_append hprefix tailTrace_6873356
  have hstable : (prefixWord ++ tailWord_6873356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873356).length < 2 ^ (prefixWord ++ tailWord_6873356).sum := by decide
  have hdescent : baseEnd_6873356 < baseStart_6873356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873390 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_6873390 : Nat := 118140960795 + 6873390 * 2 ^ 59
def prefixEnd_6873390 : Nat := 4983230072969 + 3 ^ 40 * 6873390 * 2
def baseEnd_6873390 : Nat := 1176450931935656021238287

theorem tailTrace_6873390 : CollatzResearch.WordTrace tailWord_6873390 prefixEnd_6873390 1176450931935656021238287 := by
  unfold tailWord_6873390
  simp only [CollatzResearch.WordTrace]
  refine ⟨31336641071111173299953203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167128752379259590933083749 31336641071111173299953203)
  ·
    refine ⟨47004961606666759949929805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31336641071111173299953203 47004961606666759949929805)
    ·
      refine ⟨17626860602500034981223677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47004961606666759949929805 17626860602500034981223677)
      ·
        refine ⟨6610072725937513117958879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17626860602500034981223677 6610072725937513117958879)
        ·
          refine ⟨9915109088906269676938319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610072725937513117958879 9915109088906269676938319)
          ·
            refine ⟨14872663633359404515407479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915109088906269676938319 14872663633359404515407479)
            ·
              refine ⟨22308995450039106773111219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14872663633359404515407479 22308995450039106773111219)
              ·
                refine ⟨33463493175058660159666829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22308995450039106773111219 33463493175058660159666829)
                ·
                  refine ⟨12548809940646997559875061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33463493175058660159666829 12548809940646997559875061)
                  ·
                    refine ⟨1176450931935656021238287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12548809940646997559875061 1176450931935656021238287)
                    ·
                      rfl

theorem cell23_6873390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_6873390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873390 prefixEnd_6873390 := by exact prefixLift 6873390
  have htrace : WordTrace (prefixWord ++ tailWord_6873390) baseStart_6873390 baseEnd_6873390 := by
    simpa [prefixWord, tailWord_6873390, baseEnd_6873390] using wordTrace_append hprefix tailTrace_6873390
  have hstable : (prefixWord ++ tailWord_6873390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873390).length < 2 ^ (prefixWord ++ tailWord_6873390).sum := by decide
  have hdescent : baseEnd_6873390 < baseStart_6873390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873393 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_6873393 : Nat := 118140960795 + 6873393 * 2 ^ 59
def prefixEnd_6873393 : Nat := 4983230072969 + 3 ^ 40 * 6873393 * 2
def baseEnd_6873393 : Nat := 3529354336248931551977347

theorem tailTrace_6873393 : CollatzResearch.WordTrace tailWord_6873393 prefixEnd_6873393 3529354336248931551977347 := by
  unfold tailWord_6873393
  simp only [CollatzResearch.WordTrace]
  refine ⟨250693237987878517911984833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167128825325252345274656555 250693237987878517911984833)
  ·
    refine ⟨188019928490908888433988625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250693237987878517911984833 188019928490908888433988625)
    ·
      refine ⟨141014946368181666325491469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188019928490908888433988625 141014946368181666325491469)
      ·
        refine ⟨52880604888068124872059301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141014946368181666325491469 52880604888068124872059301)
        ·
          refine ⟨9915113416512773413511119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52880604888068124872059301 9915113416512773413511119)
          ·
            refine ⟨14872670124769160120266679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915113416512773413511119 14872670124769160120266679)
            ·
              refine ⟨22309005187153740180400019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14872670124769160120266679 22309005187153740180400019)
              ·
                refine ⟨33463507780730610270600029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22309005187153740180400019 33463507780730610270600029)
                ·
                  refine ⟨12548815417773978851475011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33463507780730610270600029 12548815417773978851475011)
                  ·
                    refine ⟨18823223126660968277212517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12548815417773978851475011 18823223126660968277212517)
                    ·
                      refine ⟨3529354336248931551977347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18823223126660968277212517 3529354336248931551977347)
                      ·
                        rfl

theorem cell23_6873393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_6873393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873393 prefixEnd_6873393 := by exact prefixLift 6873393
  have htrace : WordTrace (prefixWord ++ tailWord_6873393) baseStart_6873393 baseEnd_6873393 := by
    simpa [prefixWord, tailWord_6873393, baseEnd_6873393] using wordTrace_append hprefix tailTrace_6873393
  have hstable : (prefixWord ++ tailWord_6873393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873393).length < 2 ^ (prefixWord ++ tailWord_6873393).sum := by decide
  have hdescent : baseEnd_6873393 < baseStart_6873393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873419 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_6873419 : Nat := 118140960795 + 6873419 * 2 ^ 59
def prefixEnd_6873419 : Nat := 4983230072969 + 3 ^ 40 * 6873419 * 2
def baseEnd_6873419 : Nat := 3529367686745948450252227

theorem tailTrace_6873419 : CollatzResearch.WordTrace tailWord_6873419 prefixEnd_6873419 3529367686745948450252227 := by
  unfold tailWord_6873419
  simp only [CollatzResearch.WordTrace]
  refine ⟨250694186285784324352431311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167129457523856216234954207 250694186285784324352431311)
  ·
    refine ⟨376041279428676486528646967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250694186285784324352431311 376041279428676486528646967)
    ·
      refine ⟨564061919143014729792970451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376041279428676486528646967 564061919143014729792970451)
      ·
        refine ⟨846092878714522094689455677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564061919143014729792970451 846092878714522094689455677)
        ·
          refine ⟨317284829517945785508545879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 846092878714522094689455677 317284829517945785508545879)
          ·
            refine ⟨475927244276918678262818819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317284829517945785508545879 475927244276918678262818819)
            ·
              refine ⟨713890866415378017394228229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475927244276918678262818819 713890866415378017394228229)
              ·
                refine ⟨133854537452883378261417793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713890866415378017394228229 133854537452883378261417793)
                ·
                  refine ⟨100390903089662533696063345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133854537452883378261417793 100390903089662533696063345)
                  ·
                    refine ⟨75293177317246900272047509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100390903089662533696063345 75293177317246900272047509)
                    ·
                      refine ⟨3529367686745948450252227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75293177317246900272047509 3529367686745948450252227)
                      ·
                        rfl

theorem cell23_6873419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_6873419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873419 prefixEnd_6873419 := by exact prefixLift 6873419
  have htrace : WordTrace (prefixWord ++ tailWord_6873419) baseStart_6873419 baseEnd_6873419 := by
    simpa [prefixWord, tailWord_6873419, baseEnd_6873419] using wordTrace_append hprefix tailTrace_6873419
  have hstable : (prefixWord ++ tailWord_6873419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873419).length < 2 ^ (prefixWord ++ tailWord_6873419).sum := by decide
  have hdescent : baseEnd_6873419 < baseStart_6873419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873443 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 3]
def baseStart_6873443 : Nat := 118140960795 + 6873443 * 2 ^ 59
def prefixEnd_6873443 : Nat := 4983230072969 + 3 ^ 40 * 6873443 * 2
def baseEnd_6873443 : Nat := 3529380010281656356352117

theorem tailTrace_6873443 : CollatzResearch.WordTrace tailWord_6873443 prefixEnd_6873443 3529380010281656356352117 := by
  unfold tailWord_6873443
  simp only [CollatzResearch.WordTrace]
  refine ⟨250695061637697376451304983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167130041091798250967536655 250695061637697376451304983)
  ·
    refine ⟨376042592456546064676957475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250695061637697376451304983 376042592456546064676957475)
    ·
      refine ⟨564063888684819097015436213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376042592456546064676957475 564063888684819097015436213)
      ·
        refine ⟨52880989564201790345197145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 564063888684819097015436213 52880989564201790345197145)
        ·
          refine ⟨39660742173151342758897859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52880989564201790345197145 39660742173151342758897859)
          ·
            refine ⟨59491113259727014138346789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39660742173151342758897859 59491113259727014138346789)
            ·
              refine ⟨11154583736198815150940023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59491113259727014138346789 11154583736198815150940023)
              ·
                refine ⟨16731875604298222726410035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11154583736198815150940023 16731875604298222726410035)
                ·
                  refine ⟨25097813406447334089615053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16731875604298222726410035 25097813406447334089615053)
                  ·
                    refine ⟨9411680027417750283605645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25097813406447334089615053 9411680027417750283605645)
                    ·
                      refine ⟨3529380010281656356352117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9411680027417750283605645 3529380010281656356352117)
                      ·
                        rfl

theorem cell23_6873443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_6873443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873443 prefixEnd_6873443 := by exact prefixLift 6873443
  have htrace : WordTrace (prefixWord ++ tailWord_6873443) baseStart_6873443 baseEnd_6873443 := by
    simpa [prefixWord, tailWord_6873443, baseEnd_6873443] using wordTrace_append hprefix tailTrace_6873443
  have hstable : (prefixWord ++ tailWord_6873443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873443).length < 2 ^ (prefixWord ++ tailWord_6873443).sum := by decide
  have hdescent : baseEnd_6873443 < baseStart_6873443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873476 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6873476 : Nat := 118140960795 + 6873476 * 2 ^ 59
def prefixEnd_6873476 : Nat := 4983230072969 + 3 ^ 40 * 6873476 * 2
def baseEnd_6873476 : Nat := 1176465651714418242413155

theorem tailTrace_6873476 : CollatzResearch.WordTrace tailWord_6873476 prefixEnd_6873476 1176465651714418242413155 := by
  unfold tailWord_6873476
  simp only [CollatzResearch.WordTrace]
  refine ⟨125348132623288911543628141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167130843497718548724837521 125348132623288911543628141)
  ·
    refine ⟨47005549733733341828860553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125348132623288911543628141 47005549733733341828860553)
    ·
      refine ⟨35254162300300006371645415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47005549733733341828860553 35254162300300006371645415)
      ·
        refine ⟨52881243450450009557468123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35254162300300006371645415 52881243450450009557468123)
        ·
          refine ⟨79321865175675014336202185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52881243450450009557468123 79321865175675014336202185)
          ·
            refine ⟨59491398881756260752151639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79321865175675014336202185 59491398881756260752151639)
            ·
              refine ⟨89237098322634391128227459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59491398881756260752151639 89237098322634391128227459)
              ·
                refine ⟨133855647483951586692341189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89237098322634391128227459 133855647483951586692341189)
                ·
                  refine ⟨25097933903240922504813973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133855647483951586692341189 25097933903240922504813973)
                  ·
                    refine ⟨1176465651714418242413155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25097933903240922504813973 1176465651714418242413155)
                    ·
                      rfl

theorem cell23_6873476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6873476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873476 prefixEnd_6873476 := by exact prefixLift 6873476
  have htrace : WordTrace (prefixWord ++ tailWord_6873476) baseStart_6873476 baseEnd_6873476 := by
    simpa [prefixWord, tailWord_6873476, baseEnd_6873476] using wordTrace_append hprefix tailTrace_6873476
  have hstable : (prefixWord ++ tailWord_6873476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873476).length < 2 ^ (prefixWord ++ tailWord_6873476).sum := by decide
  have hdescent : baseEnd_6873476 < baseStart_6873476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873590 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6873590 : Nat := 118140960795 + 6873590 * 2 ^ 59
def prefixEnd_6873590 : Nat := 4983230072969 + 3 ^ 40 * 6873590 * 2
def baseEnd_6873590 : Nat := 3529455491937867281213941

theorem tailTrace_6873590 : CollatzResearch.WordTrace tailWord_6873590 prefixEnd_6873590 3529455491937867281213941 := by
  unfold tailWord_6873590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668776448010301284806639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167133615445443213704604149 15668776448010301284806639)
  ·
    refine ⟨23503164672015451927209959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15668776448010301284806639 23503164672015451927209959)
    ·
      refine ⟨35254747008023177890814939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23503164672015451927209959 35254747008023177890814939)
      ·
        refine ⟨52882120512034766836222409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35254747008023177890814939 52882120512034766836222409)
        ·
          refine ⟨39661590384026075127166807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52882120512034766836222409 39661590384026075127166807)
          ·
            refine ⟨59492385576039112690750211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39661590384026075127166807 59492385576039112690750211)
            ·
              refine ⟨89238578364058669036125317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59492385576039112690750211 89238578364058669036125317)
              ·
                refine ⟨16732233443261000444273497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89238578364058669036125317 16732233443261000444273497)
                ·
                  refine ⟨12549175082445750333205123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16732233443261000444273497 12549175082445750333205123)
                  ·
                    refine ⟨18823762623668625499807685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12549175082445750333205123 18823762623668625499807685)
                    ·
                      refine ⟨3529455491937867281213941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18823762623668625499807685 3529455491937867281213941)
                      ·
                        rfl

theorem cell23_6873590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6873590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873590 prefixEnd_6873590 := by exact prefixLift 6873590
  have htrace : WordTrace (prefixWord ++ tailWord_6873590) baseStart_6873590 baseEnd_6873590 := by
    simpa [prefixWord, tailWord_6873590, baseEnd_6873590] using wordTrace_append hprefix tailTrace_6873590
  have hstable : (prefixWord ++ tailWord_6873590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873590).length < 2 ^ (prefixWord ++ tailWord_6873590).sum := by decide
  have hdescent : baseEnd_6873590 < baseStart_6873590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873607 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6873607 : Nat := 118140960795 + 6873607 * 2 ^ 59
def prefixEnd_6873607 : Nat := 4983230072969 + 3 ^ 40 * 6873607 * 2
def baseEnd_6873607 : Nat := 3529464221108993714701363

theorem tailTrace_6873607 : CollatzResearch.WordTrace tailWord_6873607 prefixEnd_6873607 3529464221108993714701363 := by
  unfold tailWord_6873607
  simp only [CollatzResearch.WordTrace]
  refine ⟨250701043209103232460275075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167134028806068821640183383 250701043209103232460275075)
  ·
    refine ⟨376051564813654848690412613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250701043209103232460275075 376051564813654848690412613)
    ·
      refine ⟨70509668402560284129452365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376051564813654848690412613 70509668402560284129452365)
      ·
        refine ⟨26441125650960106548544637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70509668402560284129452365 26441125650960106548544637)
        ·
          refine ⟨9915422119110039955704239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26441125650960106548544637 9915422119110039955704239)
          ·
            refine ⟨14873133178665059933556359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915422119110039955704239 14873133178665059933556359)
            ·
              refine ⟨22309699767997589900334539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14873133178665059933556359 22309699767997589900334539)
              ·
                refine ⟨33464549651996384850501809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22309699767997589900334539 33464549651996384850501809)
                ·
                  refine ⟨25098412238997288637876357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33464549651996384850501809 25098412238997288637876357)
                  ·
                    refine ⟨4705952294811991619601817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25098412238997288637876357 4705952294811991619601817)
                    ·
                      refine ⟨3529464221108993714701363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4705952294811991619601817 3529464221108993714701363)
                      ·
                        rfl

theorem cell23_6873607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6873607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873607 prefixEnd_6873607 := by exact prefixLift 6873607
  have htrace : WordTrace (prefixWord ++ tailWord_6873607) baseStart_6873607 baseEnd_6873607 := by
    simpa [prefixWord, tailWord_6873607, baseEnd_6873607] using wordTrace_append hprefix tailTrace_6873607
  have hstable : (prefixWord ++ tailWord_6873607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873607).length < 2 ^ (prefixWord ++ tailWord_6873607).sum := by decide
  have hdescent : baseEnd_6873607 < baseStart_6873607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873657 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6873657 : Nat := 118140960795 + 6873657 * 2 ^ 59
def prefixEnd_6873657 : Nat := 4983230072969 + 3 ^ 40 * 6873657 * 2
def baseEnd_6873657 : Nat := 3529489895141718519076133

theorem tailTrace_6873657 : CollatzResearch.WordTrace tailWord_6873657 prefixEnd_6873657 3529489895141718519076133 := by
  unfold tailWord_6873657
  simp only [CollatzResearch.WordTrace]
  refine ⟨250702866858922090999595225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167135244572614727333063483 250702866858922090999595225)
  ·
    refine ⟨188027150144191568249696419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250702866858922090999595225 188027150144191568249696419)
    ·
      refine ⟨282040725216287352374544629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188027150144191568249696419 282040725216287352374544629)
      ·
        refine ⟨26441317989026939285113559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282040725216287352374544629 26441317989026939285113559)
        ·
          refine ⟨39661976983540408927670339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26441317989026939285113559 39661976983540408927670339)
          ·
            refine ⟨59492965475310613391505509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39661976983540408927670339 59492965475310613391505509)
            ·
              refine ⟨11154931026620740010907283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59492965475310613391505509 11154931026620740010907283)
              ·
                refine ⟨16732396539931110016360925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11154931026620740010907283 16732396539931110016360925)
                ·
                  refine ⟨6274648702474166256135347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16732396539931110016360925 6274648702474166256135347)
                  ·
                    refine ⟨9411973053711249384203021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6274648702474166256135347 9411973053711249384203021)
                    ·
                      refine ⟨3529489895141718519076133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9411973053711249384203021 3529489895141718519076133)
                      ·
                        rfl

theorem cell23_6873657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6873657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873657 prefixEnd_6873657 := by exact prefixLift 6873657
  have htrace : WordTrace (prefixWord ++ tailWord_6873657) baseStart_6873657 baseEnd_6873657 := by
    simpa [prefixWord, tailWord_6873657, baseEnd_6873657] using wordTrace_append hprefix tailTrace_6873657
  have hstable : (prefixWord ++ tailWord_6873657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873657).length < 2 ^ (prefixWord ++ tailWord_6873657).sum := by decide
  have hdescent : baseEnd_6873657 < baseStart_6873657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873677 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_6873677 : Nat := 118140960795 + 6873677 * 2 ^ 59
def prefixEnd_6873677 : Nat := 4983230072969 + 3 ^ 40 * 6873677 * 2
def baseEnd_6873677 : Nat := 1176500054918269480275347

theorem tailTrace_6873677 : CollatzResearch.WordTrace tailWord_6873677 prefixEnd_6873677 1176500054918269480275347 := by
  unfold tailWord_6873677
  simp only [CollatzResearch.WordTrace]
  refine ⟨250703596318849634415323285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167135730879233089610215523 250703596318849634415323285)
  ·
    refine ⟨11751731077446076613218279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250703596318849634415323285 11751731077446076613218279)
    ·
      refine ⟨17627596616169114919827419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11751731077446076613218279 17627596616169114919827419)
      ·
        refine ⟨26441394924253672379741129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17627596616169114919827419 26441394924253672379741129)
        ·
          refine ⟨19831046193190254284805847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26441394924253672379741129 19831046193190254284805847)
          ·
            refine ⟨29746569289785381427208771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19831046193190254284805847 29746569289785381427208771)
            ·
              refine ⟨44619853934678072140813157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29746569289785381427208771 44619853934678072140813157)
              ·
                refine ⟨8366222612752138526402467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44619853934678072140813157 8366222612752138526402467)
                ·
                  refine ⟨12549333919128207789603701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8366222612752138526402467 12549333919128207789603701)
                  ·
                    refine ⟨1176500054918269480275347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12549333919128207789603701 1176500054918269480275347)
                    ·
                      rfl

theorem cell23_6873677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_6873677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873677 prefixEnd_6873677 := by exact prefixLift 6873677
  have htrace : WordTrace (prefixWord ++ tailWord_6873677) baseStart_6873677 baseEnd_6873677 := by
    simpa [prefixWord, tailWord_6873677, baseEnd_6873677] using wordTrace_append hprefix tailTrace_6873677
  have hstable : (prefixWord ++ tailWord_6873677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873677).length < 2 ^ (prefixWord ++ tailWord_6873677).sum := by decide
  have hdescent : baseEnd_6873677 < baseStart_6873677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873700 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_6873700 : Nat := 118140960795 + 6873700 * 2 ^ 59
def prefixEnd_6873700 : Nat := 4983230072969 + 3 ^ 40 * 6873700 * 2
def baseEnd_6873700 : Nat := 3529511974809861850838435

theorem tailTrace_6873700 : CollatzResearch.WordTrace tailWord_6873700 prefixEnd_6873700 3529511974809861850838435 := by
  unfold tailWord_6873700
  simp only [CollatzResearch.WordTrace]
  refine ⟨125352217598883154671705277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167136290131844206228940369 125352217598883154671705277)
  ·
    refine ⟨47007081599581183001889479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125352217598883154671705277 47007081599581183001889479)
    ·
      refine ⟨70510622399371774502834219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47007081599581183001889479 70510622399371774502834219)
      ·
        refine ⟨105765933599057661754251329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70510622399371774502834219 105765933599057661754251329)
        ·
          refine ⟨79324450199293246315688497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105765933599057661754251329 79324450199293246315688497)
          ·
            refine ⟨59493337649469934736766373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79324450199293246315688497 59493337649469934736766373)
            ·
              refine ⟨11155000809275612763143695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59493337649469934736766373 11155000809275612763143695)
              ·
                refine ⟨16732501213913419144715543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11155000809275612763143695 16732501213913419144715543)
                ·
                  refine ⟨25098751820870128717073315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16732501213913419144715543 25098751820870128717073315)
                  ·
                    refine ⟨37648127731305193075609973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25098751820870128717073315 37648127731305193075609973)
                    ·
                      refine ⟨3529511974809861850838435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37648127731305193075609973 3529511974809861850838435)
                      ·
                        rfl

theorem cell23_6873700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_6873700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873700 prefixEnd_6873700 := by exact prefixLift 6873700
  have htrace : WordTrace (prefixWord ++ tailWord_6873700) baseStart_6873700 baseEnd_6873700 := by
    simpa [prefixWord, tailWord_6873700, baseEnd_6873700] using wordTrace_append hprefix tailTrace_6873700
  have hstable : (prefixWord ++ tailWord_6873700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873700).length < 2 ^ (prefixWord ++ tailWord_6873700).sum := by decide
  have hdescent : baseEnd_6873700 < baseStart_6873700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873710 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6873710 : Nat := 118140960795 + 6873710 * 2 ^ 59
def prefixEnd_6873710 : Nat := 4983230072969 + 3 ^ 40 * 6873710 * 2
def baseEnd_6873710 : Nat := 3529517109616406811713389

theorem tailTrace_6873710 : CollatzResearch.WordTrace tailWord_6873710 prefixEnd_6873710 3529517109616406811713389 := by
  unfold tailWord_6873710
  simp only [CollatzResearch.WordTrace]
  refine ⟨31338099990966260131409323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167136533285153387367516389 31338099990966260131409323)
  ·
    refine ⟨47007149986449390197113985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31338099990966260131409323 47007149986449390197113985)
    ·
      refine ⟨35255362489837042647835489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47007149986449390197113985 35255362489837042647835489)
      ·
        refine ⟨26441521867377781985876617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35255362489837042647835489 26441521867377781985876617)
        ·
          refine ⟨19831141400533336489407463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26441521867377781985876617 19831141400533336489407463)
          ·
            refine ⟨29746712100800004734111195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19831141400533336489407463 29746712100800004734111195)
            ·
              refine ⟨44620068151200007101166793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29746712100800004734111195 44620068151200007101166793)
              ·
                refine ⟨33465051113400005325875095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44620068151200007101166793 33465051113400005325875095)
                ·
                  refine ⟨50197576670100007988812643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33465051113400005325875095 50197576670100007988812643)
                  ·
                    refine ⟨75296365005150011983218965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50197576670100007988812643 75296365005150011983218965)
                    ·
                      refine ⟨3529517109616406811713389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75296365005150011983218965 3529517109616406811713389)
                      ·
                        rfl

theorem cell23_6873710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6873710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873710 prefixEnd_6873710 := by exact prefixLift 6873710
  have htrace : WordTrace (prefixWord ++ tailWord_6873710) baseStart_6873710 baseEnd_6873710 := by
    simpa [prefixWord, tailWord_6873710, baseEnd_6873710] using wordTrace_append hprefix tailTrace_6873710
  have hstable : (prefixWord ++ tailWord_6873710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873710).length < 2 ^ (prefixWord ++ tailWord_6873710).sum := by decide
  have hdescent : baseEnd_6873710 < baseStart_6873710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873764 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_6873764 : Nat := 118140960795 + 6873764 * 2 ^ 59
def prefixEnd_6873764 : Nat := 4983230072969 + 3 ^ 40 * 6873764 * 2
def baseEnd_6873764 : Nat := 3529544837571749600438141

theorem tailTrace_6873764 : CollatzResearch.WordTrace tailWord_6873764 prefixEnd_6873764 3529544837571749600438141 := by
  unfold tailWord_6873764
  simp only [CollatzResearch.WordTrace]
  refine ⟨125353384734767224136870173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167137846313022965515826897 125353384734767224136870173)
  ·
    refine ⟨47007519275537709051326315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125353384734767224136870173 47007519275537709051326315)
    ·
      refine ⟨70511278913306563576989473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47007519275537709051326315 70511278913306563576989473)
      ·
        refine ⟨52883459184979922682742105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70511278913306563576989473 52883459184979922682742105)
        ·
          refine ⟨39662594388734942012056579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52883459184979922682742105 39662594388734942012056579)
          ·
            refine ⟨59493891583102413018084869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39662594388734942012056579 59493891583102413018084869)
            ·
              refine ⟨11155104671831702440890913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59493891583102413018084869 11155104671831702440890913)
              ·
                refine ⟨8366328503873776830668185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11155104671831702440890913 8366328503873776830668185)
                ·
                  refine ⟨6274746377905332623001139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8366328503873776830668185 6274746377905332623001139)
                  ·
                    refine ⟨9412119566857998934501709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6274746377905332623001139 9412119566857998934501709)
                    ·
                      refine ⟨3529544837571749600438141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412119566857998934501709 3529544837571749600438141)
                      ·
                        rfl

theorem cell23_6873764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_6873764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873764 prefixEnd_6873764 := by exact prefixLift 6873764
  have htrace : WordTrace (prefixWord ++ tailWord_6873764) baseStart_6873764 baseEnd_6873764 := by
    simpa [prefixWord, tailWord_6873764, baseEnd_6873764] using wordTrace_append hprefix tailTrace_6873764
  have hstable : (prefixWord ++ tailWord_6873764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873764).length < 2 ^ (prefixWord ++ tailWord_6873764).sum := by decide
  have hdescent : baseEnd_6873764 < baseStart_6873764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873787 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 8, 2, 2]
def baseStart_6873787 : Nat := 118140960795 + 6873787 * 2 ^ 59
def prefixEnd_6873787 : Nat := 4983230072969 + 3 ^ 40 * 6873787 * 2
def baseEnd_6873787 : Nat := 3529556647626803010450535

theorem tailTrace_6873787 : CollatzResearch.WordTrace tailWord_6873787 prefixEnd_6873787 3529556647626803010450535 := by
  unfold tailWord_6873787
  simp only [CollatzResearch.WordTrace]
  refine ⟨250707608348451123201827615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167138405565634082134551743 250707608348451123201827615)
  ·
    refine ⟨376061412522676684802741423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250707608348451123201827615 376061412522676684802741423)
    ·
      refine ⟨564092118784015027204112135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376061412522676684802741423 564092118784015027204112135)
      ·
        refine ⟨846138178176022540806168203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564092118784015027204112135 846138178176022540806168203)
        ·
          refine ⟨1269207267264033811209252305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846138178176022540806168203 1269207267264033811209252305)
          ·
            refine ⟨951905450448025358406939229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269207267264033811209252305 951905450448025358406939229)
            ·
              refine ⟨356964543918009509402602211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 951905450448025358406939229 356964543918009509402602211)
              ·
                refine ⟨535446815877014264103903317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356964543918009509402602211 535446815877014264103903317)
                ·
                  refine ⟨6274767373558760907467617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 535446815877014264103903317 6274767373558760907467617)
                  ·
                    refine ⟨4706075530169070680600713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6274767373558760907467617 4706075530169070680600713)
                    ·
                      refine ⟨3529556647626803010450535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706075530169070680600713 3529556647626803010450535)
                      ·
                        rfl

theorem cell23_6873787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 2, 2].length) (baseStart_6873787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873787 prefixEnd_6873787 := by exact prefixLift 6873787
  have htrace : WordTrace (prefixWord ++ tailWord_6873787) baseStart_6873787 baseEnd_6873787 := by
    simpa [prefixWord, tailWord_6873787, baseEnd_6873787] using wordTrace_append hprefix tailTrace_6873787
  have hstable : (prefixWord ++ tailWord_6873787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873787).length < 2 ^ (prefixWord ++ tailWord_6873787).sum := by decide
  have hdescent : baseEnd_6873787 < baseStart_6873787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873803 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_6873803 : Nat := 118140960795 + 6873803 * 2 ^ 59
def prefixEnd_6873803 : Nat := 4983230072969 + 3 ^ 40 * 6873803 * 2
def baseEnd_6873803 : Nat := 3529564863317274947850461

theorem tailTrace_6873803 : CollatzResearch.WordTrace tailWord_6873803 prefixEnd_6873803 3529564863317274947850461 := by
  unfold tailWord_6873803
  simp only [CollatzResearch.WordTrace]
  refine ⟨250708191916393157934410063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167138794610928771956273375 250708191916393157934410063)
  ·
    refine ⟨376062287874589736901615095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250708191916393157934410063 376062287874589736901615095)
    ·
      refine ⟨564093431811884605352422643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376062287874589736901615095 564093431811884605352422643)
      ·
        refine ⟨846140147717826908028633965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564093431811884605352422643 846140147717826908028633965)
        ·
          refine ⟨317302555394185090510737737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 846140147717826908028633965 317302555394185090510737737)
          ·
            refine ⟨237976916545638817883053303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317302555394185090510737737 237976916545638817883053303)
            ·
              refine ⟨356965374818458226824579955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237976916545638817883053303 356965374818458226824579955)
              ·
                refine ⟨535448062227687340236869933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356965374818458226824579955 535448062227687340236869933)
                ·
                  refine ⟨200793023335382752588826225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535448062227687340236869933 200793023335382752588826225)
                  ·
                    refine ⟨150594767501537064441619669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200793023335382752588826225 150594767501537064441619669)
                    ·
                      refine ⟨3529564863317274947850461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150594767501537064441619669 3529564863317274947850461)
                      ·
                        rfl

theorem cell23_6873803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_6873803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873803 prefixEnd_6873803 := by exact prefixLift 6873803
  have htrace : WordTrace (prefixWord ++ tailWord_6873803) baseStart_6873803 baseEnd_6873803 := by
    simpa [prefixWord, tailWord_6873803, baseEnd_6873803] using wordTrace_append hprefix tailTrace_6873803
  have hstable : (prefixWord ++ tailWord_6873803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873803).length < 2 ^ (prefixWord ++ tailWord_6873803).sum := by decide
  have hdescent : baseEnd_6873803 < baseStart_6873803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873804 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6873804 : Nat := 118140960795 + 6873804 * 2 ^ 59
def prefixEnd_6873804 : Nat := 4983230072969 + 3 ^ 40 * 6873804 * 2
def baseEnd_6873804 : Nat := 3529565376797929443937957

theorem tailTrace_6873804 : CollatzResearch.WordTrace tailWord_6873804 prefixEnd_6873804 3529565376797929443937957 := by
  unfold tailWord_6873804
  simp only [CollatzResearch.WordTrace]
  refine ⟨125354114194694767552598233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167138818926259690070130977 125354114194694767552598233)
  ·
    refine ⟨94015585646021075664448675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125354114194694767552598233 94015585646021075664448675)
    ·
      refine ⟨141023378469031613496673013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94015585646021075664448675 141023378469031613496673013)
      ·
        refine ⟨13220941731471713765313095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141023378469031613496673013 13220941731471713765313095)
        ·
          refine ⟨19831412597207570647969643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13220941731471713765313095 19831412597207570647969643)
          ·
            refine ⟨29747118895811355971954465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19831412597207570647969643 29747118895811355971954465)
            ·
              refine ⟨22310339171858516978965849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29747118895811355971954465 22310339171858516978965849)
              ·
                refine ⟨16732754378893887734224387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22310339171858516978965849 16732754378893887734224387)
                ·
                  refine ⟨25099131568340831601336581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16732754378893887734224387 25099131568340831601336581)
                  ·
                    refine ⟨4706087169063905925250609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25099131568340831601336581 4706087169063905925250609)
                    ·
                      refine ⟨3529565376797929443937957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706087169063905925250609 3529565376797929443937957)
                      ·
                        rfl

theorem cell23_6873804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6873804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873804 prefixEnd_6873804 := by exact prefixLift 6873804
  have htrace : WordTrace (prefixWord ++ tailWord_6873804) baseStart_6873804 baseEnd_6873804 := by
    simpa [prefixWord, tailWord_6873804, baseEnd_6873804] using wordTrace_append hprefix tailTrace_6873804
  have hstable : (prefixWord ++ tailWord_6873804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873804).length < 2 ^ (prefixWord ++ tailWord_6873804).sum := by decide
  have hdescent : baseEnd_6873804 < baseStart_6873804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873827 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 7]
def baseStart_6873827 : Nat := 118140960795 + 6873827 * 2 ^ 59
def prefixEnd_6873827 : Nat := 4983230072969 + 3 ^ 40 * 6873827 * 2
def baseEnd_6873827 : Nat := 392175242983664761550039

theorem tailTrace_6873827 : CollatzResearch.WordTrace tailWord_6873827 prefixEnd_6873827 392175242983664761550039 := by
  unfold tailWord_6873827
  simp only [CollatzResearch.WordTrace]
  refine ⟨250709067268306210033283735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167139378178870806688855823 250709067268306210033283735)
  ·
    refine ⟨376063600902459315049925603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250709067268306210033283735 376063600902459315049925603)
    ·
      refine ⟨564095401353688972574888405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376063600902459315049925603 564095401353688972574888405)
      ·
        refine ⟨13220985969227085294723947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 564095401353688972574888405 13220985969227085294723947)
        ·
          refine ⟨19831478953840627942085921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13220985969227085294723947 19831478953840627942085921)
          ·
            refine ⟨14873609215380470956564441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19831478953840627942085921 14873609215380470956564441)
            ·
              refine ⟨11155206911535353217423331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14873609215380470956564441 11155206911535353217423331)
              ·
                refine ⟨16732810367303029826134997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11155206911535353217423331 16732810367303029826134997)
                ·
                  refine ⟨392175242983664761550039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16732810367303029826134997 392175242983664761550039)
                  ·
                    rfl

theorem cell23_6873827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 7].length) (baseStart_6873827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873827 prefixEnd_6873827 := by exact prefixLift 6873827
  have htrace : WordTrace (prefixWord ++ tailWord_6873827) baseStart_6873827 baseEnd_6873827 := by
    simpa [prefixWord, tailWord_6873827, baseEnd_6873827] using wordTrace_append hprefix tailTrace_6873827
  have hstable : (prefixWord ++ tailWord_6873827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873827).length < 2 ^ (prefixWord ++ tailWord_6873827).sum := by decide
  have hdescent : baseEnd_6873827 < baseStart_6873827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873837 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_6873837 : Nat := 118140960795 + 6873837 * 2 ^ 59
def prefixEnd_6873837 : Nat := 4983230072969 + 3 ^ 40 * 6873837 * 2
def baseEnd_6873837 : Nat := 3529582321659527814825305

theorem tailTrace_6873837 : CollatzResearch.WordTrace tailWord_6873837 prefixEnd_6873837 3529582321659527814825305 := by
  unfold tailWord_6873837
  simp only [CollatzResearch.WordTrace]
  refine ⟨250709431998269981741147765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167139621332179987827431843 250709431998269981741147765)
  ·
    refine ⟨23504009249837810788232603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250709431998269981741147765 23504009249837810788232603)
    ·
      refine ⟨35256013874756716182348905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23504009249837810788232603 35256013874756716182348905)
      ·
        refine ⟨26442010406067537136761679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35256013874756716182348905 26442010406067537136761679)
        ·
          refine ⟨39663015609101305705142519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26442010406067537136761679 39663015609101305705142519)
          ·
            refine ⟨59494523413651958557713779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39663015609101305705142519 59494523413651958557713779)
            ·
              refine ⟨89241785120477937836570669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59494523413651958557713779 89241785120477937836570669)
              ·
                refine ⟨33465669420179226688714001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89241785120477937836570669 33465669420179226688714001)
                ·
                  refine ⟨25099252065134420016535501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33465669420179226688714001 25099252065134420016535501)
                  ·
                    refine ⟨9412219524425407506200813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25099252065134420016535501 9412219524425407506200813)
                    ·
                      refine ⟨3529582321659527814825305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412219524425407506200813 3529582321659527814825305)
                      ·
                        rfl

theorem cell23_6873837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_6873837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873837 prefixEnd_6873837 := by exact prefixLift 6873837
  have htrace : WordTrace (prefixWord ++ tailWord_6873837) baseStart_6873837 baseEnd_6873837 := by
    simpa [prefixWord, tailWord_6873837, baseEnd_6873837] using wordTrace_append hprefix tailTrace_6873837
  have hstable : (prefixWord ++ tailWord_6873837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873837).length < 2 ^ (prefixWord ++ tailWord_6873837).sum := by decide
  have hdescent : baseEnd_6873837 < baseStart_6873837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873838 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_6873838 : Nat := 118140960795 + 6873838 * 2 ^ 59
def prefixEnd_6873838 : Nat := 4983230072969 + 3 ^ 40 * 6873838 * 2
def baseEnd_6873838 : Nat := 3529582835140182310912801

theorem tailTrace_6873838 : CollatzResearch.WordTrace tailWord_6873838 prefixEnd_6873838 3529582835140182310912801 := by
  unfold tailWord_6873838
  simp only [CollatzResearch.WordTrace]
  refine ⟨31338683558908294863991771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167139645647510905941289445 31338683558908294863991771)
  ·
    refine ⟨47008025338362442295987657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31338683558908294863991771 47008025338362442295987657)
    ·
      refine ⟨35256019003771831721990743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47008025338362442295987657 35256019003771831721990743)
      ·
        refine ⟨52884028505657747582986115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35256019003771831721990743 52884028505657747582986115)
        ·
          refine ⟨79326042758486621374479173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52884028505657747582986115 79326042758486621374479173)
          ·
            refine ⟨14873633017216241507714845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79326042758486621374479173 14873633017216241507714845)
            ·
              refine ⟨5577612381456090565393067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14873633017216241507714845 5577612381456090565393067)
              ·
                refine ⟨8366418572184135848089601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577612381456090565393067 8366418572184135848089601)
                ·
                  refine ⟨6274813929138101886067201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8366418572184135848089601 6274813929138101886067201)
                  ·
                    refine ⟨4706110446853576414550401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6274813929138101886067201 4706110446853576414550401)
                    ·
                      refine ⟨3529582835140182310912801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706110446853576414550401 3529582835140182310912801)
                      ·
                        rfl

theorem cell23_6873838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_6873838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873838 prefixEnd_6873838 := by exact prefixLift 6873838
  have htrace : WordTrace (prefixWord ++ tailWord_6873838) baseStart_6873838 baseEnd_6873838 := by
    simpa [prefixWord, tailWord_6873838, baseEnd_6873838] using wordTrace_append hprefix tailTrace_6873838
  have hstable : (prefixWord ++ tailWord_6873838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873838).length < 2 ^ (prefixWord ++ tailWord_6873838).sum := by decide
  have hdescent : baseEnd_6873838 < baseStart_6873838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873877 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6873877 : Nat := 118140960795 + 6873877 * 2 ^ 59
def prefixEnd_6873877 : Nat := 4983230072969 + 3 ^ 40 * 6873877 * 2
def baseEnd_6873877 : Nat := 3529602860885707658325121

theorem tailTrace_6873877 : CollatzResearch.WordTrace tailWord_6873877 prefixEnd_6873877 3529602860885707658325121 := by
  unfold tailWord_6873877
  simp only [CollatzResearch.WordTrace]
  refine ⟨250710890918125068572603885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167140593945416712381735923 250710890918125068572603885)
  ·
    refine ⟨94016584094296900714726457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250710890918125068572603885 94016584094296900714726457)
    ·
      refine ⟨70512438070722675536044843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94016584094296900714726457 70512438070722675536044843)
      ·
        refine ⟨105768657106084013304067265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70512438070722675536044843 105768657106084013304067265)
        ·
          refine ⟨79326492829563009978050449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105768657106084013304067265 79326492829563009978050449)
          ·
            refine ⟨59494869622172257483537837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79326492829563009978050449 59494869622172257483537837)
            ·
              refine ⟨22310576108314596556326689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59494869622172257483537837 22310576108314596556326689)
              ·
                refine ⟨16732932081235947417245017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22310576108314596556326689 16732932081235947417245017)
                ·
                  refine ⟨12549699060926960562933763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16732932081235947417245017 12549699060926960562933763)
                  ·
                    refine ⟨18824548591390440844400645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12549699060926960562933763 18824548591390440844400645)
                    ·
                      refine ⟨3529602860885707658325121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18824548591390440844400645 3529602860885707658325121)
                      ·
                        rfl

theorem cell23_6873877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6873877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873877 prefixEnd_6873877 := by exact prefixLift 6873877
  have htrace : WordTrace (prefixWord ++ tailWord_6873877) baseStart_6873877 baseEnd_6873877 := by
    simpa [prefixWord, tailWord_6873877, baseEnd_6873877] using wordTrace_append hprefix tailTrace_6873877
  have hstable : (prefixWord ++ tailWord_6873877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873877).length < 2 ^ (prefixWord ++ tailWord_6873877).sum := by decide
  have hdescent : baseEnd_6873877 < baseStart_6873877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873977 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_6873977 : Nat := 118140960795 + 6873977 * 2 ^ 59
def prefixEnd_6873977 : Nat := 4983230072969 + 3 ^ 40 * 6873977 * 2
def baseEnd_6873977 : Nat := 1176551402983719089024887

theorem tailTrace_6873977 : CollatzResearch.WordTrace tailWord_6873977 prefixEnd_6873977 1176551402983719089024887 := by
  unfold tailWord_6873977
  simp only [CollatzResearch.WordTrace]
  refine ⟨250714538217762785651244185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167143025478508523767496123 250714538217762785651244185)
  ·
    refine ⟨188035903663322089238433139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250714538217762785651244185 188035903663322089238433139)
    ·
      refine ⟨282053855494983133857649709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188035903663322089238433139 282053855494983133857649709)
      ·
        refine ⟨105770195810618675196618641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282053855494983133857649709 105770195810618675196618641)
        ·
          refine ⟨79327646857964006397463981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105770195810618675196618641 79327646857964006397463981)
          ·
            refine ⟨29747867571736502399048993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79327646857964006397463981 29747867571736502399048993)
            ·
              refine ⟨22310900678802376799286745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29747867571736502399048993 22310900678802376799286745)
              ·
                refine ⟨16733175509101782599465059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22310900678802376799286745 16733175509101782599465059)
                ·
                  refine ⟨25099763263652673899197589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16733175509101782599465059 25099763263652673899197589)
                  ·
                    refine ⟨1176551402983719089024887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25099763263652673899197589 1176551402983719089024887)
                    ·
                      rfl

theorem cell23_6873977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_6873977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873977 prefixEnd_6873977 := by exact prefixLift 6873977
  have htrace : WordTrace (prefixWord ++ tailWord_6873977) baseStart_6873977 baseEnd_6873977 := by
    simpa [prefixWord, tailWord_6873977, baseEnd_6873977] using wordTrace_append hprefix tailTrace_6873977
  have hstable : (prefixWord ++ tailWord_6873977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873977).length < 2 ^ (prefixWord ++ tailWord_6873977).sum := by decide
  have hdescent : baseEnd_6873977 < baseStart_6873977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6873987 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5]
def baseStart_6873987 : Nat := 118140960795 + 6873987 * 2 ^ 59
def prefixEnd_6873987 : Nat := 4983230072969 + 3 ^ 40 * 6873987 * 2
def baseEnd_6873987 : Nat := 3529659343757702227949615

theorem tailTrace_6873987 : CollatzResearch.WordTrace tailWord_6873987 prefixEnd_6873987 3529659343757702227949615 := by
  unfold tailWord_6873987
  simp only [CollatzResearch.WordTrace]
  refine ⟨250714902947726557359108215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167143268631817704906072143 250714902947726557359108215)
  ·
    refine ⟨376072354421589836038662323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250714902947726557359108215 376072354421589836038662323)
    ·
      refine ⟨564108531632384754057993485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376072354421589836038662323 564108531632384754057993485)
      ·
        refine ⟨211540699362144282771747557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564108531632384754057993485 211540699362144282771747557)
        ·
          refine ⟨39663881130402053019702667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211540699362144282771747557 39663881130402053019702667)
          ·
            refine ⟨59495821695603079529554001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39663881130402053019702667 59495821695603079529554001)
            ·
              refine ⟨44621866271702309647165501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59495821695603079529554001 44621866271702309647165501)
              ·
                refine ⟨16733199851888366117687063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44621866271702309647165501 16733199851888366117687063)
                ·
                  refine ⟨25099799777832549176530595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16733199851888366117687063 25099799777832549176530595)
                  ·
                    refine ⟨37649699666748823764795893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25099799777832549176530595 37649699666748823764795893)
                    ·
                      refine ⟨3529659343757702227949615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37649699666748823764795893 3529659343757702227949615)
                      ·
                        rfl

theorem cell23_6873987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_6873987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6873987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6873987 prefixEnd_6873987 := by exact prefixLift 6873987
  have htrace : WordTrace (prefixWord ++ tailWord_6873987) baseStart_6873987 baseEnd_6873987 := by
    simpa [prefixWord, tailWord_6873987, baseEnd_6873987] using wordTrace_append hprefix tailTrace_6873987
  have hstable : (prefixWord ++ tailWord_6873987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6873987).length < 2 ^ (prefixWord ++ tailWord_6873987).sum := by decide
  have hdescent : baseEnd_6873987 < baseStart_6873987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6873987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874004 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6874004 : Nat := 118140960795 + 6874004 * 2 ^ 59
def prefixEnd_6874004 : Nat := 4983230072969 + 3 ^ 40 * 6874004 * 2
def baseEnd_6874004 : Nat := 3529668072928828661437037

theorem tailTrace_6874004 : CollatzResearch.WordTrace tailWord_6874004 prefixEnd_6874004 3529668072928828661437037 := by
  unfold tailWord_6874004
  simp only [CollatzResearch.WordTrace]
  refine ⟨125357761494332484631238533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167143681992443312841651377 125357761494332484631238533)
  ·
    refine ⟨23504580280187340868357225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125357761494332484631238533 23504580280187340868357225)
    ·
      refine ⟨17628435210140505651267919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23504580280187340868357225 17628435210140505651267919)
      ·
        refine ⟨26442652815210758476901879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17628435210140505651267919 26442652815210758476901879)
        ·
          refine ⟨39663979222816137715352819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26442652815210758476901879 39663979222816137715352819)
          ·
            refine ⟨59495968834224206573029229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39663979222816137715352819 59495968834224206573029229)
            ·
              refine ⟨22310988312834077464885961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59495968834224206573029229 22310988312834077464885961)
              ·
                refine ⟨16733241234625558098664471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22310988312834077464885961 16733241234625558098664471)
                ·
                  refine ⟨25099861851938337147996707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16733241234625558098664471 25099861851938337147996707)
                  ·
                    refine ⟨37649792777907505721995061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25099861851938337147996707 37649792777907505721995061)
                    ·
                      refine ⟨3529668072928828661437037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37649792777907505721995061 3529668072928828661437037)
                      ·
                        rfl

theorem cell23_6874004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6874004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874004 prefixEnd_6874004 := by exact prefixLift 6874004
  have htrace : WordTrace (prefixWord ++ tailWord_6874004) baseStart_6874004 baseEnd_6874004 := by
    simpa [prefixWord, tailWord_6874004, baseEnd_6874004] using wordTrace_append hprefix tailTrace_6874004
  have hstable : (prefixWord ++ tailWord_6874004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874004).length < 2 ^ (prefixWord ++ tailWord_6874004).sum := by decide
  have hdescent : baseEnd_6874004 < baseStart_6874004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874018 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6874018 : Nat := 118140960795 + 6874018 * 2 ^ 59
def prefixEnd_6874018 : Nat := 4983230072969 + 3 ^ 40 * 6874018 * 2
def baseEnd_6874018 : Nat := 3529675261657991606661973

theorem tailTrace_6874018 : CollatzResearch.WordTrace tailWord_6874018 prefixEnd_6874018 3529675261657991606661973 := by
  unfold tailWord_6874018
  simp only [CollatzResearch.WordTrace]
  refine ⟨62679008402653562413371677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167144022407076166435657805 62679008402653562413371677)
  ·
    refine ⟨23504628150995085905014379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62679008402653562413371677 23504628150995085905014379)
    ·
      refine ⟨35256942226492628857521569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23504628150995085905014379 35256942226492628857521569)
      ·
        refine ⟨26442706669869471643141177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35256942226492628857521569 26442706669869471643141177)
        ·
          refine ⟨19832030002402103732355883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26442706669869471643141177 19832030002402103732355883)
          ·
            refine ⟨29748045003603155598533825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19832030002402103732355883 29748045003603155598533825)
            ·
              refine ⟨22311033752702366698900369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29748045003603155598533825 22311033752702366698900369)
              ·
                refine ⟨16733275314526775024175277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22311033752702366698900369 16733275314526775024175277)
                ·
                  refine ⟨6274978242947540634065729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16733275314526775024175277 6274978242947540634065729)
                  ·
                    refine ⟨4706233682210655475549297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6274978242947540634065729 4706233682210655475549297)
                    ·
                      refine ⟨3529675261657991606661973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706233682210655475549297 3529675261657991606661973)
                      ·
                        rfl

theorem cell23_6874018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6874018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874018 prefixEnd_6874018 := by exact prefixLift 6874018
  have htrace : WordTrace (prefixWord ++ tailWord_6874018) baseStart_6874018 baseEnd_6874018 := by
    simpa [prefixWord, tailWord_6874018, baseEnd_6874018] using wordTrace_append hprefix tailTrace_6874018
  have hstable : (prefixWord ++ tailWord_6874018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874018).length < 2 ^ (prefixWord ++ tailWord_6874018).sum := by decide
  have hdescent : baseEnd_6874018 < baseStart_6874018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874029 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6874029 : Nat := 118140960795 + 6874029 * 2 ^ 59
def prefixEnd_6874029 : Nat := 4983230072969 + 3 ^ 40 * 6874029 * 2
def baseEnd_6874029 : Nat := 3529680909945191063624423

theorem tailTrace_6874029 : CollatzResearch.WordTrace tailWord_6874029 prefixEnd_6874029 3529680909945191063624423 := by
  unfold tailWord_6874029
  simp only [CollatzResearch.WordTrace]
  refine ⟨250716434813574398532137141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167144289875716265688091427 250716434813574398532137141)
  ·
    refine ⟨23504665763772599862387857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250716434813574398532137141 23504665763772599862387857)
    ·
      refine ⟨17628499322829449896790893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23504665763772599862387857 17628499322829449896790893)
      ·
        refine ⟨6610687246061043711296585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17628499322829449896790893 6610687246061043711296585)
        ·
          refine ⟨4958015434545782783472439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6610687246061043711296585 4958015434545782783472439)
          ·
            refine ⟨7437023151818674175208659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958015434545782783472439 7437023151818674175208659)
            ·
              refine ⟨11155534727728011262812989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437023151818674175208659 11155534727728011262812989)
              ·
                refine ⟨4183325522898004223554871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11155534727728011262812989 4183325522898004223554871)
                ·
                  refine ⟨6274988284347006335332307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4183325522898004223554871 6274988284347006335332307)
                  ·
                    refine ⟨9412482426520509502998461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6274988284347006335332307 9412482426520509502998461)
                    ·
                      refine ⟨3529680909945191063624423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412482426520509502998461 3529680909945191063624423)
                      ·
                        rfl

theorem cell23_6874029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6874029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874029 prefixEnd_6874029 := by exact prefixLift 6874029
  have htrace : WordTrace (prefixWord ++ tailWord_6874029) baseStart_6874029 baseEnd_6874029 := by
    simpa [prefixWord, tailWord_6874029, baseEnd_6874029] using wordTrace_append hprefix tailTrace_6874029
  have hstable : (prefixWord ++ tailWord_6874029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874029).length < 2 ^ (prefixWord ++ tailWord_6874029).sum := by decide
  have hdescent : baseEnd_6874029 < baseStart_6874029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874052 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6874052 : Nat := 118140960795 + 6874052 * 2 ^ 59
def prefixEnd_6874052 : Nat := 4983230072969 + 3 ^ 40 * 6874052 * 2
def baseEnd_6874052 : Nat := 3529692720000244473636817

theorem tailTrace_6874052 : CollatzResearch.WordTrace tailWord_6874052 prefixEnd_6874052 3529692720000244473636817 := by
  unfold tailWord_6874052
  simp only [CollatzResearch.WordTrace]
  refine ⟨125358636846245536730112205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167144849128327382306816273 125358636846245536730112205)
  ·
    refine ⟨47009488817342076273792077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125358636846245536730112205 47009488817342076273792077)
    ·
      refine ⟨17628558306503278602672029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47009488817342076273792077 17628558306503278602672029)
      ·
        refine ⟨6610709364938729476002011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17628558306503278602672029 6610709364938729476002011)
        ·
          refine ⟨9916064047408094214003017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610709364938729476002011 9916064047408094214003017)
          ·
            refine ⟨7437048035556070660502263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9916064047408094214003017 7437048035556070660502263)
            ·
              refine ⟨11155572053334105990753395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437048035556070660502263 11155572053334105990753395)
              ·
                refine ⟨16733358080001158986130093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11155572053334105990753395 16733358080001158986130093)
                ·
                  refine ⟨6275009280000434619798785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16733358080001158986130093 6275009280000434619798785)
                  ·
                    refine ⟨4706256960000325964849089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275009280000434619798785 4706256960000325964849089)
                    ·
                      refine ⟨3529692720000244473636817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706256960000325964849089 3529692720000244473636817)
                      ·
                        rfl

theorem cell23_6874052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6874052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874052 prefixEnd_6874052 := by exact prefixLift 6874052
  have htrace : WordTrace (prefixWord ++ tailWord_6874052) baseStart_6874052 baseEnd_6874052 := by
    simpa [prefixWord, tailWord_6874052, baseEnd_6874052] using wordTrace_append hprefix tailTrace_6874052
  have hstable : (prefixWord ++ tailWord_6874052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874052).length < 2 ^ (prefixWord ++ tailWord_6874052).sum := by decide
  have hdescent : baseEnd_6874052 < baseStart_6874052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874068 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_6874068 : Nat := 118140960795 + 6874068 * 2 ^ 59
def prefixEnd_6874068 : Nat := 4983230072969 + 3 ^ 40 * 6874068 * 2
def baseEnd_6874068 : Nat := 3529700935690716411036743

theorem tailTrace_6874068 : CollatzResearch.WordTrace tailWord_6874068 prefixEnd_6874068 3529700935690716411036743 := by
  unfold tailWord_6874068
  simp only [CollatzResearch.WordTrace]
  refine ⟨125358928630216554096403429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167145238173622072128537905 125358928630216554096403429)
  ·
    refine ⟨23504799118165603893075643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125358928630216554096403429 23504799118165603893075643)
    ·
      refine ⟨35257198677248405839613465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23504799118165603893075643 35257198677248405839613465)
      ·
        refine ⟨26442899007936304379710099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35257198677248405839613465 26442899007936304379710099)
        ·
          refine ⟨39664348511904456569565149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26442899007936304379710099 39664348511904456569565149)
          ·
            refine ⟨14874130691964171213586931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39664348511904456569565149 14874130691964171213586931)
            ·
              refine ⟨22311196037946256820380397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14874130691964171213586931 22311196037946256820380397)
              ·
                refine ⟨8366698514229846307642649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22311196037946256820380397 8366698514229846307642649)
                ·
                  refine ⟨6275023885672384730731987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8366698514229846307642649 6275023885672384730731987)
                  ·
                    refine ⟨9412535828508577096097981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6275023885672384730731987 9412535828508577096097981)
                    ·
                      refine ⟨3529700935690716411036743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412535828508577096097981 3529700935690716411036743)
                      ·
                        rfl

theorem cell23_6874068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_6874068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874068 prefixEnd_6874068 := by exact prefixLift 6874068
  have htrace : WordTrace (prefixWord ++ tailWord_6874068) baseStart_6874068 baseEnd_6874068 := by
    simpa [prefixWord, tailWord_6874068, baseEnd_6874068] using wordTrace_append hprefix tailTrace_6874068
  have hstable : (prefixWord ++ tailWord_6874068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874068).length < 2 ^ (prefixWord ++ tailWord_6874068).sum := by decide
  have hdescent : baseEnd_6874068 < baseStart_6874068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874108 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_6874108 : Nat := 118140960795 + 6874108 * 2 ^ 59
def prefixEnd_6874108 : Nat := 4983230072969 + 3 ^ 40 * 6874108 * 2
def baseEnd_6874108 : Nat := 3529721474916896254536559

theorem tailTrace_6874108 : CollatzResearch.WordTrace tailWord_6874108 prefixEnd_6874108 3529721474916896254536559 := by
  unfold tailWord_6874108
  simp only [CollatzResearch.WordTrace]
  refine ⟨125359658090144097512131489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167146210786858796682841985 125359658090144097512131489)
  ·
    refine ⟨94019743567608073134098617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125359658090144097512131489 94019743567608073134098617)
    ·
      refine ⟨70514807675706054850573963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94019743567608073134098617 70514807675706054850573963)
      ·
        refine ⟨105772211513559082275860945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70514807675706054850573963 105772211513559082275860945)
        ·
          refine ⟨79329158635169311706895709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105772211513559082275860945 79329158635169311706895709)
          ·
            refine ⟨29748434488188491890085891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79329158635169311706895709 29748434488188491890085891)
            ·
              refine ⟨44622651732282737835128837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29748434488188491890085891 44622651732282737835128837)
              ·
                refine ⟨8366747199803013344086657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44622651732282737835128837 8366747199803013344086657)
                ·
                  refine ⟨6275060399852260008064993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8366747199803013344086657 6275060399852260008064993)
                  ·
                    refine ⟨4706295299889195006048745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275060399852260008064993 4706295299889195006048745)
                    ·
                      refine ⟨3529721474916896254536559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706295299889195006048745 3529721474916896254536559)
                      ·
                        rfl

theorem cell23_6874108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_6874108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874108 prefixEnd_6874108 := by exact prefixLift 6874108
  have htrace : WordTrace (prefixWord ++ tailWord_6874108) baseStart_6874108 baseEnd_6874108 := by
    simpa [prefixWord, tailWord_6874108, baseEnd_6874108] using wordTrace_append hprefix tailTrace_6874108
  have hstable : (prefixWord ++ tailWord_6874108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874108).length < 2 ^ (prefixWord ++ tailWord_6874108).sum := by decide
  have hdescent : baseEnd_6874108 < baseStart_6874108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874124 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_6874124 : Nat := 118140960795 + 6874124 * 2 ^ 59
def prefixEnd_6874124 : Nat := 4983230072969 + 3 ^ 40 * 6874124 * 2
def baseEnd_6874124 : Nat := 3529729690607368191936485

theorem tailTrace_6874124 : CollatzResearch.WordTrace tailWord_6874124 prefixEnd_6874124 3529729690607368191936485 := by
  unfold tailWord_6874124
  simp only [CollatzResearch.WordTrace]
  refine ⟨125359949874115114878422713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167146599832153486504563617 125359949874115114878422713)
  ·
    refine ⟨94019962405586336158817035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125359949874115114878422713 94019962405586336158817035)
    ·
      refine ⟨141029943608379504238225553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94019962405586336158817035 141029943608379504238225553)
      ·
        refine ⟨105772457706284628178669165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141029943608379504238225553 105772457706284628178669165)
        ·
          refine ⟨39664671639856735567000937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105772457706284628178669165 39664671639856735567000937)
          ·
            refine ⟨29748503729892551675250703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39664671639856735567000937 29748503729892551675250703)
            ·
              refine ⟨44622755594838827512876055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29748503729892551675250703 44622755594838827512876055)
              ·
                refine ⟨66934133392258241269314083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44622755594838827512876055 66934133392258241269314083)
                ·
                  refine ⟨100401200088387361903971125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66934133392258241269314083 100401200088387361903971125)
                  ·
                    refine ⟨9412612508286315178497293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100401200088387361903971125 9412612508286315178497293)
                    ·
                      refine ⟨3529729690607368191936485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412612508286315178497293 3529729690607368191936485)
                      ·
                        rfl

theorem cell23_6874124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_6874124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874124 prefixEnd_6874124 := by exact prefixLift 6874124
  have htrace : WordTrace (prefixWord ++ tailWord_6874124) baseStart_6874124 baseEnd_6874124 := by
    simpa [prefixWord, tailWord_6874124, baseEnd_6874124] using wordTrace_append hprefix tailTrace_6874124
  have hstable : (prefixWord ++ tailWord_6874124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874124).length < 2 ^ (prefixWord ++ tailWord_6874124).sum := by decide
  have hdescent : baseEnd_6874124 < baseStart_6874124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874137 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_6874137 : Nat := 118140960795 + 6874137 * 2 ^ 59
def prefixEnd_6874137 : Nat := 4983230072969 + 3 ^ 40 * 6874137 * 2
def baseEnd_6874137 : Nat := 3529736365855876641073925

theorem tailTrace_6874137 : CollatzResearch.WordTrace tailWord_6874137 prefixEnd_6874137 3529736365855876641073925 := by
  unfold tailWord_6874137
  simp only [CollatzResearch.WordTrace]
  refine ⟨250720373897183132977068665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167146915931455421984712443 250720373897183132977068665)
  ·
    refine ⟨188040280422887349732801499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250720373897183132977068665 188040280422887349732801499)
    ·
      refine ⟨282060420634331024599202249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188040280422887349732801499 282060420634331024599202249)
      ·
        refine ⟨211545315475748268449401687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282060420634331024599202249 211545315475748268449401687)
        ·
          refine ⟨317317973213622402674102531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211545315475748268449401687 317317973213622402674102531)
          ·
            refine ⟨475976959820433604011153797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317317973213622402674102531 475976959820433604011153797)
            ·
              refine ⟨89245679966331300752091337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 475976959820433604011153797 89245679966331300752091337)
              ·
                refine ⟨66934259974748475564068503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89245679966331300752091337 66934259974748475564068503)
                ·
                  refine ⟨100401389962122713346102755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66934259974748475564068503 100401389962122713346102755)
                  ·
                    refine ⟨150602084943184070019154133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100401389962122713346102755 150602084943184070019154133)
                    ·
                      refine ⟨3529736365855876641073925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150602084943184070019154133 3529736365855876641073925)
                      ·
                        rfl

theorem cell23_6874137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_6874137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874137 prefixEnd_6874137 := by exact prefixLift 6874137
  have htrace : WordTrace (prefixWord ++ tailWord_6874137) baseStart_6874137 baseEnd_6874137 := by
    simpa [prefixWord, tailWord_6874137, baseEnd_6874137] using wordTrace_append hprefix tailTrace_6874137
  have hstable : (prefixWord ++ tailWord_6874137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874137).length < 2 ^ (prefixWord ++ tailWord_6874137).sum := by decide
  have hdescent : baseEnd_6874137 < baseStart_6874137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874148 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 5]
def baseStart_6874148 : Nat := 118140960795 + 6874148 * 2 ^ 59
def prefixEnd_6874148 : Nat := 4983230072969 + 3 ^ 40 * 6874148 * 2
def baseEnd_6874148 : Nat := 392193557127008455337375

theorem tailTrace_6874148 : CollatzResearch.WordTrace tailWord_6874148 prefixEnd_6874148 392193557127008455337375 := by
  unfold tailWord_6874148
  simp only [CollatzResearch.WordTrace]
  refine ⟨125360387550071640927859549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167147183400095521237146065 125360387550071640927859549)
  ·
    refine ⟨47010145331276865347947331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125360387550071640927859549 47010145331276865347947331)
    ·
      refine ⟨70515217996915298021920997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47010145331276865347947331 70515217996915298021920997)
      ·
        refine ⟨13221603374421618379110187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70515217996915298021920997 13221603374421618379110187)
        ·
          refine ⟨19832405061632427568665281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13221603374421618379110187 19832405061632427568665281)
          ·
            refine ⟨14874303796224320676498961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19832405061632427568665281 14874303796224320676498961)
            ·
              refine ⟨11155727847168240507374221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14874303796224320676498961 11155727847168240507374221)
              ·
                refine ⟨4183397942688090190265333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11155727847168240507374221 4183397942688090190265333)
                ·
                  refine ⟨392193557127008455337375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4183397942688090190265333 392193557127008455337375)
                  ·
                    rfl

theorem cell23_6874148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_6874148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874148 prefixEnd_6874148 := by exact prefixLift 6874148
  have htrace : WordTrace (prefixWord ++ tailWord_6874148) baseStart_6874148 baseEnd_6874148 := by
    simpa [prefixWord, tailWord_6874148, baseEnd_6874148] using wordTrace_append hprefix tailTrace_6874148
  have hstable : (prefixWord ++ tailWord_6874148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874148).length < 2 ^ (prefixWord ++ tailWord_6874148).sum := by decide
  have hdescent : baseEnd_6874148 < baseStart_6874148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874181 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 2, 4, 2]
def baseStart_6874181 : Nat := 118140960795 + 6874181 * 2 ^ 59
def prefixEnd_6874181 : Nat := 4983230072969 + 3 ^ 40 * 6874181 * 2
def baseEnd_6874181 : Nat := 3529758959004674468923723

theorem tailTrace_6874181 : CollatzResearch.WordTrace tailWord_6874181 prefixEnd_6874181 3529758959004674468923723 := by
  unfold tailWord_6874181
  simp only [CollatzResearch.WordTrace]
  refine ⟨250721978709023728491670397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167147985806015818994446931 250721978709023728491670397)
  ·
    refine ⟨94020742015883898184376399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250721978709023728491670397 94020742015883898184376399)
    ·
      refine ⟨141031113023825847276564599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94020742015883898184376399 141031113023825847276564599)
      ·
        refine ⟨211546669535738770914846899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141031113023825847276564599 211546669535738770914846899)
        ·
          refine ⟨317320004303608156372270349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211546669535738770914846899 317320004303608156372270349)
          ·
            refine ⟨118995001613853058639601381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317320004303608156372270349 118995001613853058639601381)
            ·
              refine ⟨22311562802597448494925259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118995001613853058639601381 22311562802597448494925259)
              ·
                refine ⟨33467344203896172742387889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22311562802597448494925259 33467344203896172742387889)
                ·
                  refine ⟨25100508152922129556790917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33467344203896172742387889 25100508152922129556790917)
                  ·
                    refine ⟨4706345278672899291898297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25100508152922129556790917 4706345278672899291898297)
                    ·
                      refine ⟨3529758959004674468923723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706345278672899291898297 3529758959004674468923723)
                      ·
                        rfl

theorem cell23_6874181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_6874181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874181 prefixEnd_6874181 := by exact prefixLift 6874181
  have htrace : WordTrace (prefixWord ++ tailWord_6874181) baseStart_6874181 baseEnd_6874181 := by
    simpa [prefixWord, tailWord_6874181, baseEnd_6874181] using wordTrace_append hprefix tailTrace_6874181
  have hstable : (prefixWord ++ tailWord_6874181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874181).length < 2 ^ (prefixWord ++ tailWord_6874181).sum := by decide
  have hdescent : baseEnd_6874181 < baseStart_6874181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874184 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_6874184 : Nat := 118140960795 + 6874184 * 2 ^ 59
def prefixEnd_6874184 : Nat := 4983230072969 + 3 ^ 40 * 6874184 * 2
def baseEnd_6874184 : Nat := 3529760499446637957186209

theorem tailTrace_6874184 : CollatzResearch.WordTrace tailWord_6874184 prefixEnd_6874184 3529760499446637957186209 := by
  unfold tailWord_6874184
  simp only [CollatzResearch.WordTrace]
  refine ⟨125361044064006430002014803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167148058752008573336019737 125361044064006430002014803)
  ·
    refine ⟨188041566096009645003022205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125361044064006430002014803 188041566096009645003022205)
    ·
      refine ⟨70515587286003616876133327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188041566096009645003022205 70515587286003616876133327)
      ·
        refine ⟨105773380929005425314199991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70515587286003616876133327 105773380929005425314199991)
        ·
          refine ⟨158660071393508137971299987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105773380929005425314199991 158660071393508137971299987)
          ·
            refine ⟨237990107090262206956949981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158660071393508137971299987 237990107090262206956949981)
            ·
              refine ⟨89246290158848327608856243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237990107090262206956949981 89246290158848327608856243)
              ·
                refine ⟨133869435238272491413284365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89246290158848327608856243 133869435238272491413284365)
                ·
                  refine ⟨50201038214352184279981637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133869435238272491413284365 50201038214352184279981637)
                  ·
                    refine ⟨9412694665191034552496557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50201038214352184279981637 9412694665191034552496557)
                    ·
                      refine ⟨3529760499446637957186209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412694665191034552496557 3529760499446637957186209)
                      ·
                        rfl

theorem cell23_6874184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_6874184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874184 prefixEnd_6874184 := by exact prefixLift 6874184
  have htrace : WordTrace (prefixWord ++ tailWord_6874184) baseStart_6874184 baseEnd_6874184 := by
    simpa [prefixWord, tailWord_6874184, baseEnd_6874184] using wordTrace_append hprefix tailTrace_6874184
  have hstable : (prefixWord ++ tailWord_6874184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874184).length < 2 ^ (prefixWord ++ tailWord_6874184).sum := by decide
  have hdescent : baseEnd_6874184 < baseStart_6874184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874187 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 12]
def baseStart_6874187 : Nat := 118140960795 + 6874187 * 2 ^ 59
def prefixEnd_6874187 : Nat := 4983230072969 + 3 ^ 40 * 6874187 * 2
def baseEnd_6874187 : Nat := 392195782209844605049855

theorem tailTrace_6874187 : CollatzResearch.WordTrace tailWord_6874187 prefixEnd_6874187 392195782209844605049855 := by
  unfold tailWord_6874187
  simp only [CollatzResearch.WordTrace]
  refine ⟨250722197547001991516388815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167148131698001327677592543 250722197547001991516388815)
  ·
    refine ⟨376083296320502987274583223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250722197547001991516388815 376083296320502987274583223)
    ·
      refine ⟨564124944480754480911874835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376083296320502987274583223 564124944480754480911874835)
      ·
        refine ⟨846187416721131721367812253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564124944480754480911874835 846187416721131721367812253)
        ·
          refine ⟨317320281270424395512929595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 846187416721131721367812253 317320281270424395512929595)
          ·
            refine ⟨475980421905636593269394393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317320281270424395512929595 475980421905636593269394393)
            ·
              refine ⟨356985316429227444952045795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475980421905636593269394393 356985316429227444952045795)
              ·
                refine ⟨535477974643841167428068693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356985316429227444952045795 535477974643841167428068693)
                ·
                  refine ⟨392195782209844605049855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 535477974643841167428068693 392195782209844605049855)
                  ·
                    rfl

theorem cell23_6874187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 12].length) (baseStart_6874187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874187 prefixEnd_6874187 := by exact prefixLift 6874187
  have htrace : WordTrace (prefixWord ++ tailWord_6874187) baseStart_6874187 baseEnd_6874187 := by
    simpa [prefixWord, tailWord_6874187, baseEnd_6874187] using wordTrace_append hprefix tailTrace_6874187
  have hstable : (prefixWord ++ tailWord_6874187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874187).length < 2 ^ (prefixWord ++ tailWord_6874187).sum := by decide
  have hdescent : baseEnd_6874187 < baseStart_6874187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874204 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 10]
def baseStart_6874204 : Nat := 118140960795 + 6874204 * 2 ^ 59
def prefixEnd_6874204 : Nat := 4983230072969 + 3 ^ 40 * 6874204 * 2
def baseEnd_6874204 : Nat := 392196752117747542104013

theorem tailTrace_6874204 : CollatzResearch.WordTrace tailWord_6874204 prefixEnd_6874204 392196752117747542104013 := by
  unfold tailWord_6874204
  simp only [CollatzResearch.WordTrace]
  refine ⟨125361408793970201709878833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167148545058626935613171777 125361408793970201709878833)
  ·
    refine ⟨94021056595477651282409125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125361408793970201709878833 94021056595477651282409125)
    ·
      refine ⟨17628948111652059615451711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94021056595477651282409125 17628948111652059615451711)
      ·
        refine ⟨26443422167478089423177567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17628948111652059615451711 26443422167478089423177567)
        ·
          refine ⟨39665133251217134134766351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26443422167478089423177567 39665133251217134134766351)
          ·
            refine ⟨59497699876825701202149527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39665133251217134134766351 59497699876825701202149527)
            ·
              refine ⟨89246549815238551803224291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59497699876825701202149527 89246549815238551803224291)
              ·
                refine ⟨133869824722857827704836437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89246549815238551803224291 133869824722857827704836437)
                ·
                  refine ⟨392196752117747542104013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133869824722857827704836437 392196752117747542104013)
                  ·
                    rfl

theorem cell23_6874204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_6874204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874204 prefixEnd_6874204 := by exact prefixLift 6874204
  have htrace : WordTrace (prefixWord ++ tailWord_6874204) baseStart_6874204 baseEnd_6874204 := by
    simpa [prefixWord, tailWord_6874204, baseEnd_6874204] using wordTrace_append hprefix tailTrace_6874204
  have hstable : (prefixWord ++ tailWord_6874204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874204).length < 2 ^ (prefixWord ++ tailWord_6874204).sum := by decide
  have hdescent : baseEnd_6874204 < baseStart_6874204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874218 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_6874218 : Nat := 118140960795 + 6874218 * 2 ^ 59
def prefixEnd_6874218 : Nat := 4983230072969 + 3 ^ 40 * 6874218 * 2
def baseEnd_6874218 : Nat := 3529777957788890824161053

theorem tailTrace_6874218 : CollatzResearch.WordTrace tailWord_6874218 prefixEnd_6874218 3529777957788890824161053 := by
  unfold tailWord_6874218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62680832052472420952691827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167148885473259789207178205 62680832052472420952691827)
  ·
    refine ⟨94021248078708631429037741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62680832052472420952691827 94021248078708631429037741)
    ·
      refine ⟨35257968029515736785889153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94021248078708631429037741 35257968029515736785889153)
      ·
        refine ⟨26443476022136802589416865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35257968029515736785889153 26443476022136802589416865)
        ·
          refine ⟨19832607016602601942062649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26443476022136802589416865 19832607016602601942062649)
          ·
            refine ⟨14874455262451951456546987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19832607016602601942062649 14874455262451951456546987)
            ·
              refine ⟨22311682893677927184820481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14874455262451951456546987 22311682893677927184820481)
              ·
                refine ⟨16733762170258445388615361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22311682893677927184820481 16733762170258445388615361)
                ·
                  refine ⟨12550321627693834041461521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16733762170258445388615361 12550321627693834041461521)
                  ·
                    refine ⟨9412741220770375531096141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12550321627693834041461521 9412741220770375531096141)
                    ·
                      refine ⟨3529777957788890824161053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412741220770375531096141 3529777957788890824161053)
                      ·
                        rfl

theorem cell23_6874218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_6874218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874218 prefixEnd_6874218 := by exact prefixLift 6874218
  have htrace : WordTrace (prefixWord ++ tailWord_6874218) baseStart_6874218 baseEnd_6874218 := by
    simpa [prefixWord, tailWord_6874218, baseEnd_6874218] using wordTrace_append hprefix tailTrace_6874218
  have hstable : (prefixWord ++ tailWord_6874218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874218).length < 2 ^ (prefixWord ++ tailWord_6874218).sum := by decide
  have hdescent : baseEnd_6874218 < baseStart_6874218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874284 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_6874284 : Nat := 118140960795 + 6874284 * 2 ^ 59
def prefixEnd_6874284 : Nat := 4983230072969 + 3 ^ 40 * 6874284 * 2
def baseEnd_6874284 : Nat := 3529811847512087565935749

theorem tailTrace_6874284 : CollatzResearch.WordTrace tailWord_6874284 prefixEnd_6874284 3529811847512087565935749 := by
  unfold tailWord_6874284
  simp only [CollatzResearch.WordTrace]
  refine ⟨125362867713825288541334953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167150490285100384721779937 125362867713825288541334953)
  ·
    refine ⟨94022150785368966406001215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125362867713825288541334953 94022150785368966406001215)
    ·
      refine ⟨141033226178053449609001823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94022150785368966406001215 141033226178053449609001823)
      ·
        refine ⟨211549839267080174413502735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141033226178053449609001823 211549839267080174413502735)
        ·
          refine ⟨317324758900620261620254103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211549839267080174413502735 317324758900620261620254103)
          ·
            refine ⟨475987138350930392430381155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317324758900620261620254103 475987138350930392430381155)
            ·
              refine ⟨713980707526395588645571733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475987138350930392430381155 713980707526395588645571733)
              ·
                refine ⟨33467845665299793217761175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 713980707526395588645571733 33467845665299793217761175)
                ·
                  refine ⟨50201768497949689826641763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33467845665299793217761175 50201768497949689826641763)
                  ·
                    refine ⟨75302652746924534739962645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50201768497949689826641763 75302652746924534739962645)
                    ·
                      refine ⟨3529811847512087565935749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75302652746924534739962645 3529811847512087565935749)
                      ·
                        rfl

theorem cell23_6874284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_6874284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874284 prefixEnd_6874284 := by exact prefixLift 6874284
  have htrace : WordTrace (prefixWord ++ tailWord_6874284) baseStart_6874284 baseEnd_6874284 := by
    simpa [prefixWord, tailWord_6874284, baseEnd_6874284] using wordTrace_append hprefix tailTrace_6874284
  have hstable : (prefixWord ++ tailWord_6874284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874284).length < 2 ^ (prefixWord ++ tailWord_6874284).sum := by decide
  have hdescent : baseEnd_6874284 < baseStart_6874284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874291 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3]
def baseStart_6874291 : Nat := 118140960795 + 6874291 * 2 ^ 59
def prefixEnd_6874291 : Nat := 4983230072969 + 3 ^ 40 * 6874291 * 2
def baseEnd_6874291 : Nat := 3529815441876669038548217

theorem tailTrace_6874291 : CollatzResearch.WordTrace tailWord_6874291 prefixEnd_6874291 3529815441876669038548217 := by
  unfold tailWord_6874291
  simp only [CollatzResearch.WordTrace]
  refine ⟨250725990738625217278174727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167150660492416811518783151 250725990738625217278174727)
  ·
    refine ⟨376088986107937825917262091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250725990738625217278174727 376088986107937825917262091)
    ·
      refine ⟨564133479161906738875893137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376088986107937825917262091 564133479161906738875893137)
      ·
        refine ⟨423100109371430054156919853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564133479161906738875893137 423100109371430054156919853)
        ·
          refine ⟨158662541014286270308844945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423100109371430054156919853 158662541014286270308844945)
          ·
            refine ⟨118996905760714702731633709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158662541014286270308844945 118996905760714702731633709)
            ·
              refine ⟨44623839660268013524362641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118996905760714702731633709 44623839660268013524362641)
              ·
                refine ⟨33467879745201010143271981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44623839660268013524362641 33467879745201010143271981)
                ·
                  refine ⟨12550454904450378803726993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33467879745201010143271981 12550454904450378803726993)
                  ·
                    refine ⟨9412841178337784102795245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12550454904450378803726993 9412841178337784102795245)
                    ·
                      refine ⟨3529815441876669038548217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412841178337784102795245 3529815441876669038548217)
                      ·
                        rfl

theorem cell23_6874291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_6874291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874291 prefixEnd_6874291 := by exact prefixLift 6874291
  have htrace : WordTrace (prefixWord ++ tailWord_6874291) baseStart_6874291 baseEnd_6874291 := by
    simpa [prefixWord, tailWord_6874291, baseEnd_6874291] using wordTrace_append hprefix tailTrace_6874291
  have hstable : (prefixWord ++ tailWord_6874291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874291).length < 2 ^ (prefixWord ++ tailWord_6874291).sum := by decide
  have hdescent : baseEnd_6874291 < baseStart_6874291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874301 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6874301 : Nat := 118140960795 + 6874301 * 2 ^ 59
def prefixEnd_6874301 : Nat := 4983230072969 + 3 ^ 40 * 6874301 * 2
def baseEnd_6874301 : Nat := 3529820576683213999423171

theorem tailTrace_6874301 : CollatzResearch.WordTrace tailWord_6874301 prefixEnd_6874301 3529820576683213999423171 := by
  unfold tailWord_6874301
  simp only [CollatzResearch.WordTrace]
  refine ⟨250726355468588988986038757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167150903645725992657359171 250726355468588988986038757)
  ·
    refine ⟨47011191650360435434882267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250726355468588988986038757 47011191650360435434882267)
    ·
      refine ⟨70516787475540653152323401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47011191650360435434882267 70516787475540653152323401)
      ·
        refine ⟨52887590606655489864242551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70516787475540653152323401 52887590606655489864242551)
        ·
          refine ⟨79331385909983234796363827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52887590606655489864242551 79331385909983234796363827)
          ·
            refine ⟨118997078864974852194545741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79331385909983234796363827 118997078864974852194545741)
            ·
              refine ⟨44623904574365569572954653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118997078864974852194545741 44623904574365569572954653)
              ·
                refine ⟨16733964215387088589857995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44623904574365569572954653 16733964215387088589857995)
                ·
                  refine ⟨25100946323080632884786993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16733964215387088589857995 25100946323080632884786993)
                  ·
                    refine ⟨18825709742310474663590245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25100946323080632884786993 18825709742310474663590245)
                    ·
                      refine ⟨3529820576683213999423171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18825709742310474663590245 3529820576683213999423171)
                      ·
                        rfl

theorem cell23_6874301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6874301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874301 prefixEnd_6874301 := by exact prefixLift 6874301
  have htrace : WordTrace (prefixWord ++ tailWord_6874301) baseStart_6874301 baseEnd_6874301 := by
    simpa [prefixWord, tailWord_6874301, baseEnd_6874301] using wordTrace_append hprefix tailTrace_6874301
  have hstable : (prefixWord ++ tailWord_6874301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874301).length < 2 ^ (prefixWord ++ tailWord_6874301).sum := by decide
  have hdescent : baseEnd_6874301 < baseStart_6874301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874325 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6874325 : Nat := 118140960795 + 6874325 * 2 ^ 59
def prefixEnd_6874325 : Nat := 4983230072969 + 3 ^ 40 * 6874325 * 2
def baseEnd_6874325 : Nat := 3529832900218921905523061

theorem tailTrace_6874325 : CollatzResearch.WordTrace tailWord_6874325 prefixEnd_6874325 3529832900218921905523061 := by
  unfold tailWord_6874325
  simp only [CollatzResearch.WordTrace]
  refine ⟨250727230820502041084912429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167151487213668027389941619 250727230820502041084912429)
  ·
    refine ⟨94022711557688265406842161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250727230820502041084912429 94022711557688265406842161)
    ·
      refine ⟨70517033668266199055131621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94022711557688265406842161 70517033668266199055131621)
      ·
        refine ⟨13221943812799912322837179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70517033668266199055131621 13221943812799912322837179)
        ·
          refine ⟨19832915719199868484255769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13221943812799912322837179 19832915719199868484255769)
          ·
            refine ⟨14874686789399901363191827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19832915719199868484255769 14874686789399901363191827)
            ·
              refine ⟨22312030184099852044787741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14874686789399901363191827 22312030184099852044787741)
              ·
                refine ⟨8367011319037444516795403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22312030184099852044787741 8367011319037444516795403)
                ·
                  refine ⟨12550516978556166775193105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8367011319037444516795403 12550516978556166775193105)
                  ·
                    refine ⟨9412887733917125081394829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12550516978556166775193105 9412887733917125081394829)
                    ·
                      refine ⟨3529832900218921905523061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9412887733917125081394829 3529832900218921905523061)
                      ·
                        rfl

theorem cell23_6874325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6874325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874325 prefixEnd_6874325 := by exact prefixLift 6874325
  have htrace : WordTrace (prefixWord ++ tailWord_6874325) baseStart_6874325 baseEnd_6874325 := by
    simpa [prefixWord, tailWord_6874325, baseEnd_6874325] using wordTrace_append hprefix tailTrace_6874325
  have hstable : (prefixWord ++ tailWord_6874325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874325).length < 2 ^ (prefixWord ++ tailWord_6874325).sum := by decide
  have hdescent : baseEnd_6874325 < baseStart_6874325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874331 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 9, 2]
def baseStart_6874331 : Nat := 118140960795 + 6874331 * 2 ^ 59
def prefixEnd_6874331 : Nat := 4983230072969 + 3 ^ 40 * 6874331 * 2
def baseEnd_6874331 : Nat := 3529835981102848882048033

theorem tailTrace_6874331 : CollatzResearch.WordTrace tailWord_6874331 prefixEnd_6874331 3529835981102848882048033 := by
  unfold tailWord_6874331
  simp only [CollatzResearch.WordTrace]
  refine ⟨250727449658480304109630847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167151633105653536073087231 250727449658480304109630847)
  ·
    refine ⟨376091174487720456164446271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250727449658480304109630847 376091174487720456164446271)
    ·
      refine ⟨564136761731580684246669407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376091174487720456164446271 564136761731580684246669407)
      ·
        refine ⟨846205142597371026370004111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564136761731580684246669407 846205142597371026370004111)
        ·
          refine ⟨1269307713896056539555006167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846205142597371026370004111 1269307713896056539555006167)
          ·
            refine ⟨1903961570844084809332509251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269307713896056539555006167 1903961570844084809332509251)
            ·
              refine ⟨2855942356266127213998763877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903961570844084809332509251 2855942356266127213998763877)
              ·
                refine ⟨535489191799898852624768227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2855942356266127213998763877 535489191799898852624768227)
                ·
                  refine ⟨803233787699848278937152341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535489191799898852624768227 803233787699848278937152341)
                  ·
                    refine ⟨4706447974803798509397377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 803233787699848278937152341 4706447974803798509397377)
                    ·
                      refine ⟨3529835981102848882048033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706447974803798509397377 3529835981102848882048033)
                      ·
                        rfl

theorem cell23_6874331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9, 2].length) (baseStart_6874331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874331 prefixEnd_6874331 := by exact prefixLift 6874331
  have htrace : WordTrace (prefixWord ++ tailWord_6874331) baseStart_6874331 baseEnd_6874331 := by
    simpa [prefixWord, tailWord_6874331, baseEnd_6874331] using wordTrace_append hprefix tailTrace_6874331
  have hstable : (prefixWord ++ tailWord_6874331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874331).length < 2 ^ (prefixWord ++ tailWord_6874331).sum := by decide
  have hdescent : baseEnd_6874331 < baseStart_6874331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874378 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_6874378 : Nat := 118140960795 + 6874378 * 2 ^ 59
def prefixEnd_6874378 : Nat := 4983230072969 + 3 ^ 40 * 6874378 * 2
def baseEnd_6874378 : Nat := 3529860114693610198160317

theorem tailTrace_6874378 : CollatzResearch.WordTrace tailWord_6874378 prefixEnd_6874378 3529860114693610198160317 := by
  unfold tailWord_6874378
  simp only [CollatzResearch.WordTrace]
  refine ⟨62682290972327507784147947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167152775926206687424394525 62682290972327507784147947)
  ·
    refine ⟨94023436458491261676221921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62682290972327507784147947 94023436458491261676221921)
    ·
      refine ⟨70517577343868446257166441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94023436458491261676221921 70517577343868446257166441)
      ·
        refine ⟨52888183007901334692874831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70517577343868446257166441 52888183007901334692874831)
        ·
          refine ⟨79332274511852002039312247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52888183007901334692874831 79332274511852002039312247)
          ·
            refine ⟨118998411767778003058968371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79332274511852002039312247 118998411767778003058968371)
            ·
              refine ⟨178497617651667004588452557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118998411767778003058968371 178497617651667004588452557)
              ·
                refine ⟨66936606619375126720669709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178497617651667004588452557 66936606619375126720669709)
                ·
                  refine ⟨25101227482265672520251141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66936606619375126720669709 25101227482265672520251141)
                  ·
                    refine ⟨4706480152924813597547089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25101227482265672520251141 4706480152924813597547089)
                    ·
                      refine ⟨3529860114693610198160317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706480152924813597547089 3529860114693610198160317)
                      ·
                        rfl

theorem cell23_6874378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_6874378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874378 prefixEnd_6874378 := by exact prefixLift 6874378
  have htrace : WordTrace (prefixWord ++ tailWord_6874378) baseStart_6874378 baseEnd_6874378 := by
    simpa [prefixWord, tailWord_6874378, baseEnd_6874378] using wordTrace_append hprefix tailTrace_6874378
  have hstable : (prefixWord ++ tailWord_6874378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874378).length < 2 ^ (prefixWord ++ tailWord_6874378).sum := by decide
  have hdescent : baseEnd_6874378 < baseStart_6874378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874395 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 2, 2, 2]
def baseStart_6874395 : Nat := 118140960795 + 6874395 * 2 ^ 59
def prefixEnd_6874395 : Nat := 4983230072969 + 3 ^ 40 * 6874395 * 2
def baseEnd_6874395 : Nat := 3529868843864736631647739

theorem tailTrace_6874395 : CollatzResearch.WordTrace tailWord_6874395 prefixEnd_6874395 3529868843864736631647739 := by
  unfold tailWord_6874395
  simp only [CollatzResearch.WordTrace]
  refine ⟨250729783930248443039960639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167153189286832295359973759 250729783930248443039960639)
  ·
    refine ⟨376094675895372664559940959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250729783930248443039960639 376094675895372664559940959)
    ·
      refine ⟨564142013843058996839911439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376094675895372664559940959 564142013843058996839911439)
      ·
        refine ⟨846213020764588495259867159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564142013843058996839911439 846213020764588495259867159)
        ·
          refine ⟨1269319531146882742889800739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846213020764588495259867159 1269319531146882742889800739)
          ·
            refine ⟨1903979296720324114334701109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269319531146882742889800739 1903979296720324114334701109)
            ·
              refine ⟨178498059067530385718878229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1903979296720324114334701109 178498059067530385718878229)
              ·
                refine ⟨8367096518790486830572417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178498059067530385718878229 8367096518790486830572417)
                ·
                  refine ⟨6275322389092865122929313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367096518790486830572417 6275322389092865122929313)
                  ·
                    refine ⟨4706491791819648842196985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275322389092865122929313 4706491791819648842196985)
                    ·
                      refine ⟨3529868843864736631647739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706491791819648842196985 3529868843864736631647739)
                      ·
                        rfl

theorem cell23_6874395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 2, 2].length) (baseStart_6874395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874395 prefixEnd_6874395 := by exact prefixLift 6874395
  have htrace : WordTrace (prefixWord ++ tailWord_6874395) baseStart_6874395 baseEnd_6874395 := by
    simpa [prefixWord, tailWord_6874395, baseEnd_6874395] using wordTrace_append hprefix tailTrace_6874395
  have hstable : (prefixWord ++ tailWord_6874395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874395).length < 2 ^ (prefixWord ++ tailWord_6874395).sum := by decide
  have hdescent : baseEnd_6874395 < baseStart_6874395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874441 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_6874441 : Nat := 118140960795 + 6874441 * 2 ^ 59
def prefixEnd_6874441 : Nat := 4983230072969 + 3 ^ 40 * 6874441 * 2
def baseEnd_6874441 : Nat := 3529892463974843451672527

theorem tailTrace_6874441 : CollatzResearch.WordTrace tailWord_6874441 prefixEnd_6874441 3529892463974843451672527 := by
  unfold tailWord_6874441
  simp only [CollatzResearch.WordTrace]
  refine ⟨250731461688081792896135177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167154307792054528597423451 250731461688081792896135177)
  ·
    refine ⟨188048596266061344672101383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250731461688081792896135177 188048596266061344672101383)
    ·
      refine ⟨282072894399092017008152075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188048596266061344672101383 282072894399092017008152075)
      ·
        refine ⟨423109341598638025512228113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282072894399092017008152075 423109341598638025512228113)
        ·
          refine ⟨317332006198978519134171085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423109341598638025512228113 317332006198978519134171085)
          ·
            refine ⟨118999502324616944675314157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317332006198978519134171085 118999502324616944675314157)
            ·
              refine ⟨44624813371731354253242809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118999502324616944675314157 44624813371731354253242809)
              ·
                refine ⟨33468610028798515689932107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44624813371731354253242809 33468610028798515689932107)
                ·
                  refine ⟨50202915043197773534898161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33468610028798515689932107 50202915043197773534898161)
                  ·
                    refine ⟨37652186282398330151173621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50202915043197773534898161 37652186282398330151173621)
                    ·
                      refine ⟨3529892463974843451672527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37652186282398330151173621 3529892463974843451672527)
                      ·
                        rfl

theorem cell23_6874441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_6874441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874441 prefixEnd_6874441 := by exact prefixLift 6874441
  have htrace : WordTrace (prefixWord ++ tailWord_6874441) baseStart_6874441 baseEnd_6874441 := by
    simpa [prefixWord, tailWord_6874441, baseEnd_6874441] using wordTrace_append hprefix tailTrace_6874441
  have hstable : (prefixWord ++ tailWord_6874441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874441).length < 2 ^ (prefixWord ++ tailWord_6874441).sum := by decide
  have hdescent : baseEnd_6874441 < baseStart_6874441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874485 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_6874485 : Nat := 118140960795 + 6874485 * 2 ^ 59
def prefixEnd_6874485 : Nat := 4983230072969 + 3 ^ 40 * 6874485 * 2
def baseEnd_6874485 : Nat := 3529915057123641279522325

theorem tailTrace_6874485 : CollatzResearch.WordTrace tailWord_6874485 prefixEnd_6874485 3529915057123641279522325 := by
  unfold tailWord_6874485
  simp only [CollatzResearch.WordTrace]
  refine ⟨250733066499922388410736909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167155377666614925607157939 250733066499922388410736909)
  ·
    refine ⟨94024899937470895654026341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250733066499922388410736909 94024899937470895654026341)
    ·
      refine ⟨17629668738275792935129939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94024899937470895654026341 17629668738275792935129939)
      ·
        refine ⟨26444503107413689402694909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17629668738275792935129939 26444503107413689402694909)
        ·
          refine ⟨9916688665280133526010591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26444503107413689402694909 9916688665280133526010591)
          ·
            refine ⟨14875032997920200289015887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9916688665280133526010591 14875032997920200289015887)
            ·
              refine ⟨22312549496880300433523831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14875032997920200289015887 22312549496880300433523831)
              ·
                refine ⟨33468824245320450650285747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22312549496880300433523831 33468824245320450650285747)
                ·
                  refine ⟨50203236367980675975428621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33468824245320450650285747 50203236367980675975428621)
                  ·
                    refine ⟨18826213637992753490785733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50203236367980675975428621 18826213637992753490785733)
                    ·
                      refine ⟨3529915057123641279522325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18826213637992753490785733 3529915057123641279522325)
                      ·
                        rfl

theorem cell23_6874485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_6874485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874485 prefixEnd_6874485 := by exact prefixLift 6874485
  have htrace : WordTrace (prefixWord ++ tailWord_6874485) baseStart_6874485 baseEnd_6874485 := by
    simpa [prefixWord, tailWord_6874485, baseEnd_6874485] using wordTrace_append hprefix tailTrace_6874485
  have hstable : (prefixWord ++ tailWord_6874485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874485).length < 2 ^ (prefixWord ++ tailWord_6874485).sum := by decide
  have hdescent : baseEnd_6874485 < baseStart_6874485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874491 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 8]
def baseStart_6874491 : Nat := 118140960795 + 6874491 * 2 ^ 59
def prefixEnd_6874491 : Nat := 4983230072969 + 3 ^ 40 * 6874491 * 2
def baseEnd_6874491 : Nat := 392213126445285361783033

theorem tailTrace_6874491 : CollatzResearch.WordTrace tailWord_6874491 prefixEnd_6874491 392213126445285361783033 := by
  unfold tailWord_6874491
  simp only [CollatzResearch.WordTrace]
  refine ⟨250733285337900651435455327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167155523558600434290303551 250733285337900651435455327)
  ·
    refine ⟨376099928006850977153182991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250733285337900651435455327 376099928006850977153182991)
    ·
      refine ⟨564149892010276465729774487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376099928006850977153182991 564149892010276465729774487)
      ·
        refine ⟨846224838015414698594661731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564149892010276465729774487 846224838015414698594661731)
        ·
          refine ⟨1269337257023122047891992597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846224838015414698594661731 1269337257023122047891992597)
          ·
            refine ⟨59500183922958845994937153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1269337257023122047891992597 59500183922958845994937153)
            ·
              refine ⟨44625137942219134496202865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59500183922958845994937153 44625137942219134496202865)
              ·
                refine ⟨33468853456664350872152149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44625137942219134496202865 33468853456664350872152149)
                ·
                  refine ⟨392213126445285361783033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33468853456664350872152149 392213126445285361783033)
                  ·
                    rfl

theorem cell23_6874491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 8].length) (baseStart_6874491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874491 prefixEnd_6874491 := by exact prefixLift 6874491
  have htrace : WordTrace (prefixWord ++ tailWord_6874491) baseStart_6874491 baseEnd_6874491 := by
    simpa [prefixWord, tailWord_6874491, baseEnd_6874491] using wordTrace_append hprefix tailTrace_6874491
  have hstable : (prefixWord ++ tailWord_6874491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874491).length < 2 ^ (prefixWord ++ tailWord_6874491).sum := by decide
  have hdescent : baseEnd_6874491 < baseStart_6874491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874545 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 1, 5, 2]
def baseStart_6874545 : Nat := 118140960795 + 6874545 * 2 ^ 59
def prefixEnd_6874545 : Nat := 4983230072969 + 3 ^ 40 * 6874545 * 2
def baseEnd_6874545 : Nat := 3529945865962911044772049

theorem tailTrace_6874545 : CollatzResearch.WordTrace tailWord_6874545 prefixEnd_6874545 3529945865962911044772049 := by
  unfold tailWord_6874545
  simp only [CollatzResearch.WordTrace]
  refine ⟨250735254879705018657921089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167156836586470012438614059 250735254879705018657921089)
  ·
    refine ⟨188051441159778763993440817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250735254879705018657921089 188051441159778763993440817)
    ·
      refine ⟨141038580869834072995080613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188051441159778763993440817 141038580869834072995080613)
      ·
        refine ⟨26444733913093888686577615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141038580869834072995080613 26444733913093888686577615)
        ·
          refine ⟨39667100869640833029866423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26444733913093888686577615 39667100869640833029866423)
          ·
            refine ⟨59500651304461249544799635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39667100869640833029866423 59500651304461249544799635)
            ·
              refine ⟨89250976956691874317199453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59500651304461249544799635 89250976956691874317199453)
              ·
                refine ⟨33469116358759452868949795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89250976956691874317199453 33469116358759452868949795)
                ·
                  refine ⟨50203674538139179303424693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33469116358759452868949795 50203674538139179303424693)
                  ·
                    refine ⟨4706594487950548059696065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50203674538139179303424693 4706594487950548059696065)
                    ·
                      refine ⟨3529945865962911044772049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706594487950548059696065 3529945865962911044772049)
                      ·
                        rfl

theorem cell23_6874545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_6874545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874545 prefixEnd_6874545 := by exact prefixLift 6874545
  have htrace : WordTrace (prefixWord ++ tailWord_6874545) baseStart_6874545 baseEnd_6874545 := by
    simpa [prefixWord, tailWord_6874545, baseEnd_6874545] using wordTrace_append hprefix tailTrace_6874545
  have hstable : (prefixWord ++ tailWord_6874545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874545).length < 2 ^ (prefixWord ++ tailWord_6874545).sum := by decide
  have hdescent : baseEnd_6874545 < baseStart_6874545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874652 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6874652 : Nat := 118140960795 + 6874652 * 2 ^ 59
def prefixEnd_6874652 : Nat := 4983230072969 + 3 ^ 40 * 6874652 * 2
def baseEnd_6874652 : Nat := 3530000808392942126134057

theorem tailTrace_6874652 : CollatzResearch.WordTrace tailWord_6874652 prefixEnd_6874652 3530000808392942126134057 := by
  unfold tailWord_6874652
  simp only [CollatzResearch.WordTrace]
  refine ⟨125369578745158687966033105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167159438326878250621377473 125369578745158687966033105)
  ·
    refine ⟨94027184058869015974524829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125369578745158687966033105 94027184058869015974524829)
    ·
      refine ⟨35260194022075880990446811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94027184058869015974524829 35260194022075880990446811)
      ·
        refine ⟨52890291033113821485670217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35260194022075880990446811 52890291033113821485670217)
        ·
          refine ⟨39667718274835366114252663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52890291033113821485670217 39667718274835366114252663)
          ·
            refine ⟨59501577412253049171378995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39667718274835366114252663 59501577412253049171378995)
            ·
              refine ⟨89252366118379573757068493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59501577412253049171378995 89252366118379573757068493)
              ·
                refine ⟨33469637294392340158900685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89252366118379573757068493 33469637294392340158900685)
                ·
                  refine ⟨12551113985397127559587757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33469637294392340158900685 12551113985397127559587757)
                  ·
                    refine ⟨4706667744523922834845409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12551113985397127559587757 4706667744523922834845409)
                    ·
                      refine ⟨3530000808392942126134057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706667744523922834845409 3530000808392942126134057)
                      ·
                        rfl

theorem cell23_6874652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6874652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874652 prefixEnd_6874652 := by exact prefixLift 6874652
  have htrace : WordTrace (prefixWord ++ tailWord_6874652) baseStart_6874652 baseEnd_6874652 := by
    simpa [prefixWord, tailWord_6874652, baseEnd_6874652] using wordTrace_append hprefix tailTrace_6874652
  have hstable : (prefixWord ++ tailWord_6874652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874652).length < 2 ^ (prefixWord ++ tailWord_6874652).sum := by decide
  have hdescent : baseEnd_6874652 < baseStart_6874652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874745 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6874745 : Nat := 118140960795 + 6874745 * 2 ^ 59
def prefixEnd_6874745 : Nat := 4983230072969 + 3 ^ 40 * 6874745 * 2
def baseEnd_6874745 : Nat := 3530048562093810262271129

theorem tailTrace_6874745 : CollatzResearch.WordTrace tailWord_6874745 prefixEnd_6874745 3530048562093810262271129 := by
  unfold tailWord_6874745
  simp only [CollatzResearch.WordTrace]
  refine ⟨250742549478980452815201689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167161699652653635210134459 250742549478980452815201689)
  ·
    refine ⟨188056912109235339611401267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250742549478980452815201689 188056912109235339611401267)
    ·
      refine ⟨282085368163853009417101901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188056912109235339611401267 282085368163853009417101901)
      ·
        refine ⟨105782013061444878531413213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282085368163853009417101901 105782013061444878531413213)
        ·
          refine ⟨39668254898041829449279955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105782013061444878531413213 39668254898041829449279955)
          ·
            refine ⟨59502382347062744173919933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39668254898041829449279955 59502382347062744173919933)
            ·
              refine ⟨22313393380148529065219975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59502382347062744173919933 22313393380148529065219975)
              ·
                refine ⟨33470090070222793597829963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22313393380148529065219975 33470090070222793597829963)
                ·
                  refine ⟨50205135105334190396744945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33470090070222793597829963 50205135105334190396744945)
                  ·
                    refine ⟨37653851329000642797558709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50205135105334190396744945 37653851329000642797558709)
                    ·
                      refine ⟨3530048562093810262271129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37653851329000642797558709 3530048562093810262271129)
                      ·
                        rfl

theorem cell23_6874745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6874745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874745 prefixEnd_6874745 := by exact prefixLift 6874745
  have htrace : WordTrace (prefixWord ++ tailWord_6874745) baseStart_6874745 baseEnd_6874745 := by
    simpa [prefixWord, tailWord_6874745, baseEnd_6874745] using wordTrace_append hprefix tailTrace_6874745
  have hstable : (prefixWord ++ tailWord_6874745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874745).length < 2 ^ (prefixWord ++ tailWord_6874745).sum := by decide
  have hdescent : baseEnd_6874745 < baseStart_6874745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874755 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 4]
def baseStart_6874755 : Nat := 118140960795 + 6874755 * 2 ^ 59
def prefixEnd_6874755 : Nat := 4983230072969 + 3 ^ 40 * 6874755 * 2
def baseEnd_6874755 : Nat := 3530053696900355223146083

theorem tailTrace_6874755 : CollatzResearch.WordTrace tailWord_6874755 prefixEnd_6874755 3530053696900355223146083 := by
  unfold tailWord_6874755
  simp only [CollatzResearch.WordTrace]
  refine ⟨250742914208944224523065719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167161942805962816348710479 250742914208944224523065719)
  ·
    refine ⟨376114371313416336784598579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250742914208944224523065719 376114371313416336784598579)
    ·
      refine ⟨564171556970124505176897869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376114371313416336784598579 564171556970124505176897869)
      ·
        refine ⟨211564333863796689441336701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564171556970124505176897869 211564333863796689441336701)
        ·
          refine ⟨79336625198923758540501263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211564333863796689441336701 79336625198923758540501263)
          ·
            refine ⟨119004937798385637810751895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79336625198923758540501263 119004937798385637810751895)
            ·
              refine ⟨178507406697578456716127843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119004937798385637810751895 178507406697578456716127843)
              ·
                refine ⟨267761110046367685074191765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178507406697578456716127843 267761110046367685074191765)
                ·
                  refine ⟨12551302033423485237852739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267761110046367685074191765 12551302033423485237852739)
                  ·
                    refine ⟨18826953050135227856779109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12551302033423485237852739 18826953050135227856779109)
                    ·
                      refine ⟨3530053696900355223146083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18826953050135227856779109 3530053696900355223146083)
                      ·
                        rfl

theorem cell23_6874755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_6874755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874755 prefixEnd_6874755 := by exact prefixLift 6874755
  have htrace : WordTrace (prefixWord ++ tailWord_6874755) baseStart_6874755 baseEnd_6874755 := by
    simpa [prefixWord, tailWord_6874755, baseEnd_6874755] using wordTrace_append hprefix tailTrace_6874755
  have hstable : (prefixWord ++ tailWord_6874755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874755).length < 2 ^ (prefixWord ++ tailWord_6874755).sum := by decide
  have hdescent : baseEnd_6874755 < baseStart_6874755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874799 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 1, 4]
def baseStart_6874799 : Nat := 118140960795 + 6874799 * 2 ^ 59
def prefixEnd_6874799 : Nat := 4983230072969 + 3 ^ 40 * 6874799 * 2
def baseEnd_6874799 : Nat := 1176692096683051016998627

theorem tailTrace_6874799 : CollatzResearch.WordTrace tailWord_6874799 prefixEnd_6874799 1176692096683051016998627 := by
  unfold tailWord_6874799
  simp only [CollatzResearch.WordTrace]
  refine ⟨250744519020784820037667451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167163012680523213358444967 250744519020784820037667451)
  ·
    refine ⟨376116778531177230056501177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250744519020784820037667451 376116778531177230056501177)
    ·
      refine ⟨282087583898382922542375883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376116778531177230056501177 282087583898382922542375883)
      ·
        refine ⟨423131375847574383813563825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282087583898382922542375883 423131375847574383813563825)
        ·
          refine ⟨317348531885680787860172869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423131375847574383813563825 317348531885680787860172869)
          ·
            refine ⟨59502849728565147723782413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317348531885680787860172869 59502849728565147723782413)
            ·
              refine ⟨22313568648211930396418405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59502849728565147723782413 22313568648211930396418405)
              ·
                refine ⟨4183794121539736949328451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22313568648211930396418405 4183794121539736949328451)
                ·
                  refine ⟨6275691182309605423992677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4183794121539736949328451 6275691182309605423992677)
                  ·
                    refine ⟨1176692096683051016998627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6275691182309605423992677 1176692096683051016998627)
                    ·
                      rfl

theorem cell23_6874799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 4].length) (baseStart_6874799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874799 prefixEnd_6874799 := by exact prefixLift 6874799
  have htrace : WordTrace (prefixWord ++ tailWord_6874799) baseStart_6874799 baseEnd_6874799 := by
    simpa [prefixWord, tailWord_6874799, baseEnd_6874799] using wordTrace_append hprefix tailTrace_6874799
  have hstable : (prefixWord ++ tailWord_6874799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874799).length < 2 ^ (prefixWord ++ tailWord_6874799).sum := by decide
  have hdescent : baseEnd_6874799 < baseStart_6874799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874806 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6874806 : Nat := 118140960795 + 6874806 * 2 ^ 59
def prefixEnd_6874806 : Nat := 4983230072969 + 3 ^ 40 * 6874806 * 2
def baseEnd_6874806 : Nat := 3530079884413734523608349

theorem tailTrace_6874806 : CollatzResearch.WordTrace tailWord_6874806 prefixEnd_6874806 3530079884413734523608349 := by
  unfold tailWord_6874806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671548395734966264573267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167163182887839640155448181 15671548395734966264573267)
  ·
    refine ⟨23507322593602449396859901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15671548395734966264573267 23507322593602449396859901)
    ·
      refine ⟨8815245972600918523822463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23507322593602449396859901 8815245972600918523822463)
      ·
        refine ⟨13222868958901377785733695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8815245972600918523822463 13222868958901377785733695)
        ·
          refine ⟨19834303438352066678600543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13222868958901377785733695 19834303438352066678600543)
          ·
            refine ⟨29751455157528100017900815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19834303438352066678600543 29751455157528100017900815)
            ·
              refine ⟨44627182736292150026851223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29751455157528100017900815 44627182736292150026851223)
              ·
                refine ⟨66940774104438225040276835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44627182736292150026851223 66940774104438225040276835)
                ·
                  refine ⟨100411161156657337560415253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66940774104438225040276835 100411161156657337560415253)
                  ·
                    refine ⟨4706773179218312698144465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100411161156657337560415253 4706773179218312698144465)
                    ·
                      refine ⟨3530079884413734523608349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706773179218312698144465 3530079884413734523608349)
                      ·
                        rfl

theorem cell23_6874806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6874806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874806 prefixEnd_6874806 := by exact prefixLift 6874806
  have htrace : WordTrace (prefixWord ++ tailWord_6874806) baseStart_6874806 baseEnd_6874806 := by
    simpa [prefixWord, tailWord_6874806, baseEnd_6874806] using wordTrace_append hprefix tailTrace_6874806
  have hstable : (prefixWord ++ tailWord_6874806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874806).length < 2 ^ (prefixWord ++ tailWord_6874806).sum := by decide
  have hdescent : baseEnd_6874806 < baseStart_6874806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874812 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 6]
def baseStart_6874812 : Nat := 118140960795 + 6874812 * 2 ^ 59
def prefixEnd_6874812 : Nat := 4983230072969 + 3 ^ 40 * 6874812 * 2
def baseEnd_6874812 : Nat := 392231440588629055570369

theorem tailTrace_6874812 : CollatzResearch.WordTrace tailWord_6874812 prefixEnd_6874812 392231440588629055570369 := by
  unfold tailWord_6874812
  simp only [CollatzResearch.WordTrace]
  refine ⟨125372496584868861628945345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167163328779825148838593793 125372496584868861628945345)
  ·
    refine ⟨94029372438651646221709009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125372496584868861628945345 94029372438651646221709009)
    ·
      refine ⟨70522029328988734666281757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94029372438651646221709009 70522029328988734666281757)
      ·
        refine ⟨26445760998370775499855659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70522029328988734666281757 26445760998370775499855659)
        ·
          refine ⟨39668641497556163249783489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26445760998370775499855659 39668641497556163249783489)
          ·
            refine ⟨29751481123167122437337617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39668641497556163249783489 29751481123167122437337617)
            ·
              refine ⟨22313610842375341828003213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29751481123167122437337617 22313610842375341828003213)
              ·
                refine ⟨8367604065890753185501205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22313610842375341828003213 8367604065890753185501205)
                ·
                  refine ⟨392231440588629055570369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8367604065890753185501205 392231440588629055570369)
                  ·
                    rfl

theorem cell23_6874812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_6874812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874812 prefixEnd_6874812 := by exact prefixLift 6874812
  have htrace : WordTrace (prefixWord ++ tailWord_6874812) baseStart_6874812 baseEnd_6874812 := by
    simpa [prefixWord, tailWord_6874812, baseEnd_6874812] using wordTrace_append hprefix tailTrace_6874812
  have hstable : (prefixWord ++ tailWord_6874812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874812).length < 2 ^ (prefixWord ++ tailWord_6874812).sum := by decide
  have hdescent : baseEnd_6874812 < baseStart_6874812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874826 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_6874826 : Nat := 118140960795 + 6874826 * 2 ^ 59
def prefixEnd_6874826 : Nat := 4983230072969 + 3 ^ 40 * 6874826 * 2
def baseEnd_6874826 : Nat := 3530090154026824445358257

theorem tailTrace_6874826 : CollatzResearch.WordTrace tailWord_6874826 prefixEnd_6874826 3530090154026824445358257 := by
  unfold tailWord_6874826
  simp only [CollatzResearch.WordTrace]
  refine ⟨62686375947921750912225083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167163669194458002432600221 62686375947921750912225083)
  ·
    refine ⟨94029563921882626368337625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62686375947921750912225083 94029563921882626368337625)
    ·
      refine ⟨70522172941411969776253219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94029563921882626368337625 70522172941411969776253219)
      ·
        refine ⟨105783259412117954664379829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70522172941411969776253219 105783259412117954664379829)
        ·
          refine ⟨9917180569886058249785609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105783259412117954664379829 9917180569886058249785609)
          ·
            refine ⟨7437885427414543687339207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917180569886058249785609 7437885427414543687339207)
            ·
              refine ⟨11156828141121815531008811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437885427414543687339207 11156828141121815531008811)
              ·
                refine ⟨16735242211682723296513217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11156828141121815531008811 16735242211682723296513217)
                ·
                  refine ⟨12551431658762042472384913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16735242211682723296513217 12551431658762042472384913)
                  ·
                    refine ⟨9413573744071531854288685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12551431658762042472384913 9413573744071531854288685)
                    ·
                      refine ⟨3530090154026824445358257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9413573744071531854288685 3530090154026824445358257)
                      ·
                        rfl

theorem cell23_6874826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_6874826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874826 prefixEnd_6874826 := by exact prefixLift 6874826
  have htrace : WordTrace (prefixWord ++ tailWord_6874826) baseStart_6874826 baseEnd_6874826 := by
    simpa [prefixWord, tailWord_6874826, baseEnd_6874826] using wordTrace_append hprefix tailTrace_6874826
  have hstable : (prefixWord ++ tailWord_6874826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874826).length < 2 ^ (prefixWord ++ tailWord_6874826).sum := by decide
  have hdescent : baseEnd_6874826 < baseStart_6874826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874856 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6874856 : Nat := 118140960795 + 6874856 * 2 ^ 59
def prefixEnd_6874856 : Nat := 4983230072969 + 3 ^ 40 * 6874856 * 2
def baseEnd_6874856 : Nat := 3530105558446459327983119

theorem tailTrace_6874856 : CollatzResearch.WordTrace tailWord_6874856 prefixEnd_6874856 3530105558446459327983119 := by
  unfold tailWord_6874856
  simp only [CollatzResearch.WordTrace]
  refine ⟨125373298990789159386246211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167164398654385545848328281 125373298990789159386246211)
  ·
    refine ⟨188059948486183739079369317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125373298990789159386246211 188059948486183739079369317)
    ·
      refine ⟨35261240341159451077381747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188059948486183739079369317 35261240341159451077381747)
      ·
        refine ⟨52891860511739176616072621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35261240341159451077381747 52891860511739176616072621)
        ·
          refine ⟨19834447691902191231027233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52891860511739176616072621 19834447691902191231027233)
          ·
            refine ⟨14875835768926643423270425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19834447691902191231027233 14875835768926643423270425)
            ·
              refine ⟨11156876826694982567452819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14875835768926643423270425 11156876826694982567452819)
              ·
                refine ⟨16735315240042473851179229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11156876826694982567452819 16735315240042473851179229)
                ·
                  refine ⟨6275743215015927694192211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16735315240042473851179229 6275743215015927694192211)
                  ·
                    refine ⟨9413614822523891541288317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6275743215015927694192211 9413614822523891541288317)
                    ·
                      refine ⟨3530105558446459327983119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9413614822523891541288317 3530105558446459327983119)
                      ·
                        rfl

theorem cell23_6874856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6874856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874856 prefixEnd_6874856 := by exact prefixLift 6874856
  have htrace : WordTrace (prefixWord ++ tailWord_6874856) baseStart_6874856 baseEnd_6874856 := by
    simpa [prefixWord, tailWord_6874856, baseEnd_6874856] using wordTrace_append hprefix tailTrace_6874856
  have hstable : (prefixWord ++ tailWord_6874856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874856).length < 2 ^ (prefixWord ++ tailWord_6874856).sum := by decide
  have hdescent : baseEnd_6874856 < baseStart_6874856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874892 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6874892 : Nat := 118140960795 + 6874892 * 2 ^ 59
def prefixEnd_6874892 : Nat := 4983230072969 + 3 ^ 40 * 6874892 * 2
def baseEnd_6874892 : Nat := 3530124043750021187132953

theorem tailTrace_6874892 : CollatzResearch.WordTrace tailWord_6874892 prefixEnd_6874892 3530124043750021187132953 := by
  unfold tailWord_6874892
  simp only [CollatzResearch.WordTrace]
  refine ⟨125373955504723948460401465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167165274006298597947201953 125373955504723948460401465)
  ·
    refine ⟨94030466628542961345301099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125373955504723948460401465 94030466628542961345301099)
    ·
      refine ⟨141045699942814442017951649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94030466628542961345301099 141045699942814442017951649)
      ·
        refine ⟨105784274957110831513463737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141045699942814442017951649 105784274957110831513463737)
        ·
          refine ⟨79338206217833123635097803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105784274957110831513463737 79338206217833123635097803)
          ·
            refine ⟨119007309326749685452646705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79338206217833123635097803 119007309326749685452646705)
            ·
              refine ⟨89255481995062264089485029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119007309326749685452646705 89255481995062264089485029)
              ·
                refine ⟨16735402874074174516778443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89255481995062264089485029 16735402874074174516778443)
                ·
                  refine ⟨25103104311111261775167665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16735402874074174516778443 25103104311111261775167665)
                  ·
                    refine ⟨18827328233333446331375749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25103104311111261775167665 18827328233333446331375749)
                    ·
                      refine ⟨3530124043750021187132953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18827328233333446331375749 3530124043750021187132953)
                      ·
                        rfl

theorem cell23_6874892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6874892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874892 prefixEnd_6874892 := by exact prefixLift 6874892
  have htrace : WordTrace (prefixWord ++ tailWord_6874892) baseStart_6874892 baseEnd_6874892 := by
    simpa [prefixWord, tailWord_6874892, baseEnd_6874892] using wordTrace_append hprefix tailTrace_6874892
  have hstable : (prefixWord ++ tailWord_6874892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874892).length < 2 ^ (prefixWord ++ tailWord_6874892).sum := by decide
  have hdescent : baseEnd_6874892 < baseStart_6874892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874913 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6874913 : Nat := 118140960795 + 6874913 * 2 ^ 59
def prefixEnd_6874913 : Nat := 4983230072969 + 3 ^ 40 * 6874913 * 2
def baseEnd_6874913 : Nat := 3530134826843765604970357

theorem tailTrace_6874913 : CollatzResearch.WordTrace tailWord_6874913 prefixEnd_6874913 3530134826843765604970357 := by
  unfold tailWord_6874913
  simp only [CollatzResearch.WordTrace]
  refine ⟨250748676942371817507317393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167165784628247878338211595 250748676942371817507317393)
  ·
    refine ⟨188061507706778863130488045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250748676942371817507317393 188061507706778863130488045)
    ·
      refine ⟨70523065390042073673933017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188061507706778863130488045 70523065390042073673933017)
      ·
        refine ⟨52892299042531555255449763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70523065390042073673933017 52892299042531555255449763)
        ·
          refine ⟨79338448563797332883174645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52892299042531555255449763 79338448563797332883174645)
          ·
            refine ⟨7437979552855999957797623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79338448563797332883174645 7437979552855999957797623)
            ·
              refine ⟨11156969329283999936696435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437979552855999957797623 11156969329283999936696435)
              ·
                refine ⟨16735453993925999905044653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11156969329283999936696435 16735453993925999905044653)
                ·
                  refine ⟨6275795247722249964391745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16735453993925999905044653 6275795247722249964391745)
                  ·
                    refine ⟨4706846435791687473293809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6275795247722249964391745 4706846435791687473293809)
                    ·
                      refine ⟨3530134826843765604970357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706846435791687473293809 3530134826843765604970357)
                      ·
                        rfl

theorem cell23_6874913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6874913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874913 prefixEnd_6874913 := by exact prefixLift 6874913
  have htrace : WordTrace (prefixWord ++ tailWord_6874913) baseStart_6874913 baseEnd_6874913 := by
    simpa [prefixWord, tailWord_6874913, baseEnd_6874913] using wordTrace_append hprefix tailTrace_6874913
  have hstable : (prefixWord ++ tailWord_6874913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874913).length < 2 ^ (prefixWord ++ tailWord_6874913).sum := by decide
  have hdescent : baseEnd_6874913 < baseStart_6874913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874933 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_6874933 : Nat := 118140960795 + 6874933 * 2 ^ 59
def prefixEnd_6874933 : Nat := 4983230072969 + 3 ^ 40 * 6874933 * 2
def baseEnd_6874933 : Nat := 3530145096456855526720265

theorem tailTrace_6874933 : CollatzResearch.WordTrace tailWord_6874933 prefixEnd_6874933 3530145096456855526720265 := by
  unfold tailWord_6874933
  simp only [CollatzResearch.WordTrace]
  refine ⟨250749406402299360923045453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167166270934866240615363635 250749406402299360923045453)
  ·
    refine ⟨94031027400862260346142045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250749406402299360923045453 94031027400862260346142045)
    ·
      refine ⟨35261635275323347629803267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94031027400862260346142045 35261635275323347629803267)
      ·
        refine ⟨52892452912985021444704901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35261635275323347629803267 52892452912985021444704901)
        ·
          refine ⟨9917334921184691520882169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52892452912985021444704901 9917334921184691520882169)
          ·
            refine ⟨7438001190888518640661627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917334921184691520882169 7438001190888518640661627)
            ·
              refine ⟨11157001786332777960992441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438001190888518640661627 11157001786332777960992441)
              ·
                refine ⟨8367751339749583470744331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11157001786332777960992441 8367751339749583470744331)
                ·
                  refine ⟨12551627009624375206116497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8367751339749583470744331 12551627009624375206116497)
                  ·
                    refine ⟨9413720257218281404587373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12551627009624375206116497 9413720257218281404587373)
                    ·
                      refine ⟨3530145096456855526720265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9413720257218281404587373 3530145096456855526720265)
                      ·
                        rfl

theorem cell23_6874933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_6874933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874933 prefixEnd_6874933 := by exact prefixLift 6874933
  have htrace : WordTrace (prefixWord ++ tailWord_6874933) baseStart_6874933 baseEnd_6874933 := by
    simpa [prefixWord, tailWord_6874933, baseEnd_6874933] using wordTrace_append hprefix tailTrace_6874933
  have hstable : (prefixWord ++ tailWord_6874933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874933).length < 2 ^ (prefixWord ++ tailWord_6874933).sum := by decide
  have hdescent : baseEnd_6874933 < baseStart_6874933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874969 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 3, 4, 2]
def baseStart_6874969 : Nat := 118140960795 + 6874969 * 2 ^ 59
def prefixEnd_6874969 : Nat := 4983230072969 + 3 ^ 40 * 6874969 * 2
def baseEnd_6874969 : Nat := 3530163581760417385870099

theorem tailTrace_6874969 : CollatzResearch.WordTrace tailWord_6874969 prefixEnd_6874969 3530163581760417385870099 := by
  unfold tailWord_6874969
  simp only [CollatzResearch.WordTrace]
  refine ⟨250750719430168939071355961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167167146286779292714237307 250750719430168939071355961)
  ·
    refine ⟨188063039572626704303516971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250750719430168939071355961 188063039572626704303516971)
    ·
      refine ⟨282094559358940056455275457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188063039572626704303516971 282094559358940056455275457)
      ·
        refine ⟨211570919519205042341456593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282094559358940056455275457 211570919519205042341456593)
        ·
          refine ⟨158678189639403781756092445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211570919519205042341456593 158678189639403781756092445)
          ·
            refine ⟨59504321114776418158534667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158678189639403781756092445 59504321114776418158534667)
            ·
              refine ⟨89256481672164627237802001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59504321114776418158534667 89256481672164627237802001)
              ·
                refine ⟨66942361254123470428351501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89256481672164627237802001 66942361254123470428351501)
                ·
                  refine ⟨25103385470296301410631813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66942361254123470428351501 25103385470296301410631813)
                  ·
                    refine ⟨4706884775680556514493465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25103385470296301410631813 4706884775680556514493465)
                    ·
                      refine ⟨3530163581760417385870099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706884775680556514493465 3530163581760417385870099)
                      ·
                        rfl

theorem cell23_6874969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_6874969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874969 prefixEnd_6874969 := by exact prefixLift 6874969
  have htrace : WordTrace (prefixWord ++ tailWord_6874969) baseStart_6874969 baseEnd_6874969 := by
    simpa [prefixWord, tailWord_6874969, baseEnd_6874969] using wordTrace_append hprefix tailTrace_6874969
  have hstable : (prefixWord ++ tailWord_6874969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874969).length < 2 ^ (prefixWord ++ tailWord_6874969).sum := by decide
  have hdescent : baseEnd_6874969 < baseStart_6874969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874979 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 2, 6]
def baseStart_6874979 : Nat := 118140960795 + 6874979 * 2 ^ 59
def prefixEnd_6874979 : Nat := 4983230072969 + 3 ^ 40 * 6874979 * 2
def baseEnd_6874979 : Nat := 1176722905522320782248351

theorem tailTrace_6874979 : CollatzResearch.WordTrace tailWord_6874979 prefixEnd_6874979 1176722905522320782248351 := by
  unfold tailWord_6874979
  simp only [CollatzResearch.WordTrace]
  refine ⟨250751084160132710779219991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167167389440088473852813327 250751084160132710779219991)
  ·
    refine ⟨376126626240199066168829987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250751084160132710779219991 376126626240199066168829987)
    ·
      refine ⟨564189939360298599253244981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376126626240199066168829987 564189939360298599253244981)
      ·
        refine ⟨52892806815027993679991717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 564189939360298599253244981 52892806815027993679991717)
        ·
          refine ⟨9917401277817748814998447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52892806815027993679991717 9917401277817748814998447)
          ·
            refine ⟨14876101916726623222497671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9917401277817748814998447 14876101916726623222497671)
            ·
              refine ⟨22314152875089934833746507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876101916726623222497671 22314152875089934833746507)
              ·
                refine ⟨33471229312634902250619761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22314152875089934833746507 33471229312634902250619761)
                ·
                  refine ⟨25103421984476176687964821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33471229312634902250619761 25103421984476176687964821)
                  ·
                    refine ⟨1176722905522320782248351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25103421984476176687964821 1176722905522320782248351)
                    ·
                      rfl

theorem cell23_6874979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 6].length) (baseStart_6874979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6874979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6874979 prefixEnd_6874979 := by exact prefixLift 6874979
  have htrace : WordTrace (prefixWord ++ tailWord_6874979) baseStart_6874979 baseEnd_6874979 := by
    simpa [prefixWord, tailWord_6874979, baseEnd_6874979] using wordTrace_append hprefix tailTrace_6874979
  have hstable : (prefixWord ++ tailWord_6874979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874979).length < 2 ^ (prefixWord ++ tailWord_6874979).sum := by decide
  have hdescent : baseEnd_6874979 < baseStart_6874979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875026 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_6875026 : Nat := 118140960795 + 6875026 * 2 ^ 59
def prefixEnd_6875026 : Nat := 4983230072969 + 3 ^ 40 * 6875026 * 2
def baseEnd_6875026 : Nat := 392243650017524851428593

theorem tailTrace_6875026 : CollatzResearch.WordTrace tailWord_6875026 prefixEnd_6875026 392243650017524851428593 := by
  unfold tailWord_6875026
  simp only [CollatzResearch.WordTrace]
  refine ⟨62688199597740609451545233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167168532260641625204120621 62688199597740609451545233)
  ·
    refine ⟨47016149698305457088658925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62688199597740609451545233 47016149698305457088658925)
    ·
      refine ⟨17631056136864546408247097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47016149698305457088658925 17631056136864546408247097)
      ·
        refine ⟨13223292102648409806185323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17631056136864546408247097 13223292102648409806185323)
        ·
          refine ⟨19834938153972614709277985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13223292102648409806185323 19834938153972614709277985)
          ·
            refine ⟨14876203615479461031958489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19834938153972614709277985 14876203615479461031958489)
            ·
              refine ⟨11157152711609595773968867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14876203615479461031958489 11157152711609595773968867)
              ·
                refine ⟨16735729067414393660953301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11157152711609595773968867 16735729067414393660953301)
                ·
                  refine ⟨392243650017524851428593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16735729067414393660953301 392243650017524851428593)
                  ·
                    rfl

theorem cell23_6875026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_6875026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875026 prefixEnd_6875026 := by exact prefixLift 6875026
  have htrace : WordTrace (prefixWord ++ tailWord_6875026) baseStart_6875026 baseEnd_6875026 := by
    simpa [prefixWord, tailWord_6875026, baseEnd_6875026] using wordTrace_append hprefix tailTrace_6875026
  have hstable : (prefixWord ++ tailWord_6875026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875026).length < 2 ^ (prefixWord ++ tailWord_6875026).sum := by decide
  have hdescent : baseEnd_6875026 < baseStart_6875026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875036 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6875036 : Nat := 118140960795 + 6875036 * 2 ^ 59
def prefixEnd_6875036 : Nat := 4983230072969 + 3 ^ 40 * 6875036 * 2
def baseEnd_6875036 : Nat := 3530197984964268623732291

theorem tailTrace_6875036 : CollatzResearch.WordTrace tailWord_6875036 prefixEnd_6875036 3530197984964268623732291 := by
  unfold tailWord_6875036
  simp only [CollatzResearch.WordTrace]
  refine ⟨125376581560463104757022481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167168775413950806342696641 125376581560463104757022481)
  ·
    refine ⟨94032436170347328567766861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125376581560463104757022481 94032436170347328567766861)
    ·
      refine ⟨35262163563880248212912573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94032436170347328567766861 35262163563880248212912573)
      ·
        refine ⟨13223311336455093079842215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35262163563880248212912573 13223311336455093079842215)
        ·
          refine ⟨19834967004682639619763323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13223311336455093079842215 19834967004682639619763323)
          ·
            refine ⟨29752450507023959429644985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19834967004682639619763323 29752450507023959429644985)
            ·
              refine ⟨22314337880267969572233739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29752450507023959429644985 22314337880267969572233739)
              ·
                refine ⟨33471506820401954358350609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22314337880267969572233739 33471506820401954358350609)
                ·
                  refine ⟨25103630115301465768762957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33471506820401954358350609 25103630115301465768762957)
                  ·
                    refine ⟨9413861293238049663286109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25103630115301465768762957 9413861293238049663286109)
                    ·
                      refine ⟨3530197984964268623732291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9413861293238049663286109 3530197984964268623732291)
                      ·
                        rfl

theorem cell23_6875036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6875036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875036 prefixEnd_6875036 := by exact prefixLift 6875036
  have htrace : WordTrace (prefixWord ++ tailWord_6875036) baseStart_6875036 baseEnd_6875036 := by
    simpa [prefixWord, tailWord_6875036, baseEnd_6875036] using wordTrace_append hprefix tailTrace_6875036
  have hstable : (prefixWord ++ tailWord_6875036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875036).length < 2 ^ (prefixWord ++ tailWord_6875036).sum := by decide
  have hdescent : baseEnd_6875036 < baseStart_6875036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875059 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 4]
def baseStart_6875059 : Nat := 118140960795 + 6875059 * 2 ^ 59
def prefixEnd_6875059 : Nat := 4983230072969 + 3 ^ 40 * 6875059 * 2
def baseEnd_6875059 : Nat := 3530209795019322033744685

theorem tailTrace_6875059 : CollatzResearch.WordTrace tailWord_6875059 prefixEnd_6875059 3530209795019322033744685 := by
  unfold tailWord_6875059
  simp only [CollatzResearch.WordTrace]
  refine ⟨250754001999842884442132231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167169334666561922961421487 250754001999842884442132231)
  ·
    refine ⟨376131002999764326663198347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250754001999842884442132231 376131002999764326663198347)
    ·
      refine ⟨564196504499646489994797521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376131002999764326663198347 564196504499646489994797521)
      ·
        refine ⟨423147378374734867496098141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564196504499646489994797521 423147378374734867496098141)
        ·
          refine ⟨158680266890525575311036803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423147378374734867496098141 158680266890525575311036803)
          ·
            refine ⟨238020400335788362966555205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158680266890525575311036803 238020400335788362966555205)
            ·
              refine ⟨44628825062960318056229101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238020400335788362966555205 44628825062960318056229101)
              ·
                refine ⟨16735809398610119271085913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44628825062960318056229101 16735809398610119271085913)
                ·
                  refine ⟨12551857048957589453314435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16735809398610119271085913 12551857048957589453314435)
                  ·
                    refine ⟨18827785573436384179971653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12551857048957589453314435 18827785573436384179971653)
                    ·
                      refine ⟨3530209795019322033744685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18827785573436384179971653 3530209795019322033744685)
                      ·
                        rfl

theorem cell23_6875059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_6875059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875059 prefixEnd_6875059 := by exact prefixLift 6875059
  have htrace : WordTrace (prefixWord ++ tailWord_6875059) baseStart_6875059 baseEnd_6875059 := by
    simpa [prefixWord, tailWord_6875059, baseEnd_6875059] using wordTrace_append hprefix tailTrace_6875059
  have hstable : (prefixWord ++ tailWord_6875059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875059).length < 2 ^ (prefixWord ++ tailWord_6875059).sum := by decide
  have hdescent : baseEnd_6875059 < baseStart_6875059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875136 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 4, 3, 2]
def baseStart_6875136 : Nat := 118140960795 + 6875136 * 2 ^ 59
def prefixEnd_6875136 : Nat := 4983230072969 + 3 ^ 40 * 6875136 * 2
def baseEnd_6875136 : Nat := 3530249333029718232481831

theorem tailTrace_6875136 : CollatzResearch.WordTrace tailWord_6875136 prefixEnd_6875136 3530249333029718232481831 := by
  unfold tailWord_6875136
  simp only [CollatzResearch.WordTrace]
  refine ⟨125378405210281963296342631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167171206947042617728456841 125378405210281963296342631)
  ·
    refine ⟨188067607815422944944513947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125378405210281963296342631 188067607815422944944513947)
    ·
      refine ⟨282101411723134417416770921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188067607815422944944513947 282101411723134417416770921)
      ·
        refine ⟨211576058792350813062578191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282101411723134417416770921 211576058792350813062578191)
        ·
          refine ⟨317364088188526219593867287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211576058792350813062578191 317364088188526219593867287)
          ·
            refine ⟨476046132282789329390800931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317364088188526219593867287 476046132282789329390800931)
            ·
              refine ⟨714069198424183994086201397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476046132282789329390800931 714069198424183994086201397)
              ·
                refine ⟨66943987352267249445581381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 714069198424183994086201397 66943987352267249445581381)
                ·
                  refine ⟨12551997628550109271046509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66943987352267249445581381 12551997628550109271046509)
                  ·
                    refine ⟨4706999110706290976642441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12551997628550109271046509 4706999110706290976642441)
                    ·
                      refine ⟨3530249333029718232481831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4706999110706290976642441 3530249333029718232481831)
                      ·
                        rfl

theorem cell23_6875136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_6875136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875136 prefixEnd_6875136 := by exact prefixLift 6875136
  have htrace : WordTrace (prefixWord ++ tailWord_6875136) baseStart_6875136 baseEnd_6875136 := by
    simpa [prefixWord, tailWord_6875136, baseEnd_6875136] using wordTrace_append hprefix tailTrace_6875136
  have hstable : (prefixWord ++ tailWord_6875136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875136).length < 2 ^ (prefixWord ++ tailWord_6875136).sum := by decide
  have hdescent : baseEnd_6875136 < baseStart_6875136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875179 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4]
def baseStart_6875179 : Nat := 118140960795 + 6875179 * 2 ^ 59
def prefixEnd_6875179 : Nat := 4983230072969 + 3 ^ 40 * 6875179 * 2
def baseEnd_6875179 : Nat := 3530271412697861564244133

theorem tailTrace_6875179 : CollatzResearch.WordTrace tailWord_6875179 prefixEnd_6875179 3530271412697861564244133 := by
  unfold tailWord_6875179
  simp only [CollatzResearch.WordTrace]
  refine ⟨250758378759408144936500591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167172252506272096624333727 250758378759408144936500591)
  ·
    refine ⟨376137568139112217404750887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250758378759408144936500591 376137568139112217404750887)
    ·
      refine ⟨564206352208668326107126331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376137568139112217404750887 564206352208668326107126331)
      ·
        refine ⟨846309528313002489160689497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564206352208668326107126331 846309528313002489160689497)
        ·
          refine ⟨634732146234751866870517123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846309528313002489160689497 634732146234751866870517123)
          ·
            refine ⟨952098219352127800305775685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634732146234751866870517123 952098219352127800305775685)
            ·
              refine ⟨178518416128523962557332941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 952098219352127800305775685 178518416128523962557332941)
              ·
                refine ⟨66944406048196485958999853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178518416128523962557332941 66944406048196485958999853)
                ·
                  refine ⟨25104152268073682234624945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66944406048196485958999853 25104152268073682234624945)
                  ·
                    refine ⟨18828114201055261675968709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25104152268073682234624945 18828114201055261675968709)
                    ·
                      refine ⟨3530271412697861564244133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18828114201055261675968709 3530271412697861564244133)
                      ·
                        rfl

theorem cell23_6875179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_6875179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875179 prefixEnd_6875179 := by exact prefixLift 6875179
  have htrace : WordTrace (prefixWord ++ tailWord_6875179) baseStart_6875179 baseEnd_6875179 := by
    simpa [prefixWord, tailWord_6875179, baseEnd_6875179] using wordTrace_append hprefix tailTrace_6875179
  have hstable : (prefixWord ++ tailWord_6875179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875179).length < 2 ^ (prefixWord ++ tailWord_6875179).sum := by decide
  have hdescent : baseEnd_6875179 < baseStart_6875179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875193 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 4, 4]
def baseStart_6875193 : Nat := 118140960795 + 6875193 * 2 ^ 59
def prefixEnd_6875193 : Nat := 4983230072969 + 3 ^ 40 * 6875193 * 2
def baseEnd_6875193 : Nat := 1176759533809008169823023

theorem tailTrace_6875193 : CollatzResearch.WordTrace tailWord_6875193 prefixEnd_6875193 1176759533809008169823023 := by
  unfold tailWord_6875193
  simp only [CollatzResearch.WordTrace]
  refine ⟨250758889381357425327510233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167172592920904950218340155 250758889381357425327510233)
  ·
    refine ⟨188069167036018068995632675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250758889381357425327510233 188069167036018068995632675)
    ·
      refine ⟨282103750554027103493449013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188069167036018068995632675 282103750554027103493449013)
      ·
        refine ⟨26447226614440040952510845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282103750554027103493449013 26447226614440040952510845)
        ·
          refine ⟨9917709980415015357191567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26447226614440040952510845 9917709980415015357191567)
          ·
            refine ⟨14876564970622523035787351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9917709980415015357191567 14876564970622523035787351)
            ·
              refine ⟨22314847455933784553681027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876564970622523035787351 22314847455933784553681027)
              ·
                refine ⟨33472271183900676830521541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22314847455933784553681027 33472271183900676830521541)
                ·
                  refine ⟨6276050846981376905722789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33472271183900676830521541 6276050846981376905722789)
                  ·
                    refine ⟨1176759533809008169823023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276050846981376905722789 1176759533809008169823023)
                    ·
                      rfl

theorem cell23_6875193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_6875193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875193 prefixEnd_6875193 := by exact prefixLift 6875193
  have htrace : WordTrace (prefixWord ++ tailWord_6875193) baseStart_6875193 baseEnd_6875193 := by
    simpa [prefixWord, tailWord_6875193, baseEnd_6875193] using wordTrace_append hprefix tailTrace_6875193
  have hstable : (prefixWord ++ tailWord_6875193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875193).length < 2 ^ (prefixWord ++ tailWord_6875193).sum := by decide
  have hdescent : baseEnd_6875193 < baseStart_6875193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875200 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 3, 2, 2]
def baseStart_6875200 : Nat := 118140960795 + 6875200 * 2 ^ 59
def prefixEnd_6875200 : Nat := 4983230072969 + 3 ^ 40 * 6875200 * 2
def baseEnd_6875200 : Nat := 3530282195791605982081537

theorem tailTrace_6875200 : CollatzResearch.WordTrace tailWord_6875200 prefixEnd_6875200 3530282195791605982081537 := by
  unfold tailWord_6875200
  simp only [CollatzResearch.WordTrace]
  refine ⟨125379572346166032761507527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167172763128221377015343369 125379572346166032761507527)
  ·
    refine ⟨188069358519249049142261291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125379572346166032761507527 188069358519249049142261291)
    ·
      refine ⟨282104037778873573713391937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188069358519249049142261291 282104037778873573713391937)
      ·
        refine ⟨211578028334155180285043953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282104037778873573713391937 211578028334155180285043953)
        ·
          refine ⟨158683521250616385213782965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211578028334155180285043953 158683521250616385213782965)
          ·
            refine ⟨14876580117245286113792153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158683521250616385213782965 14876580117245286113792153)
            ·
              refine ⟨11157435087933964585344115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14876580117245286113792153 11157435087933964585344115)
              ·
                refine ⟨16736152631900946878016173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11157435087933964585344115 16736152631900946878016173)
                ·
                  refine ⟨6276057236962855079256065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16736152631900946878016173 6276057236962855079256065)
                  ·
                    refine ⟨4707042927722141309442049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276057236962855079256065 4707042927722141309442049)
                    ·
                      refine ⟨3530282195791605982081537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707042927722141309442049 3530282195791605982081537)
                      ·
                        rfl

theorem cell23_6875200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_6875200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875200 prefixEnd_6875200 := by exact prefixLift 6875200
  have htrace : WordTrace (prefixWord ++ tailWord_6875200) baseStart_6875200 baseEnd_6875200 := by
    simpa [prefixWord, tailWord_6875200, baseEnd_6875200] using wordTrace_append hprefix tailTrace_6875200
  have hstable : (prefixWord ++ tailWord_6875200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875200).length < 2 ^ (prefixWord ++ tailWord_6875200).sum := by decide
  have hdescent : baseEnd_6875200 < baseStart_6875200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875246 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6875246 : Nat := 118140960795 + 6875246 * 2 ^ 59
def prefixEnd_6875246 : Nat := 4983230072969 + 3 ^ 40 * 6875246 * 2
def baseEnd_6875246 : Nat := 3530305815901712802106325

theorem tailTrace_6875246 : CollatzResearch.WordTrace tailWord_6875246 prefixEnd_6875246 3530305815901712802106325 := by
  unfold tailWord_6875246
  simp only [CollatzResearch.WordTrace]
  refine ⟨31345102806270676922398699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167173881633443610252793061 31345102806270676922398699)
  ·
    refine ⟨47017654209406015383598049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31345102806270676922398699 47017654209406015383598049)
    ·
      refine ⟨35263240657054511537698537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47017654209406015383598049 35263240657054511537698537)
      ·
        refine ⟨26447430492790883653273903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35263240657054511537698537 26447430492790883653273903)
        ·
          refine ⟨39671145739186325479910855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26447430492790883653273903 39671145739186325479910855)
          ·
            refine ⟨59506718608779488219866283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39671145739186325479910855 59506718608779488219866283)
            ·
              refine ⟨89260077913169232329799425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59506718608779488219866283 89260077913169232329799425)
              ·
                refine ⟨66945058434876924247349569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89260077913169232329799425 66945058434876924247349569)
                ·
                  refine ⟨50208793826157693185512177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66945058434876924247349569 50208793826157693185512177)
                  ·
                    refine ⟨37656595369618269889134133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50208793826157693185512177 37656595369618269889134133)
                    ·
                      refine ⟨3530305815901712802106325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37656595369618269889134133 3530305815901712802106325)
                      ·
                        rfl

theorem cell23_6875246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6875246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875246 prefixEnd_6875246 := by exact prefixLift 6875246
  have htrace : WordTrace (prefixWord ++ tailWord_6875246) baseStart_6875246 baseEnd_6875246 := by
    simpa [prefixWord, tailWord_6875246, baseEnd_6875246] using wordTrace_append hprefix tailTrace_6875246
  have hstable : (prefixWord ++ tailWord_6875246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875246).length < 2 ^ (prefixWord ++ tailWord_6875246).sum := by decide
  have hdescent : baseEnd_6875246 < baseStart_6875246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875267 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 2, 1, 3]
def baseStart_6875267 : Nat := 118140960795 + 6875267 * 2 ^ 59
def prefixEnd_6875267 : Nat := 4983230072969 + 3 ^ 40 * 6875267 * 2
def baseEnd_6875267 : Nat := 3530316598995457219943729

theorem tailTrace_6875267 : CollatzResearch.WordTrace tailWord_6875267 prefixEnd_6875267 3530316598995457219943729 := by
  unfold tailWord_6875267
  simp only [CollatzResearch.WordTrace]
  refine ⟨250761588383089335965704055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167174392255392890643802703 250761588383089335965704055)
  ·
    refine ⟨376142382574634003948556083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250761588383089335965704055 376142382574634003948556083)
    ·
      refine ⟨564213573861951005922834125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376142382574634003948556083 564213573861951005922834125)
      ·
        refine ⟨211580090198231627221062797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564213573861951005922834125 211580090198231627221062797)
        ·
          refine ⟨79342533824336860207898549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211580090198231627221062797 79342533824336860207898549)
          ·
            refine ⟨7438362546031580644490489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79342533824336860207898549 7438362546031580644490489)
            ·
              refine ⟨5578771909523685483367867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438362546031580644490489 5578771909523685483367867)
              ·
                refine ⟨8368157864285528225051801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578771909523685483367867 8368157864285528225051801)
                ·
                  refine ⟨6276118398214146168788851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8368157864285528225051801 6276118398214146168788851)
                  ·
                    refine ⟨9414177597321219253183277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6276118398214146168788851 9414177597321219253183277)
                    ·
                      refine ⟨3530316598995457219943729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9414177597321219253183277 3530316598995457219943729)
                      ·
                        rfl

theorem cell23_6875267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_6875267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875267 prefixEnd_6875267 := by exact prefixLift 6875267
  have htrace : WordTrace (prefixWord ++ tailWord_6875267) baseStart_6875267 baseEnd_6875267 := by
    simpa [prefixWord, tailWord_6875267, baseEnd_6875267] using wordTrace_append hprefix tailTrace_6875267
  have hstable : (prefixWord ++ tailWord_6875267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875267).length < 2 ^ (prefixWord ++ tailWord_6875267).sum := by decide
  have hdescent : baseEnd_6875267 < baseStart_6875267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875273 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 1, 4, 2]
def baseStart_6875273 : Nat := 118140960795 + 6875273 * 2 ^ 59
def prefixEnd_6875273 : Nat := 4983230072969 + 3 ^ 40 * 6875273 * 2
def baseEnd_6875273 : Nat := 3530319679879384196468701

theorem tailTrace_6875273 : CollatzResearch.WordTrace tailWord_6875273 prefixEnd_6875273 3530319679879384196468701 := by
  unfold tailWord_6875273
  simp only [CollatzResearch.WordTrace]
  refine ⟨250761807221067598990422473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167174538147378399326948315 250761807221067598990422473)
  ·
    refine ⟨188071355415800699242816855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250761807221067598990422473 188071355415800699242816855)
    ·
      refine ⟨282107033123701048864225283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188071355415800699242816855 282107033123701048864225283)
      ·
        refine ⟨423160549685551573296337925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282107033123701048864225283 423160549685551573296337925)
        ·
          refine ⟨79342603066040919993063361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423160549685551573296337925 79342603066040919993063361)
          ·
            refine ⟨59506952299530689994797521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79342603066040919993063361 59506952299530689994797521)
            ·
              refine ⟨44630214224648017496098141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59506952299530689994797521 44630214224648017496098141)
              ·
                refine ⟨16736330334243006561036803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44630214224648017496098141 16736330334243006561036803)
                ·
                  refine ⟨25104495501364509841555205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16736330334243006561036803 25104495501364509841555205)
                  ·
                    refine ⟨4707092906505845595291601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25104495501364509841555205 4707092906505845595291601)
                    ·
                      refine ⟨3530319679879384196468701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707092906505845595291601 3530319679879384196468701)
                      ·
                        rfl

theorem cell23_6875273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 4, 2].length) (baseStart_6875273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875273 prefixEnd_6875273 := by exact prefixLift 6875273
  have htrace : WordTrace (prefixWord ++ tailWord_6875273) baseStart_6875273 baseEnd_6875273 := by
    simpa [prefixWord, tailWord_6875273, baseEnd_6875273] using wordTrace_append hprefix tailTrace_6875273
  have hstable : (prefixWord ++ tailWord_6875273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875273).length < 2 ^ (prefixWord ++ tailWord_6875273).sum := by decide
  have hdescent : baseEnd_6875273 < baseStart_6875273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875330 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6875330 : Nat := 118140960795 + 6875330 * 2 ^ 59
def prefixEnd_6875330 : Nat := 4983230072969 + 3 ^ 40 * 6875330 * 2
def baseEnd_6875330 : Nat := 392260994252965608161771

theorem tailTrace_6875330 : CollatzResearch.WordTrace tailWord_6875330 prefixEnd_6875330 392260994252965608161771 := by
  unfold tailWord_6875330
  simp only [CollatzResearch.WordTrace]
  refine ⟨62690971545465274431311861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167175924121240731816831629 62690971545465274431311861)
  ·
    refine ⟨5877278582387369477935487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62690971545465274431311861 5877278582387369477935487)
    ·
      refine ⟨8815917873581054216903231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877278582387369477935487 8815917873581054216903231)
      ·
        refine ⟨13223876810371581325354847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8815917873581054216903231 13223876810371581325354847)
        ·
          refine ⟨19835815215557371988032271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13223876810371581325354847 19835815215557371988032271)
          ·
            refine ⟨29753722823336057982048407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19835815215557371988032271 29753722823336057982048407)
            ·
              refine ⟨44630584235004086973072611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29753722823336057982048407 44630584235004086973072611)
              ·
                refine ⟨66945876352506130459608917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44630584235004086973072611 66945876352506130459608917)
                ·
                  refine ⟨392260994252965608161771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66945876352506130459608917 392260994252965608161771)
                  ·
                    rfl

theorem cell23_6875330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6875330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875330 prefixEnd_6875330 := by exact prefixLift 6875330
  have htrace : WordTrace (prefixWord ++ tailWord_6875330) baseStart_6875330 baseEnd_6875330 := by
    simpa [prefixWord, tailWord_6875330, baseEnd_6875330] using wordTrace_append hprefix tailTrace_6875330
  have hstable : (prefixWord ++ tailWord_6875330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875330).length < 2 ^ (prefixWord ++ tailWord_6875330).sum := by decide
  have hdescent : baseEnd_6875330 < baseStart_6875330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875390 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6875390 : Nat := 118140960795 + 6875390 * 2 ^ 59
def prefixEnd_6875390 : Nat := 4983230072969 + 3 ^ 40 * 6875390 * 2
def baseEnd_6875390 : Nat := 1176793252371986746235221

theorem tailTrace_6875390 : CollatzResearch.WordTrace tailWord_6875390 prefixEnd_6875390 1176793252371986746235221 := by
  unfold tailWord_6875390
  simp only [CollatzResearch.WordTrace]
  refine ⟨31345759320205465996553953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167177383041095818648287749 31345759320205465996553953)
  ·
    refine ⟨23509319490154099497415465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31345759320205465996553953 23509319490154099497415465)
    ·
      refine ⟨17631989617615574623061599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23509319490154099497415465 17631989617615574623061599)
      ·
        refine ⟨26447984426423361934592399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17631989617615574623061599 26447984426423361934592399)
        ·
          refine ⟨39671976639635042901888599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26447984426423361934592399 39671976639635042901888599)
          ·
            refine ⟨59507964959452564352832899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39671976639635042901888599 59507964959452564352832899)
            ·
              refine ⟨89261947439178846529249349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59507964959452564352832899 89261947439178846529249349)
              ·
                refine ⟨16736615144846033724234253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89261947439178846529249349 16736615144846033724234253)
                ·
                  refine ⟨6276230679317262646587845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16736615144846033724234253 6276230679317262646587845)
                  ·
                    refine ⟨1176793252371986746235221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276230679317262646587845 1176793252371986746235221)
                    ·
                      rfl

theorem cell23_6875390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6875390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875390 prefixEnd_6875390 := by exact prefixLift 6875390
  have htrace : WordTrace (prefixWord ++ tailWord_6875390) baseStart_6875390 baseEnd_6875390 := by
    simpa [prefixWord, tailWord_6875390, baseEnd_6875390] using wordTrace_append hprefix tailTrace_6875390
  have hstable : (prefixWord ++ tailWord_6875390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875390).length < 2 ^ (prefixWord ++ tailWord_6875390).sum := by decide
  have hdescent : baseEnd_6875390 < baseStart_6875390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875424 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 1, 4]
def baseStart_6875424 : Nat := 118140960795 + 6875424 * 2 ^ 59
def prefixEnd_6875424 : Nat := 4983230072969 + 3 ^ 40 * 6875424 * 2
def baseEnd_6875424 : Nat := 1176799071819404368560169

theorem tailTrace_6875424 : CollatzResearch.WordTrace tailWord_6875424 prefixEnd_6875424 1176799071819404368560169 := by
  unfold tailWord_6875424
  simp only [CollatzResearch.WordTrace]
  refine ⟨125383657321760275889584663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167178209762347034519446217 125383657321760275889584663)
  ·
    refine ⟨188075485982640413834376995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125383657321760275889584663 188075485982640413834376995)
    ·
      refine ⟨282113228973960620751565493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188075485982640413834376995 282113228973960620751565493)
      ·
        refine ⟨26448115216308808195459265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282113228973960620751565493 26448115216308808195459265)
        ·
          refine ⟨19836086412231606146594449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26448115216308808195459265 19836086412231606146594449)
          ·
            refine ⟨14877064809173704609945837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19836086412231606146594449 14877064809173704609945837)
            ·
              refine ⟨5578899303440139228729689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14877064809173704609945837 5578899303440139228729689)
              ·
                refine ⟨4184174477580104421547267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5578899303440139228729689 4184174477580104421547267)
                ·
                  refine ⟨6276261716370156632320901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184174477580104421547267 6276261716370156632320901)
                  ·
                    refine ⟨1176799071819404368560169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276261716370156632320901 1176799071819404368560169)
                    ·
                      rfl

theorem cell23_6875424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 4].length) (baseStart_6875424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875424 prefixEnd_6875424 := by exact prefixLift 6875424
  have htrace : WordTrace (prefixWord ++ tailWord_6875424) baseStart_6875424 baseEnd_6875424 := by
    simpa [prefixWord, tailWord_6875424, baseEnd_6875424] using wordTrace_append hprefix tailTrace_6875424
  have hstable : (prefixWord ++ tailWord_6875424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875424).length < 2 ^ (prefixWord ++ tailWord_6875424).sum := by decide
  have hdescent : baseEnd_6875424 < baseStart_6875424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875437 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 6]
def baseStart_6875437 : Nat := 118140960795 + 6875437 * 2 ^ 59
def prefixEnd_6875437 : Nat := 4983230072969 + 3 ^ 40 * 6875437 * 2
def baseEnd_6875437 : Nat := 392267098967413506090883

theorem tailTrace_6875437 : CollatzResearch.WordTrace tailWord_6875437 prefixEnd_6875437 392267098967413506090883 := by
  unfold tailWord_6875437
  simp only [CollatzResearch.WordTrace]
  refine ⟨250767788792473454999392565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167178525861648969999595043 250767788792473454999392565)
  ·
    refine ⟨23509480199294386406193053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250767788792473454999392565 23509480199294386406193053)
    ·
      refine ⟨8816055074735394902322395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23509480199294386406193053 8816055074735394902322395)
      ·
        refine ⟨13224082612103092353483593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816055074735394902322395 13224082612103092353483593)
        ·
          refine ⟨9918061959077319265112695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13224082612103092353483593 9918061959077319265112695)
          ·
            refine ⟨14877092938615978897669043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918061959077319265112695 14877092938615978897669043)
            ·
              refine ⟨22315639407923968346503565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14877092938615978897669043 22315639407923968346503565)
              ·
                refine ⟨8368364777971488129938837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22315639407923968346503565 8368364777971488129938837)
                ·
                  refine ⟨392267098967413506090883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8368364777971488129938837 392267098967413506090883)
                  ·
                    rfl

theorem cell23_6875437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_6875437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875437 prefixEnd_6875437 := by exact prefixLift 6875437
  have htrace : WordTrace (prefixWord ++ tailWord_6875437) baseStart_6875437 baseEnd_6875437 := by
    simpa [prefixWord, tailWord_6875437, baseEnd_6875437] using wordTrace_append hprefix tailTrace_6875437
  have hstable : (prefixWord ++ tailWord_6875437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875437).length < 2 ^ (prefixWord ++ tailWord_6875437).sum := by decide
  have hdescent : baseEnd_6875437 < baseStart_6875437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875450 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_6875450 : Nat := 118140960795 + 6875450 * 2 ^ 59
def prefixEnd_6875450 : Nat := 4983230072969 + 3 ^ 40 * 6875450 * 2
def baseEnd_6875450 : Nat := 1176803521985076667985129

theorem tailTrace_6875450 : CollatzResearch.WordTrace tailWord_6875450 prefixEnd_6875450 1176803521985076667985129 := by
  unfold tailWord_6875450
  simp only [CollatzResearch.WordTrace]
  refine ⟨62692065735356589554903951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167178841960950905479743869 62692065735356589554903951)
  ·
    refine ⟨94038098603034884332355927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62692065735356589554903951 94038098603034884332355927)
    ·
      refine ⟨141057147904552326498533891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94038098603034884332355927 141057147904552326498533891)
      ·
        refine ⟨211585721856828489747800837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141057147904552326498533891 211585721856828489747800837)
        ·
          refine ⟨39672322848155341827712657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211585721856828489747800837 39672322848155341827712657)
          ·
            refine ⟨29754242136116506370784493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39672322848155341827712657 29754242136116506370784493)
            ·
              refine ⟨11157840801043689889044185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29754242136116506370784493 11157840801043689889044185)
              ·
                refine ⟨8368380600782767416783139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11157840801043689889044185 8368380600782767416783139)
                ·
                  refine ⟨12552570901174151125174709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8368380600782767416783139 12552570901174151125174709)
                  ·
                    refine ⟨1176803521985076667985129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12552570901174151125174709 1176803521985076667985129)
                    ·
                      rfl

theorem cell23_6875450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_6875450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875450 prefixEnd_6875450 := by exact prefixLift 6875450
  have htrace : WordTrace (prefixWord ++ tailWord_6875450) baseStart_6875450 baseEnd_6875450 := by
    simpa [prefixWord, tailWord_6875450, baseEnd_6875450] using wordTrace_append hprefix tailTrace_6875450
  have hstable : (prefixWord ++ tailWord_6875450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875450).length < 2 ^ (prefixWord ++ tailWord_6875450).sum := by decide
  have hdescent : baseEnd_6875450 < baseStart_6875450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875463 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 1, 6]
def baseStart_6875463 : Nat := 118140960795 + 6875463 * 2 ^ 59
def prefixEnd_6875463 : Nat := 4983230072969 + 3 ^ 40 * 6875463 * 2
def baseEnd_6875463 : Nat := 1176805747067912817697609

theorem tailTrace_6875463 : CollatzResearch.WordTrace tailWord_6875463 prefixEnd_6875463 1176805747067912817697609 := by
  unfold tailWord_6875463
  simp only [CollatzResearch.WordTrace]
  refine ⟨250768737090379261439839043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167179158060252840959892695 250768737090379261439839043)
  ·
    refine ⟨376153105635568892159758565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250768737090379261439839043 376153105635568892159758565)
    ·
      refine ⟨70528707306669167279954731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376153105635568892159758565 70528707306669167279954731)
      ·
        refine ⟨105793060960003750919932097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70528707306669167279954731 105793060960003750919932097)
        ·
          refine ⟨79344795720002813189949073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105793060960003750919932097 79344795720002813189949073)
          ·
            refine ⟨59508596790002109892461805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79344795720002813189949073 59508596790002109892461805)
            ·
              refine ⟨22315723796250791209673177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59508596790002109892461805 22315723796250791209673177)
              ·
                refine ⟨16736792847188093407254883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22315723796250791209673177 16736792847188093407254883)
                ·
                  refine ⟨25105189270782140110882325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16736792847188093407254883 25105189270782140110882325)
                  ·
                    refine ⟨1176805747067912817697609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25105189270782140110882325 1176805747067912817697609)
                    ·
                      rfl

theorem cell23_6875463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_6875463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875463 prefixEnd_6875463 := by exact prefixLift 6875463
  have htrace : WordTrace (prefixWord ++ tailWord_6875463) baseStart_6875463 baseEnd_6875463 := by
    simpa [prefixWord, tailWord_6875463, baseEnd_6875463] using wordTrace_append hprefix tailTrace_6875463
  have hstable : (prefixWord ++ tailWord_6875463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875463).length < 2 ^ (prefixWord ++ tailWord_6875463).sum := by decide
  have hdescent : baseEnd_6875463 < baseStart_6875463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875493 : List Nat := [1, 3, 1, 3, 1, 3, 3, 8]
def baseStart_6875493 : Nat := 118140960795 + 6875493 * 2 ^ 59
def prefixEnd_6875493 : Nat := 4983230072969 + 3 ^ 40 * 6875493 * 2
def baseEnd_6875493 : Nat := 130756764652717530952507

theorem tailTrace_6875493 : CollatzResearch.WordTrace tailWord_6875493 prefixEnd_6875493 130756764652717530952507 := by
  unfold tailWord_6875493
  simp only [CollatzResearch.WordTrace]
  refine ⟨250769831280270576563431133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167179887520180384375620755 250769831280270576563431133)
  ·
    refine ⟨94038686730101466211286675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250769831280270576563431133 94038686730101466211286675)
    ·
      refine ⟨141058030095152199316930013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94038686730101466211286675 141058030095152199316930013)
      ·
        refine ⟨52896761285682074743848755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141058030095152199316930013 52896761285682074743848755)
        ·
          refine ⟨79345141928523112115773133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52896761285682074743848755 79345141928523112115773133)
          ·
            refine ⟨29754428223196167043414925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79345141928523112115773133 29754428223196167043414925)
            ·
              refine ⟨11157910583698562641280597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29754428223196167043414925 11157910583698562641280597)
              ·
                refine ⟨130756764652717530952507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11157910583698562641280597 130756764652717530952507)
                ·
                  rfl

theorem cell23_6875493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 8].length) (baseStart_6875493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875493 prefixEnd_6875493 := by exact prefixLift 6875493
  have htrace : WordTrace (prefixWord ++ tailWord_6875493) baseStart_6875493 baseEnd_6875493 := by
    simpa [prefixWord, tailWord_6875493, baseEnd_6875493] using wordTrace_append hprefix tailTrace_6875493
  have hstable : (prefixWord ++ tailWord_6875493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875493).length < 2 ^ (prefixWord ++ tailWord_6875493).sum := by decide
  have hdescent : baseEnd_6875493 < baseStart_6875493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875521 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6875521 : Nat := 118140960795 + 6875521 * 2 ^ 59
def prefixEnd_6875521 : Nat := 4983230072969 + 3 ^ 40 * 6875521 * 2
def baseEnd_6875521 : Nat := 3530447023081699226167561

theorem tailTrace_6875521 : CollatzResearch.WordTrace tailWord_6875521 prefixEnd_6875521 3530447023081699226167561 := by
  unfold tailWord_6875521
  simp only [CollatzResearch.WordTrace]
  refine ⟨250770852524169137345450417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167180568349446091563633611 250770852524169137345450417)
  ·
    refine ⟨188078139393126853009087813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250770852524169137345450417 188078139393126853009087813)
    ·
      refine ⟨35264651136211284939203965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188078139393126853009087813 35264651136211284939203965)
      ·
        refine ⟨13224244176079231852201487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35264651136211284939203965 13224244176079231852201487)
        ·
          refine ⟨19836366264118847778302231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13224244176079231852201487 19836366264118847778302231)
          ·
            refine ⟨29754549396178271667453347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19836366264118847778302231 29754549396178271667453347)
            ·
              refine ⟨44631824094267407501180021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29754549396178271667453347 44631824094267407501180021)
              ·
                refine ⟨4184233508837569453235627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44631824094267407501180021 4184233508837569453235627)
                ·
                  refine ⟨6276350263256354179853441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184233508837569453235627 6276350263256354179853441)
                  ·
                    refine ⟨4707262697442265634890081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276350263256354179853441 4707262697442265634890081)
                    ·
                      refine ⟨3530447023081699226167561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707262697442265634890081 3530447023081699226167561)
                      ·
                        rfl

theorem cell23_6875521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6875521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875521 prefixEnd_6875521 := by exact prefixLift 6875521
  have htrace : WordTrace (prefixWord ++ tailWord_6875521) baseStart_6875521 baseEnd_6875521 := by
    simpa [prefixWord, tailWord_6875521, baseEnd_6875521] using wordTrace_append hprefix tailTrace_6875521
  have hstable : (prefixWord ++ tailWord_6875521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875521).length < 2 ^ (prefixWord ++ tailWord_6875521).sum := by decide
  have hdescent : baseEnd_6875521 < baseStart_6875521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875543 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_6875543 : Nat := 118140960795 + 6875543 * 2 ^ 59
def prefixEnd_6875543 : Nat := 4983230072969 + 3 ^ 40 * 6875543 * 2
def baseEnd_6875543 : Nat := 3530458319656098140092459

theorem tailTrace_6875543 : CollatzResearch.WordTrace tailWord_6875543 prefixEnd_6875543 3530458319656098140092459 := by
  unfold tailWord_6875543
  simp only [CollatzResearch.WordTrace]
  refine ⟨250771654930089435102751283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167181103286726290068500855 250771654930089435102751283)
  ·
    refine ⟨376157482395134152654126925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250771654930089435102751283 376157482395134152654126925)
    ·
      refine ⟨141059055898175307245297597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376157482395134152654126925 141059055898175307245297597)
      ·
        refine ⟨52897145961815740216986599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141059055898175307245297597 52897145961815740216986599)
        ·
          refine ⟨79345718942723610325479899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52897145961815740216986599 79345718942723610325479899)
          ·
            refine ⟨119018578414085415488219849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79345718942723610325479899 119018578414085415488219849)
            ·
              refine ⟨89263933810564061616164887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119018578414085415488219849 89263933810564061616164887)
              ·
                refine ⟨133895900715846092424247331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89263933810564061616164887 133895900715846092424247331)
                ·
                  refine ⟨200843851073769138636370997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133895900715846092424247331 200843851073769138636370997)
                  ·
                    refine ⟨18829111038165856747159781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200843851073769138636370997 18829111038165856747159781)
                    ·
                      refine ⟨3530458319656098140092459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18829111038165856747159781 3530458319656098140092459)
                      ·
                        rfl

theorem cell23_6875543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_6875543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875543 prefixEnd_6875543 := by exact prefixLift 6875543
  have htrace : WordTrace (prefixWord ++ tailWord_6875543) baseStart_6875543 baseEnd_6875543 := by
    simpa [prefixWord, tailWord_6875543, baseEnd_6875543] using wordTrace_append hprefix tailTrace_6875543
  have hstable : (prefixWord ++ tailWord_6875543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875543).length < 2 ^ (prefixWord ++ tailWord_6875543).sum := by decide
  have hdescent : baseEnd_6875543 < baseStart_6875543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875572 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6875572 : Nat := 118140960795 + 6875572 * 2 ^ 59
def prefixEnd_6875572 : Nat := 4983230072969 + 3 ^ 40 * 6875572 * 2
def baseEnd_6875572 : Nat := 3530473210595078526629827

theorem tailTrace_6875572 : CollatzResearch.WordTrace tailWord_6875572 prefixEnd_6875572 3530473210595078526629827 := by
  unfold tailWord_6875572
  simp only [CollatzResearch.WordTrace]
  refine ⟨125386356323492186527778485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167181808431322915370371313 125386356323492186527778485)
  ·
    refine ⟨11754970905327392486979233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125386356323492186527778485 11754970905327392486979233)
    ·
      refine ⟨8816228178995544365234425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11754970905327392486979233 8816228178995544365234425)
      ·
        refine ⟨6612171134246658273925819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816228178995544365234425 6612171134246658273925819)
        ·
          refine ⟨9918256701369987410888729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612171134246658273925819 9918256701369987410888729)
          ·
            refine ⟨7438692526027490558166547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9918256701369987410888729 7438692526027490558166547)
            ·
              refine ⟨11158038789041235837249821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438692526027490558166547 11158038789041235837249821)
              ·
                refine ⟨4184264545890463438968683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11158038789041235837249821 4184264545890463438968683)
                ·
                  refine ⟨6276396818835695158453025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184264545890463438968683 6276396818835695158453025)
                  ·
                    refine ⟨4707297614126771368839769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276396818835695158453025 4707297614126771368839769)
                    ·
                      refine ⟨3530473210595078526629827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707297614126771368839769 3530473210595078526629827)
                      ·
                        rfl

theorem cell23_6875572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6875572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875572 prefixEnd_6875572 := by exact prefixLift 6875572
  have htrace : WordTrace (prefixWord ++ tailWord_6875572) baseStart_6875572 baseEnd_6875572 := by
    simpa [prefixWord, tailWord_6875572, baseEnd_6875572] using wordTrace_append hprefix tailTrace_6875572
  have hstable : (prefixWord ++ tailWord_6875572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875572).length < 2 ^ (prefixWord ++ tailWord_6875572).sum := by decide
  have hdescent : baseEnd_6875572 < baseStart_6875572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875580 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6875580 : Nat := 118140960795 + 6875580 * 2 ^ 59
def prefixEnd_6875580 : Nat := 4983230072969 + 3 ^ 40 * 6875580 * 2
def baseEnd_6875580 : Nat := 3530477318440314495329789

theorem tailTrace_6875580 : CollatzResearch.WordTrace tailWord_6875580 prefixEnd_6875580 3530477318440314495329789 := by
  unfold tailWord_6875580
  simp only [CollatzResearch.WordTrace]
  refine ⟨125386502215477695210924097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167182002953970260281232129 125386502215477695210924097)
  ·
    refine ⟨94039876661608271408193073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125386502215477695210924097 94039876661608271408193073)
    ·
      refine ⟨70529907496206203556144805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94039876661608271408193073 70529907496206203556144805)
      ·
        refine ⟨13224357655538663166777151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70529907496206203556144805 13224357655538663166777151)
        ·
          refine ⟨19836536483307994750165727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13224357655538663166777151 19836536483307994750165727)
          ·
            refine ⟨29754804724961992125248591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19836536483307994750165727 29754804724961992125248591)
            ·
              refine ⟨44632207087442988187872887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29754804724961992125248591 44632207087442988187872887)
              ·
                refine ⟨66948310631164482281809331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44632207087442988187872887 66948310631164482281809331)
                ·
                  refine ⟨100422465946746723422713997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66948310631164482281809331 100422465946746723422713997)
                  ·
                    refine ⟨37658424730030021283517749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100422465946746723422713997 37658424730030021283517749)
                    ·
                      refine ⟨3530477318440314495329789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37658424730030021283517749 3530477318440314495329789)
                      ·
                        rfl

theorem cell23_6875580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6875580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875580 prefixEnd_6875580 := by exact prefixLift 6875580
  have htrace : WordTrace (prefixWord ++ tailWord_6875580) baseStart_6875580 baseEnd_6875580 := by
    simpa [prefixWord, tailWord_6875580, baseEnd_6875580] using wordTrace_append hprefix tailTrace_6875580
  have hstable : (prefixWord ++ tailWord_6875580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875580).length < 2 ^ (prefixWord ++ tailWord_6875580).sum := by decide
  have hdescent : baseEnd_6875580 < baseStart_6875580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875594 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_6875594 : Nat := 118140960795 + 6875594 * 2 ^ 59
def prefixEnd_6875594 : Nat := 4983230072969 + 3 ^ 40 * 6875594 * 2
def baseEnd_6875594 : Nat := 3530484507169477440554725

theorem tailTrace_6875594 : CollatzResearch.WordTrace tailWord_6875594 prefixEnd_6875594 3530484507169477440554725 := by
  unfold tailWord_6875594
  simp only [CollatzResearch.WordTrace]
  refine ⟨62693378763226167703214459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167182343368603113875238557 62693378763226167703214459)
  ·
    refine ⟨94040068144839251554821689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62693378763226167703214459 94040068144839251554821689)
    ·
      refine ⟨70530051108629438666116267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94040068144839251554821689 70530051108629438666116267)
      ·
        refine ⟨105795076662944157999174401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70530051108629438666116267 105795076662944157999174401)
        ·
          refine ⟨79346307497208118499380801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105795076662944157999174401 79346307497208118499380801)
          ·
            refine ⟨59509730622906088874535601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79346307497208118499380801 59509730622906088874535601)
            ·
              refine ⟨44632297967179566655901701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59509730622906088874535601 44632297967179566655901701)
              ·
                refine ⟨8368555868846168747981569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44632297967179566655901701 8368555868846168747981569)
                ·
                  refine ⟨6276416901634626560986177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8368555868846168747981569 6276416901634626560986177)
                  ·
                    refine ⟨4707312676225969920739633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276416901634626560986177 4707312676225969920739633)
                    ·
                      refine ⟨3530484507169477440554725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707312676225969920739633 3530484507169477440554725)
                      ·
                        rfl

theorem cell23_6875594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_6875594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875594 prefixEnd_6875594 := by exact prefixLift 6875594
  have htrace : WordTrace (prefixWord ++ tailWord_6875594) baseStart_6875594 baseEnd_6875594 := by
    simpa [prefixWord, tailWord_6875594, baseEnd_6875594] using wordTrace_append hprefix tailTrace_6875594
  have hstable : (prefixWord ++ tailWord_6875594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875594).length < 2 ^ (prefixWord ++ tailWord_6875594).sum := by decide
  have hdescent : baseEnd_6875594 < baseStart_6875594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875610 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_6875610 : Nat := 118140960795 + 6875610 * 2 ^ 59
def prefixEnd_6875610 : Nat := 4983230072969 + 3 ^ 40 * 6875610 * 2
def baseEnd_6875610 : Nat := 3530492722859949377954651

theorem tailTrace_6875610 : CollatzResearch.WordTrace tailWord_6875610 prefixEnd_6875610 3530492722859949377954651 := by
  unfold tailWord_6875610
  simp only [CollatzResearch.WordTrace]
  refine ⟨62693524655211676386360071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167182732413897803696960189 62693524655211676386360071)
  ·
    refine ⟨94040286982817514579540107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62693524655211676386360071 94040286982817514579540107)
    ·
      refine ⟨141060430474226271869310161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94040286982817514579540107 141060430474226271869310161)
      ·
        refine ⟨105795322855669703901982621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141060430474226271869310161 105795322855669703901982621)
        ·
          refine ⟨39673246070876138963243483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105795322855669703901982621 39673246070876138963243483)
          ·
            refine ⟨59509869106314208444865225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39673246070876138963243483 59509869106314208444865225)
            ·
              refine ⟨44632401829735656333648919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59509869106314208444865225 44632401829735656333648919)
              ·
                refine ⟨66948602744603484500473379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44632401829735656333648919 66948602744603484500473379)
                ·
                  refine ⟨100422904116905226750710069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66948602744603484500473379 100422904116905226750710069)
                  ·
                    refine ⟨9414647260959865007879069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100422904116905226750710069 9414647260959865007879069)
                    ·
                      refine ⟨3530492722859949377954651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9414647260959865007879069 3530492722859949377954651)
                      ·
                        rfl

theorem cell23_6875610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_6875610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875610 prefixEnd_6875610 := by exact prefixLift 6875610
  have htrace : WordTrace (prefixWord ++ tailWord_6875610) baseStart_6875610 baseEnd_6875610 := by
    simpa [prefixWord, tailWord_6875610, baseEnd_6875610] using wordTrace_append hprefix tailTrace_6875610
  have hstable : (prefixWord ++ tailWord_6875610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875610).length < 2 ^ (prefixWord ++ tailWord_6875610).sum := by decide
  have hdescent : baseEnd_6875610 < baseStart_6875610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875661 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6875661 : Nat := 118140960795 + 6875661 * 2 ^ 59
def prefixEnd_6875661 : Nat := 4983230072969 + 3 ^ 40 * 6875661 * 2
def baseEnd_6875661 : Nat := 3530518910373328678416917

theorem tailTrace_6875661 : CollatzResearch.WordTrace tailWord_6875661 prefixEnd_6875661 3530518910373328678416917 := by
  unfold tailWord_6875661
  simp only [CollatzResearch.WordTrace]
  refine ⟨250775958743661941255546837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167183972495774627503697891 250775958743661941255546837)
  ·
    refine ⟨5877561533054576748176879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 250775958743661941255546837 5877561533054576748176879)
    ·
      refine ⟨8816342299581865122265319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877561533054576748176879 8816342299581865122265319)
      ·
        refine ⟨13224513449372797683397979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816342299581865122265319 13224513449372797683397979)
        ·
          refine ⟨19836770174059196525096969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13224513449372797683397979 19836770174059196525096969)
          ·
            refine ⟨14877577630544397393822727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19836770174059196525096969 14877577630544397393822727)
            ·
              refine ⟨22316366445816596090734091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14877577630544397393822727 22316366445816596090734091)
              ·
                refine ⟨33474549668724894136101137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22316366445816596090734091 33474549668724894136101137)
                ·
                  refine ⟨25105912251543670602075853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33474549668724894136101137 25105912251543670602075853)
                  ·
                    refine ⟨9414717094328876475778445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25105912251543670602075853 9414717094328876475778445)
                    ·
                      refine ⟨3530518910373328678416917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9414717094328876475778445 3530518910373328678416917)
                      ·
                        rfl

theorem cell23_6875661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6875661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875661 prefixEnd_6875661 := by exact prefixLift 6875661
  have htrace : WordTrace (prefixWord ++ tailWord_6875661) baseStart_6875661 baseEnd_6875661 := by
    simpa [prefixWord, tailWord_6875661, baseEnd_6875661] using wordTrace_append hprefix tailTrace_6875661
  have hstable : (prefixWord ++ tailWord_6875661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875661).length < 2 ^ (prefixWord ++ tailWord_6875661).sum := by decide
  have hdescent : baseEnd_6875661 < baseStart_6875661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875667 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 2, 4, 2]
def baseStart_6875667 : Nat := 118140960795 + 6875667 * 2 ^ 59
def prefixEnd_6875667 : Nat := 4983230072969 + 3 ^ 40 * 6875667 * 2
def baseEnd_6875667 : Nat := 3530521991257255654941889

theorem tailTrace_6875667 : CollatzResearch.WordTrace tailWord_6875667 prefixEnd_6875667 3530521991257255654941889 := by
  unfold tailWord_6875667
  simp only [CollatzResearch.WordTrace]
  refine ⟨250776177581640204280265255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167184118387760136186843503 250776177581640204280265255)
  ·
    refine ⟨376164266372460306420397883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250776177581640204280265255 376164266372460306420397883)
    ·
      refine ⟨564246399558690459630596825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376164266372460306420397883 564246399558690459630596825)
      ·
        refine ⟨423184799669017844722947619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564246399558690459630596825 423184799669017844722947619)
        ·
          refine ⟨634777199503526767084421429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423184799669017844722947619 634777199503526767084421429)
          ·
            refine ⟨59510362453455634414164509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 634777199503526767084421429 59510362453455634414164509)
            ·
              refine ⟨22316385920045862905311691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59510362453455634414164509 22316385920045862905311691)
              ·
                refine ⟨33474578880068794357967537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22316385920045862905311691 33474578880068794357967537)
                ·
                  refine ⟨25105934160051595768475653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33474578880068794357967537 25105934160051595768475653)
                  ·
                    refine ⟨4707362655009674206589185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25105934160051595768475653 4707362655009674206589185)
                    ·
                      refine ⟨3530521991257255654941889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707362655009674206589185 3530521991257255654941889)
                      ·
                        rfl

theorem cell23_6875667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4, 2].length) (baseStart_6875667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875667 prefixEnd_6875667 := by exact prefixLift 6875667
  have htrace : WordTrace (prefixWord ++ tailWord_6875667) baseStart_6875667 baseEnd_6875667 := by
    simpa [prefixWord, tailWord_6875667, baseEnd_6875667] using wordTrace_append hprefix tailTrace_6875667
  have hstable : (prefixWord ++ tailWord_6875667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875667).length < 2 ^ (prefixWord ++ tailWord_6875667).sum := by decide
  have hdescent : baseEnd_6875667 < baseStart_6875667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875677 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_6875677 : Nat := 118140960795 + 6875677 * 2 ^ 59
def prefixEnd_6875677 : Nat := 4983230072969 + 3 ^ 40 * 6875677 * 2
def baseEnd_6875677 : Nat := 1176842375354600205272281

theorem tailTrace_6875677 : CollatzResearch.WordTrace tailWord_6875677 prefixEnd_6875677 1176842375354600205272281 := by
  unfold tailWord_6875677
  simp only [CollatzResearch.WordTrace]
  refine ⟨250776542311603975988129285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167184361541069317325419523 250776542311603975988129285)
  ·
    refine ⟨47020601683425745497774241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250776542311603975988129285 47020601683425745497774241)
    ·
      refine ⟨35265451262569309123330681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47020601683425745497774241 35265451262569309123330681)
      ·
        refine ⟨26449088446926981842498011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35265451262569309123330681 26449088446926981842498011)
        ·
          refine ⟨39673632670390472763747017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26449088446926981842498011 39673632670390472763747017)
          ·
            refine ⟨29755224502792854572810263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39673632670390472763747017 29755224502792854572810263)
            ·
              refine ⟨44632836754189281859215395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29755224502792854572810263 44632836754189281859215395)
              ·
                refine ⟨66949255131283922788823093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44632836754189281859215395 66949255131283922788823093)
                ·
                  refine ⟨6276492668557867761452165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66949255131283922788823093 6276492668557867761452165)
                  ·
                    refine ⟨1176842375354600205272281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276492668557867761452165 1176842375354600205272281)
                    ·
                      rfl

theorem cell23_6875677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_6875677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875677 prefixEnd_6875677 := by exact prefixLift 6875677
  have htrace : WordTrace (prefixWord ++ tailWord_6875677) baseStart_6875677 baseEnd_6875677 := by
    simpa [prefixWord, tailWord_6875677, baseEnd_6875677] using wordTrace_append hprefix tailTrace_6875677
  have hstable : (prefixWord ++ tailWord_6875677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875677).length < 2 ^ (prefixWord ++ tailWord_6875677).sum := by decide
  have hdescent : baseEnd_6875677 < baseStart_6875677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875684 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6875684 : Nat := 118140960795 + 6875684 * 2 ^ 59
def prefixEnd_6875684 : Nat := 4983230072969 + 3 ^ 40 * 6875684 * 2
def baseEnd_6875684 : Nat := 3530530720428382088429311

theorem tailTrace_6875684 : CollatzResearch.WordTrace tailWord_6875684 prefixEnd_6875684 3530530720428382088429311 := by
  unfold tailWord_6875684
  simp only [CollatzResearch.WordTrace]
  refine ⟨125388398811289308091817053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167184531748385744122422737 125388398811289308091817053)
  ·
    refine ⟨47020649554233490534431395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125388398811289308091817053 47020649554233490534431395)
    ·
      refine ⟨70530974331350235801647093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47020649554233490534431395 70530974331350235801647093)
      ·
        refine ⟨6612278843564084606404415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70530974331350235801647093 6612278843564084606404415)
        ·
          refine ⟨9918418265346126909606623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612278843564084606404415 9918418265346126909606623)
          ·
            refine ⟨14877627398019190364409935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918418265346126909606623 14877627398019190364409935)
            ·
              refine ⟨22316441097028785546614903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14877627398019190364409935 22316441097028785546614903)
              ·
                refine ⟨33474661645543178319922355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22316441097028785546614903 33474661645543178319922355)
                ·
                  refine ⟨50211992468314767479883533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33474661645543178319922355 50211992468314767479883533)
                  ·
                    refine ⟨18829497175618037804956325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50211992468314767479883533 18829497175618037804956325)
                    ·
                      refine ⟨3530530720428382088429311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18829497175618037804956325 3530530720428382088429311)
                      ·
                        rfl

theorem cell23_6875684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6875684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875684 prefixEnd_6875684 := by exact prefixLift 6875684
  have htrace : WordTrace (prefixWord ++ tailWord_6875684) baseStart_6875684 baseEnd_6875684 := by
    simpa [prefixWord, tailWord_6875684, baseEnd_6875684] using wordTrace_append hprefix tailTrace_6875684
  have hstable : (prefixWord ++ tailWord_6875684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875684).length < 2 ^ (prefixWord ++ tailWord_6875684).sum := by decide
  have hdescent : baseEnd_6875684 < baseStart_6875684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875720 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_6875720 : Nat := 118140960795 + 6875720 * 2 ^ 59
def prefixEnd_6875720 : Nat := 4983230072969 + 3 ^ 40 * 6875720 * 2
def baseEnd_6875720 : Nat := 1176849735243981315859715

theorem tailTrace_6875720 : CollatzResearch.WordTrace tailWord_6875720 prefixEnd_6875720 1176849735243981315859715 := by
  unfold tailWord_6875720
  simp only [CollatzResearch.WordTrace]
  refine ⟨125389055325224097165972307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167185407100298796221296409 125389055325224097165972307)
  ·
    refine ⟨188083582987836145748958461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125389055325224097165972307 188083582987836145748958461)
    ·
      refine ⟨70531343620438554655859423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188083582987836145748958461 70531343620438554655859423)
      ·
        refine ⟨105797015430657831983789135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70531343620438554655859423 105797015430657831983789135)
        ·
          refine ⟨158695523145986747975683703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105797015430657831983789135 158695523145986747975683703)
          ·
            refine ⟨238043284718980121963525555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158695523145986747975683703 238043284718980121963525555)
            ·
              refine ⟨357064927078470182945288333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238043284718980121963525555 357064927078470182945288333)
              ·
                refine ⟨133899347654426318604483125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357064927078470182945288333 133899347654426318604483125)
                ·
                  refine ⟨12553063842602467369170293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133899347654426318604483125 12553063842602467369170293)
                  ·
                    refine ⟨1176849735243981315859715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12553063842602467369170293 1176849735243981315859715)
                    ·
                      rfl

theorem cell23_6875720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_6875720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875720 prefixEnd_6875720 := by exact prefixLift 6875720
  have htrace : WordTrace (prefixWord ++ tailWord_6875720) baseStart_6875720 baseEnd_6875720 := by
    simpa [prefixWord, tailWord_6875720, baseEnd_6875720] using wordTrace_append hprefix tailTrace_6875720
  have hstable : (prefixWord ++ tailWord_6875720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875720).length < 2 ^ (prefixWord ++ tailWord_6875720).sum := by decide
  have hdescent : baseEnd_6875720 < baseStart_6875720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875727 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 1, 5, 2]
def baseStart_6875727 : Nat := 118140960795 + 6875727 * 2 ^ 59
def prefixEnd_6875727 : Nat := 4983230072969 + 3 ^ 40 * 6875727 * 2
def baseEnd_6875727 : Nat := 3530552800096525420191613

theorem tailTrace_6875727 : CollatzResearch.WordTrace tailWord_6875727 prefixEnd_6875727 3530552800096525420191613 := by
  unfold tailWord_6875727
  simp only [CollatzResearch.WordTrace]
  refine ⟨250778365961422834527449435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167185577307615223018299623 250778365961422834527449435)
  ·
    refine ⟨376167548942134251791174153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250778365961422834527449435 376167548942134251791174153)
    ·
      refine ⟨282125661706600688843380615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376167548942134251791174153 282125661706600688843380615)
      ·
        refine ⟨423188492559901033265070923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282125661706600688843380615 423188492559901033265070923)
        ·
          refine ⟨634782738839851549897606385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423188492559901033265070923 634782738839851549897606385)
          ·
            refine ⟨476087054129888662423204789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634782738839851549897606385 476087054129888662423204789)
            ·
              refine ⟨44633161324677062102175449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476087054129888662423204789 44633161324677062102175449)
              ·
                refine ⟨33474870993507796576631587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44633161324677062102175449 33474870993507796576631587)
                ·
                  refine ⟨50212306490261694864947381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33474870993507796576631587 50212306490261694864947381)
                  ·
                    refine ⟨4707403733462033893588817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50212306490261694864947381 4707403733462033893588817)
                    ·
                      refine ⟨3530552800096525420191613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707403733462033893588817 3530552800096525420191613)
                      ·
                        rfl

theorem cell23_6875727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5, 2].length) (baseStart_6875727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875727 prefixEnd_6875727 := by exact prefixLift 6875727
  have htrace : WordTrace (prefixWord ++ tailWord_6875727) baseStart_6875727 baseEnd_6875727 := by
    simpa [prefixWord, tailWord_6875727, baseEnd_6875727] using wordTrace_append hprefix tailTrace_6875727
  have hstable : (prefixWord ++ tailWord_6875727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875727).length < 2 ^ (prefixWord ++ tailWord_6875727).sum := by decide
  have hdescent : baseEnd_6875727 < baseStart_6875727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875767 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 4, 4]
def baseStart_6875767 : Nat := 118140960795 + 6875767 * 2 ^ 59
def prefixEnd_6875767 : Nat := 4983230072969 + 3 ^ 40 * 6875767 * 2
def baseEnd_6875767 : Nat := 1176857779774235087897143

theorem tailTrace_6875767 : CollatzResearch.WordTrace tailWord_6875767 prefixEnd_6875767 1176857779774235087897143 := by
  unfold tailWord_6875767
  simp only [CollatzResearch.WordTrace]
  refine ⟨250779824881277921358905555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167186549920851947572603703 250779824881277921358905555)
  ·
    refine ⟨376169737321916882038358333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250779824881277921358905555 376169737321916882038358333)
    ·
      refine ⟨141063651495718830764384375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376169737321916882038358333 141063651495718830764384375)
      ·
        refine ⟨211595477243578246146576563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141063651495718830764384375 211595477243578246146576563)
        ·
          refine ⟨317393215865367369219864845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211595477243578246146576563 317393215865367369219864845)
          ·
            refine ⟨119022455949512763457449317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317393215865367369219864845 119022455949512763457449317)
            ·
              refine ⟨22316710490533643148271747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119022455949512763457449317 22316710490533643148271747)
              ·
                refine ⟨33475065735800464722407621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22316710490533643148271747 33475065735800464722407621)
                ·
                  refine ⟨6276574825462587135451429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33475065735800464722407621 6276574825462587135451429)
                  ·
                    refine ⟨1176857779774235087897143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276574825462587135451429 1176857779774235087897143)
                    ·
                      rfl

theorem cell23_6875767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_6875767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875767 prefixEnd_6875767 := by exact prefixLift 6875767
  have htrace : WordTrace (prefixWord ++ tailWord_6875767) baseStart_6875767 baseEnd_6875767 := by
    simpa [prefixWord, tailWord_6875767, baseEnd_6875767] using wordTrace_append hprefix tailTrace_6875767
  have hstable : (prefixWord ++ tailWord_6875767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875767).length < 2 ^ (prefixWord ++ tailWord_6875767).sum := by decide
  have hdescent : baseEnd_6875767 < baseStart_6875767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875777 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6875777 : Nat := 118140960795 + 6875777 * 2 ^ 59
def prefixEnd_6875777 : Nat := 4983230072969 + 3 ^ 40 * 6875777 * 2
def baseEnd_6875777 : Nat := 3530578474129250224566383

theorem tailTrace_6875777 : CollatzResearch.WordTrace tailWord_6875777 prefixEnd_6875777 3530578474129250224566383 := by
  unfold tailWord_6875777
  simp only [CollatzResearch.WordTrace]
  refine ⟨250780189611241693066769585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167186793074161128711179723 250780189611241693066769585)
  ·
    refine ⟨188085142208431269800077189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250780189611241693066769585 188085142208431269800077189)
    ·
      refine ⟨35265964164080863087514473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188085142208431269800077189 35265964164080863087514473)
      ·
        refine ⟨26449473123060647315635855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35265964164080863087514473 26449473123060647315635855)
        ·
          refine ⟨39674209684590970973453783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26449473123060647315635855 39674209684590970973453783)
          ·
            refine ⟨59511314526886456460180675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39674209684590970973453783 59511314526886456460180675)
            ·
              refine ⟨89266971790329684690271013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59511314526886456460180675 89266971790329684690271013)
              ·
                refine ⟨16737557210686815879425815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89266971790329684690271013 16737557210686815879425815)
                ·
                  refine ⟨25106335816030223819138723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16737557210686815879425815 25106335816030223819138723)
                  ·
                    refine ⟨37659503724045335728708085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25106335816030223819138723 37659503724045335728708085)
                    ·
                      refine ⟨3530578474129250224566383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37659503724045335728708085 3530578474129250224566383)
                      ·
                        rfl

theorem cell23_6875777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6875777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875777 prefixEnd_6875777 := by exact prefixLift 6875777
  have htrace : WordTrace (prefixWord ++ tailWord_6875777) baseStart_6875777 baseEnd_6875777 := by
    simpa [prefixWord, tailWord_6875777, baseEnd_6875777] using wordTrace_append hprefix tailTrace_6875777
  have hstable : (prefixWord ++ tailWord_6875777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875777).length < 2 ^ (prefixWord ++ tailWord_6875777).sum := by decide
  have hdescent : baseEnd_6875777 < baseStart_6875777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875804 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6875804 : Nat := 118140960795 + 6875804 * 2 ^ 59
def prefixEnd_6875804 : Nat := 4983230072969 + 3 ^ 40 * 6875804 * 2
def baseEnd_6875804 : Nat := 3530592338106921618928759

theorem tailTrace_6875804 : CollatzResearch.WordTrace tailWord_6875804 prefixEnd_6875804 3530592338106921618928759 := by
  unfold tailWord_6875804
  simp only [CollatzResearch.WordTrace]
  refine ⟨125390587191071938339001233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167187449588095917785334977 125390587191071938339001233)
  ·
    refine ⟨94042940393303953754250925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125390587191071938339001233 94042940393303953754250925)
    ·
      refine ⟨35266102647488982657844097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94042940393303953754250925 35266102647488982657844097)
      ·
        refine ⟨26449576985616736993383073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35266102647488982657844097 26449576985616736993383073)
        ·
          refine ⟨19837182739212552745037305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26449576985616736993383073 19837182739212552745037305)
          ·
            refine ⟨14877887054409414558777979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19837182739212552745037305 14877887054409414558777979)
            ·
              refine ⟨22316830581614121838166969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14877887054409414558777979 22316830581614121838166969)
              ·
                refine ⟨16737622936210591378625227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22316830581614121838166969 16737622936210591378625227)
                ·
                  refine ⟨25106434404315887067937841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16737622936210591378625227 25106434404315887067937841)
                  ·
                    refine ⟨18829825803236915300953381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25106434404315887067937841 18829825803236915300953381)
                    ·
                      refine ⟨3530592338106921618928759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18829825803236915300953381 3530592338106921618928759)
                      ·
                        rfl

theorem cell23_6875804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6875804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875804 prefixEnd_6875804 := by exact prefixLift 6875804
  have htrace : WordTrace (prefixWord ++ tailWord_6875804) baseStart_6875804 baseEnd_6875804 := by
    simpa [prefixWord, tailWord_6875804, baseEnd_6875804] using wordTrace_append hprefix tailTrace_6875804
  have hstable : (prefixWord ++ tailWord_6875804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875804).length < 2 ^ (prefixWord ++ tailWord_6875804).sum := by decide
  have hdescent : baseEnd_6875804 < baseStart_6875804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875820 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_6875820 : Nat := 118140960795 + 6875820 * 2 ^ 59
def prefixEnd_6875820 : Nat := 4983230072969 + 3 ^ 40 * 6875820 * 2
def baseEnd_6875820 : Nat := 3530600553797393556328685

theorem tailTrace_6875820 : CollatzResearch.WordTrace tailWord_6875820 prefixEnd_6875820 3530600553797393556328685 := by
  unfold tailWord_6875820
  simp only [CollatzResearch.WordTrace]
  refine ⟨125390878975042955705292457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167187838633390607607056609 125390878975042955705292457)
  ·
    refine ⟨94043159231282216778969343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125390878975042955705292457 94043159231282216778969343)
    ·
      refine ⟨141064738846923325168454015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94043159231282216778969343 141064738846923325168454015)
      ·
        refine ⟨211597108270384987752681023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141064738846923325168454015 211597108270384987752681023)
        ·
          refine ⟨317395662405577481629021535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211597108270384987752681023 317395662405577481629021535)
          ·
            refine ⟨476093493608366222443532303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317395662405577481629021535 476093493608366222443532303)
            ·
              refine ⟨714140240412549333665298455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476093493608366222443532303 714140240412549333665298455)
              ·
                refine ⟨1071210360618824000497947683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714140240412549333665298455 1071210360618824000497947683)
                ·
                  refine ⟨1606815540928236000746921525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071210360618824000497947683 1606815540928236000746921525)
                  ·
                    refine ⟨150638956962022125070023893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1606815540928236000746921525 150638956962022125070023893)
                    ·
                      refine ⟨3530600553797393556328685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150638956962022125070023893 3530600553797393556328685)
                      ·
                        rfl

theorem cell23_6875820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_6875820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875820 prefixEnd_6875820 := by exact prefixLift 6875820
  have htrace : WordTrace (prefixWord ++ tailWord_6875820) baseStart_6875820 baseEnd_6875820 := by
    simpa [prefixWord, tailWord_6875820, baseEnd_6875820] using wordTrace_append hprefix tailTrace_6875820
  have hstable : (prefixWord ++ tailWord_6875820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875820).length < 2 ^ (prefixWord ++ tailWord_6875820).sum := by decide
  have hdescent : baseEnd_6875820 < baseStart_6875820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875834 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2]
def baseStart_6875834 : Nat := 118140960795 + 6875834 * 2 ^ 59
def prefixEnd_6875834 : Nat := 4983230072969 + 3 ^ 40 * 6875834 * 2
def baseEnd_6875834 : Nat := 3530607742526556501553621

theorem tailTrace_6875834 : CollatzResearch.WordTrace tailWord_6875834 prefixEnd_6875834 3530607742526556501553621 := by
  unfold tailWord_6875834
  simp only [CollatzResearch.WordTrace]
  refine ⟨62695567143008797950398639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167188179048023461201063037 62695567143008797950398639)
  ·
    refine ⟨94043350714513196925597959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62695567143008797950398639 94043350714513196925597959)
    ·
      refine ⟨141065026071769795388396939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94043350714513196925597959 141065026071769795388396939)
      ·
        refine ⟨211597539107654693082595409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141065026071769795388396939 211597539107654693082595409)
        ·
          refine ⟨158698154330741019811946557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211597539107654693082595409 158698154330741019811946557)
          ·
            refine ⟨59511807874027882429479959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158698154330741019811946557 59511807874027882429479959)
            ·
              refine ⟨89267711811041823644219939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59511807874027882429479959 89267711811041823644219939)
              ·
                refine ⟨133901567716562735466329909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89267711811041823644219939 133901567716562735466329909)
                ·
                  refine ⟨12553271973427756449968429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133901567716562735466329909 12553271973427756449968429)
                  ·
                    refine ⟨4707476990035408668738161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12553271973427756449968429 4707476990035408668738161)
                    ·
                      refine ⟨3530607742526556501553621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707476990035408668738161 3530607742526556501553621)
                      ·
                        rfl

theorem cell23_6875834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_6875834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875834 prefixEnd_6875834 := by exact prefixLift 6875834
  have htrace : WordTrace (prefixWord ++ tailWord_6875834) baseStart_6875834 baseEnd_6875834 := by
    simpa [prefixWord, tailWord_6875834, baseEnd_6875834] using wordTrace_append hprefix tailTrace_6875834
  have hstable : (prefixWord ++ tailWord_6875834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875834).length < 2 ^ (prefixWord ++ tailWord_6875834).sum := by decide
  have hdescent : baseEnd_6875834 < baseStart_6875834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875887 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 7]
def baseStart_6875887 : Nat := 118140960795 + 6875887 * 2 ^ 59
def prefixEnd_6875887 : Nat := 4983230072969 + 3 ^ 40 * 6875887 * 2
def baseEnd_6875887 : Nat := 392292773000138310465653

theorem tailTrace_6875887 : CollatzResearch.WordTrace tailWord_6875887 prefixEnd_6875887 392292773000138310465653 := by
  unfold tailWord_6875887
  simp only [CollatzResearch.WordTrace]
  refine ⟨250784201640843181853273915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167189467760562121235515943 250784201640843181853273915)
  ·
    refine ⟨376176302461264772779910873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250784201640843181853273915 376176302461264772779910873)
    ·
      refine ⟨282132226845948579584933155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376176302461264772779910873 282132226845948579584933155)
      ·
        refine ⟨423198340268922869377399733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282132226845948579584933155 423198340268922869377399733)
        ·
          refine ⟨39674844400211519004131225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 423198340268922869377399733 39674844400211519004131225)
          ·
            refine ⟨29756133300158639253098419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39674844400211519004131225 29756133300158639253098419)
            ·
              refine ⟨44634199950237958879647629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29756133300158639253098419 44634199950237958879647629)
              ·
                refine ⟨16737824981339234579867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44634199950237958879647629 16737824981339234579867861)
                ·
                  refine ⟨392292773000138310465653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16737824981339234579867861 392292773000138310465653)
                  ·
                    rfl

theorem cell23_6875887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 7].length) (baseStart_6875887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875887 prefixEnd_6875887 := by exact prefixLift 6875887
  have htrace : WordTrace (prefixWord ++ tailWord_6875887) baseStart_6875887 baseEnd_6875887 := by
    simpa [prefixWord, tailWord_6875887, baseEnd_6875887] using wordTrace_append hprefix tailTrace_6875887
  have hstable : (prefixWord ++ tailWord_6875887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875887).length < 2 ^ (prefixWord ++ tailWord_6875887).sum := by decide
  have hdescent : baseEnd_6875887 < baseStart_6875887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875892 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6875892 : Nat := 118140960795 + 6875892 * 2 ^ 59
def prefixEnd_6875892 : Nat := 4983230072969 + 3 ^ 40 * 6875892 * 2
def baseEnd_6875892 : Nat := 3530637524404517274628355

theorem tailTrace_6875892 : CollatzResearch.WordTrace tailWord_6875892 prefixEnd_6875892 3530637524404517274628355 := by
  unfold tailWord_6875892
  simp only [CollatzResearch.WordTrace]
  refine ⟨125392192002912533853602965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167189589337216711804803953 125392192002912533853602965)
  ·
    refine ⟨5877759000136525024387639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125392192002912533853602965 5877759000136525024387639)
    ·
      refine ⟨8816638500204787536581459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877759000136525024387639 8816638500204787536581459)
      ·
        refine ⟨13224957750307181304872189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816638500204787536581459 13224957750307181304872189)
        ·
          refine ⟨4959359156365192989327071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13224957750307181304872189 4959359156365192989327071)
          ·
            refine ⟨7439038734547789483990607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959359156365192989327071 7439038734547789483990607)
            ·
              refine ⟨11158558101821684225985911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7439038734547789483990607 11158558101821684225985911)
              ·
                refine ⟨16737837152732526338978867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11158558101821684225985911 16737837152732526338978867)
                ·
                  refine ⟨25106755729098789508468301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16737837152732526338978867 25106755729098789508468301)
                  ·
                    refine ⟨9415033398412046065675613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25106755729098789508468301 9415033398412046065675613)
                    ·
                      refine ⟨3530637524404517274628355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9415033398412046065675613 3530637524404517274628355)
                      ·
                        rfl

theorem cell23_6875892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6875892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875892 prefixEnd_6875892 := by exact prefixLift 6875892
  have htrace : WordTrace (prefixWord ++ tailWord_6875892) baseStart_6875892 baseEnd_6875892 := by
    simpa [prefixWord, tailWord_6875892, baseEnd_6875892] using wordTrace_append hprefix tailTrace_6875892
  have hstable : (prefixWord ++ tailWord_6875892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875892).length < 2 ^ (prefixWord ++ tailWord_6875892).sum := by decide
  have hdescent : baseEnd_6875892 < baseStart_6875892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875894 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6875894 : Nat := 118140960795 + 6875894 * 2 ^ 59
def prefixEnd_6875894 : Nat := 4983230072969 + 3 ^ 40 * 6875894 * 2
def baseEnd_6875894 : Nat := 3530638551365826266803345

theorem tailTrace_6875894 : CollatzResearch.WordTrace tailWord_6875894 prefixEnd_6875894 3530638551365826266803345 := by
  unfold tailWord_6875894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674028559488613878048671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167189637967878548032519157 15674028559488613878048671)
  ·
    refine ⟨23511042839232920817073007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674028559488613878048671 23511042839232920817073007)
    ·
      refine ⟨35266564258849381225609511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23511042839232920817073007 35266564258849381225609511)
      ·
        refine ⟨52899846388274071838414267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35266564258849381225609511 52899846388274071838414267)
        ·
          refine ⟨79349769582411107757621401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52899846388274071838414267 79349769582411107757621401)
          ·
            refine ⟨59512327186808330818216051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79349769582411107757621401 59512327186808330818216051)
            ·
              refine ⟨89268490780212496227324077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59512327186808330818216051 89268490780212496227324077)
              ·
                refine ⟨33475684042579686085246529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89268490780212496227324077 33475684042579686085246529)
                ·
                  refine ⟨25106763031934764563934897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33475684042579686085246529 25106763031934764563934897)
                  ·
                    refine ⟨18830072273951073422951173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25106763031934764563934897 18830072273951073422951173)
                    ·
                      refine ⟨3530638551365826266803345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18830072273951073422951173 3530638551365826266803345)
                      ·
                        rfl

theorem cell23_6875894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6875894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875894 prefixEnd_6875894 := by exact prefixLift 6875894
  have htrace : WordTrace (prefixWord ++ tailWord_6875894) baseStart_6875894 baseEnd_6875894 := by
    simpa [prefixWord, tailWord_6875894, baseEnd_6875894] using wordTrace_append hprefix tailTrace_6875894
  have hstable : (prefixWord ++ tailWord_6875894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875894).length < 2 ^ (prefixWord ++ tailWord_6875894).sum := by decide
  have hdescent : baseEnd_6875894 < baseStart_6875894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875938 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_6875938 : Nat := 118140960795 + 6875938 * 2 ^ 59
def prefixEnd_6875938 : Nat := 4983230072969 + 3 ^ 40 * 6875938 * 2
def baseEnd_6875938 : Nat := 392295682723847121628127

theorem tailTrace_6875938 : CollatzResearch.WordTrace tailWord_6875938 prefixEnd_6875938 392295682723847121628127 := by
  unfold tailWord_6875938
  simp only [CollatzResearch.WordTrace]
  refine ⟨62696515440914604390845117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167190707842438945042253645 62696515440914604390845117)
  ·
    refine ⟨23511193290342976646566919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62696515440914604390845117 23511193290342976646566919)
    ·
      refine ⟨35266789935514464969850379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23511193290342976646566919 35266789935514464969850379)
      ·
        refine ⟨52900184903271697454775569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35266789935514464969850379 52900184903271697454775569)
        ·
          refine ⟨39675138677453773091081677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52900184903271697454775569 39675138677453773091081677)
          ·
            refine ⟨14878177004045164909155629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39675138677453773091081677 14878177004045164909155629)
            ·
              refine ⟨5579316376516936840933361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14878177004045164909155629 5579316376516936840933361)
              ·
                refine ⟨4184487282387702630700021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579316376516936840933361 4184487282387702630700021)
                ·
                  refine ⟨392295682723847121628127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184487282387702630700021 392295682723847121628127)
                  ·
                    rfl

theorem cell23_6875938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_6875938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875938 prefixEnd_6875938 := by exact prefixLift 6875938
  have htrace : WordTrace (prefixWord ++ tailWord_6875938) baseStart_6875938 baseEnd_6875938 := by
    simpa [prefixWord, tailWord_6875938, baseEnd_6875938] using wordTrace_append hprefix tailTrace_6875938
  have hstable : (prefixWord ++ tailWord_6875938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875938).length < 2 ^ (prefixWord ++ tailWord_6875938).sum := by decide
  have hdescent : baseEnd_6875938 < baseStart_6875938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875944 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6875944 : Nat := 118140960795 + 6875944 * 2 ^ 59
def prefixEnd_6875944 : Nat := 4983230072969 + 3 ^ 40 * 6875944 * 2
def baseEnd_6875944 : Nat := 3530664225398551071178115

theorem tailTrace_6875944 : CollatzResearch.WordTrace tailWord_6875944 prefixEnd_6875944 3530664225398551071178115 := by
  unfold tailWord_6875944
  simp only [CollatzResearch.WordTrace]
  refine ⟨125393140300818340294049443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167190853734424453725399257 125393140300818340294049443)
  ·
    refine ⟨188089710451227510441074165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125393140300818340294049443 188089710451227510441074165)
    ·
      refine ⟨17633410354802579103850703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188089710451227510441074165 17633410354802579103850703)
      ·
        refine ⟨26450115532203868655776055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17633410354802579103850703 26450115532203868655776055)
        ·
          refine ⟨39675173298305802983664083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26450115532203868655776055 39675173298305802983664083)
          ·
            refine ⟨59512759947458704475496125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39675173298305802983664083 59512759947458704475496125)
            ·
              refine ⟨22317284980297014178311047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59512759947458704475496125 22317284980297014178311047)
              ·
                refine ⟨33475927470445521267466571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22317284980297014178311047 33475927470445521267466571)
                ·
                  refine ⟨50213891205668281901199857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33475927470445521267466571 50213891205668281901199857)
                  ·
                    refine ⟨37660418404251211425899893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50213891205668281901199857 37660418404251211425899893)
                    ·
                      refine ⟨3530664225398551071178115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37660418404251211425899893 3530664225398551071178115)
                      ·
                        rfl

theorem cell23_6875944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6875944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875944 prefixEnd_6875944 := by exact prefixLift 6875944
  have htrace : WordTrace (prefixWord ++ tailWord_6875944) baseStart_6875944 baseEnd_6875944 := by
    simpa [prefixWord, tailWord_6875944, baseEnd_6875944] using wordTrace_append hprefix tailTrace_6875944
  have hstable : (prefixWord ++ tailWord_6875944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875944).length < 2 ^ (prefixWord ++ tailWord_6875944).sum := by decide
  have hdescent : baseEnd_6875944 < baseStart_6875944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875954 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_6875954 : Nat := 118140960795 + 6875954 * 2 ^ 59
def prefixEnd_6875954 : Nat := 4983230072969 + 3 ^ 40 * 6875954 * 2
def baseEnd_6875954 : Nat := 3530669360205096032053069

theorem tailTrace_6875954 : CollatzResearch.WordTrace tailWord_6875954 prefixEnd_6875954 3530669360205096032053069 := by
  unfold tailWord_6875954
  simp only [CollatzResearch.WordTrace]
  refine ⟨62696661332900113073990729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167191096887733634863975277 62696661332900113073990729)
  ·
    refine ⟨47022495999675084805493047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62696661332900113073990729 47022495999675084805493047)
    ·
      refine ⟨70533743999512627208239571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47022495999675084805493047 70533743999512627208239571)
      ·
        refine ⟨105800615999268940812359357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70533743999512627208239571 105800615999268940812359357)
        ·
          refine ⟨39675230999725852804634759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105800615999268940812359357 39675230999725852804634759)
          ·
            refine ⟨59512846499588779206952139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39675230999725852804634759 59512846499588779206952139)
            ·
              refine ⟨89269269749383168810428209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59512846499588779206952139 89269269749383168810428209)
              ·
                refine ⟨66951952312037376607821157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89269269749383168810428209 66951952312037376607821157)
                ·
                  refine ⟨12553491058507008113966467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66951952312037376607821157 12553491058507008113966467)
                  ·
                    refine ⟨18830236587760512170949701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12553491058507008113966467 18830236587760512170949701)
                    ·
                      refine ⟨3530669360205096032053069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18830236587760512170949701 3530669360205096032053069)
                      ·
                        rfl

theorem cell23_6875954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_6875954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875954 prefixEnd_6875954 := by exact prefixLift 6875954
  have htrace : WordTrace (prefixWord ++ tailWord_6875954) baseStart_6875954 baseEnd_6875954 := by
    simpa [prefixWord, tailWord_6875954, baseEnd_6875954] using wordTrace_append hprefix tailTrace_6875954
  have hstable : (prefixWord ++ tailWord_6875954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875954).length < 2 ^ (prefixWord ++ tailWord_6875954).sum := by decide
  have hdescent : baseEnd_6875954 < baseStart_6875954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875964 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_6875964 : Nat := 118140960795 + 6875964 * 2 ^ 59
def prefixEnd_6875964 : Nat := 4983230072969 + 3 ^ 40 * 6875964 * 2
def baseEnd_6875964 : Nat := 1176891498337213664309341

theorem tailTrace_6875964 : CollatzResearch.WordTrace tailWord_6875964 prefixEnd_6875964 1176891498337213664309341 := by
  unfold tailWord_6875964
  simp only [CollatzResearch.WordTrace]
  refine ⟨125393505030782112001913473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167191340041042816002551297 125393505030782112001913473)
  ·
    refine ⟨94045128773086584001435105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125393505030782112001913473 94045128773086584001435105)
    ·
      refine ⟨70533846579814938001076329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94045128773086584001435105 70533846579814938001076329)
      ·
        refine ⟨52900384934861203500807247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70533846579814938001076329 52900384934861203500807247)
        ·
          refine ⟨79350577402291805251210871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52900384934861203500807247 79350577402291805251210871)
          ·
            refine ⟨119025866103437707876816307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79350577402291805251210871 119025866103437707876816307)
            ·
              refine ⟨178538799155156561815224461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119025866103437707876816307 178538799155156561815224461)
              ·
                refine ⟨66952049683183710680709173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178538799155156561815224461 66952049683183710680709173)
                ·
                  refine ⟨6276754657798472876316485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66952049683183710680709173 6276754657798472876316485)
                  ·
                    refine ⟨1176891498337213664309341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276754657798472876316485 1176891498337213664309341)
                    ·
                      rfl

theorem cell23_6875964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_6875964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875964 prefixEnd_6875964 := by exact prefixLift 6875964
  have htrace : WordTrace (prefixWord ++ tailWord_6875964) baseStart_6875964 baseEnd_6875964 := by
    simpa [prefixWord, tailWord_6875964, baseEnd_6875964] using wordTrace_append hprefix tailTrace_6875964
  have hstable : (prefixWord ++ tailWord_6875964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875964).length < 2 ^ (prefixWord ++ tailWord_6875964).sum := by decide
  have hdescent : baseEnd_6875964 < baseStart_6875964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875991 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_6875991 : Nat := 118140960795 + 6875991 * 2 ^ 59
def prefixEnd_6875991 : Nat := 4983230072969 + 3 ^ 40 * 6875991 * 2
def baseEnd_6875991 : Nat := 3530688358989312387290399

theorem tailTrace_6875991 : CollatzResearch.WordTrace tailWord_6875991 prefixEnd_6875991 3530688358989312387290399 := by
  unfold tailWord_6875991
  simp only [CollatzResearch.WordTrace]
  refine ⟨250787994832466407615059827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167191996554977605076706551 250787994832466407615059827)
  ·
    refine ⟨376181992248699611422589741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250787994832466407615059827 376181992248699611422589741)
    ·
      refine ⟨141068247093262354283471153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376181992248699611422589741 141068247093262354283471153)
      ·
        refine ⟨105801185319946765712603365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141068247093262354283471153 105801185319946765712603365)
        ·
          refine ⟨19837722247490018571113131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105801185319946765712603365 19837722247490018571113131)
          ·
            refine ⟨29756583371235027856669697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19837722247490018571113131 29756583371235027856669697)
            ·
              refine ⟨22317437528426270892502273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29756583371235027856669697 22317437528426270892502273)
              ·
                refine ⟨16738078146319703169376705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22317437528426270892502273 16738078146319703169376705)
                ·
                  refine ⟨12553558609739777377032529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16738078146319703169376705 12553558609739777377032529)
                  ·
                    refine ⟨9415168957304833032774397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12553558609739777377032529 9415168957304833032774397)
                    ·
                      refine ⟨3530688358989312387290399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9415168957304833032774397 3530688358989312387290399)
                      ·
                        rfl

theorem cell23_6875991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_6875991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875991 prefixEnd_6875991 := by exact prefixLift 6875991
  have htrace : WordTrace (prefixWord ++ tailWord_6875991) baseStart_6875991 baseEnd_6875991 := by
    simpa [prefixWord, tailWord_6875991, baseEnd_6875991] using wordTrace_append hprefix tailTrace_6875991
  have hstable : (prefixWord ++ tailWord_6875991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875991).length < 2 ^ (prefixWord ++ tailWord_6875991).sum := by decide
  have hdescent : baseEnd_6875991 < baseStart_6875991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6875994 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_6875994 : Nat := 118140960795 + 6875994 * 2 ^ 59
def prefixEnd_6875994 : Nat := 4983230072969 + 3 ^ 40 * 6875994 * 2
def baseEnd_6875994 : Nat := 392298877714586208394765

theorem tailTrace_6875994 : CollatzResearch.WordTrace tailWord_6875994 prefixEnd_6875994 392298877714586208394765 := by
  unfold tailWord_6875994
  simp only [CollatzResearch.WordTrace]
  refine ⟨62697026062863884781854759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167192069500970359418279357 62697026062863884781854759)
  ·
    refine ⟨94045539094295827172782139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62697026062863884781854759 94045539094295827172782139)
    ·
      refine ⟨141068308641443740759173209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94045539094295827172782139 141068308641443740759173209)
      ·
        refine ⟨105801231481082805569379907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141068308641443740759173209 105801231481082805569379907)
        ·
          refine ⟨158701847221624208354069861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105801231481082805569379907 158701847221624208354069861)
          ·
            refine ⟨29756596354054539066388099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158701847221624208354069861 29756596354054539066388099)
            ·
              refine ⟨44634894531081808599582149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29756596354054539066388099 44634894531081808599582149)
              ·
                refine ⟨8369042724577839112421653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44634894531081808599582149 8369042724577839112421653)
                ·
                  refine ⟨392298877714586208394765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8369042724577839112421653 392298877714586208394765)
                  ·
                    rfl

theorem cell23_6875994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_6875994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6875994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6875994 prefixEnd_6875994 := by exact prefixLift 6875994
  have htrace : WordTrace (prefixWord ++ tailWord_6875994) baseStart_6875994 baseEnd_6875994 := by
    simpa [prefixWord, tailWord_6875994, baseEnd_6875994] using wordTrace_append hprefix tailTrace_6875994
  have hstable : (prefixWord ++ tailWord_6875994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6875994).length < 2 ^ (prefixWord ++ tailWord_6875994).sum := by decide
  have hdescent : baseEnd_6875994 < baseStart_6875994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6875994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876041 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 1, 5]
def baseStart_6876041 : Nat := 118140960795 + 6876041 * 2 ^ 59
def prefixEnd_6876041 : Nat := 4983230072969 + 3 ^ 40 * 6876041 * 2
def baseEnd_6876041 : Nat := 1176904677674012397221723

theorem tailTrace_6876041 : CollatzResearch.WordTrace tailWord_6876041 prefixEnd_6876041 1176904677674012397221723 := by
  unfold tailWord_6876041
  simp only [CollatzResearch.WordTrace]
  refine ⟨250789818482285266154379977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167193212321523510769586651 250789818482285266154379977)
  ·
    refine ⟨188092363861713949615784983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250789818482285266154379977 188092363861713949615784983)
    ·
      refine ⟨282138545792570924423677475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188092363861713949615784983 282138545792570924423677475)
      ·
        refine ⟨423207818688856386635516213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282138545792570924423677475 423207818688856386635516213)
        ·
          refine ⟨39675733002080286247079645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 423207818688856386635516213 39675733002080286247079645)
          ·
            refine ⟨14878399875780107342654867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39675733002080286247079645 14878399875780107342654867)
            ·
              refine ⟨22317599813670161013982301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14878399875780107342654867 22317599813670161013982301)
              ·
                refine ⟨8369099930126310380243363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22317599813670161013982301 8369099930126310380243363)
                ·
                  refine ⟨12553649895189465570365045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8369099930126310380243363 12553649895189465570365045)
                  ·
                    refine ⟨1176904677674012397221723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12553649895189465570365045 1176904677674012397221723)
                    ·
                      rfl

theorem cell23_6876041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_6876041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876041 prefixEnd_6876041 := by exact prefixLift 6876041
  have htrace : WordTrace (prefixWord ++ tailWord_6876041) baseStart_6876041 baseEnd_6876041 := by
    simpa [prefixWord, tailWord_6876041, baseEnd_6876041] using wordTrace_append hprefix tailTrace_6876041
  have hstable : (prefixWord ++ tailWord_6876041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876041).length < 2 ^ (prefixWord ++ tailWord_6876041).sum := by decide
  have hdescent : baseEnd_6876041 < baseStart_6876041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876064 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_6876064 : Nat := 118140960795 + 6876064 * 2 ^ 59
def prefixEnd_6876064 : Nat := 4983230072969 + 3 ^ 40 * 6876064 * 2
def baseEnd_6876064 : Nat := 3530725843077090601677563

theorem tailTrace_6876064 : CollatzResearch.WordTrace tailWord_6876064 prefixEnd_6876064 3530725843077090601677563 := by
  unfold tailWord_6876064
  simp only [CollatzResearch.WordTrace]
  refine ⟨125395328680600970541233623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167193771574134627388311497 125395328680600970541233623)
  ·
    refine ⟨188092993020901455811850435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125395328680600970541233623 188092993020901455811850435)
    ·
      refine ⟨282139489531352183717775653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188092993020901455811850435 282139489531352183717775653)
      ·
        refine ⟨52901154287128534447082935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282139489531352183717775653 52901154287128534447082935)
        ·
          refine ⟨79351731430692801670624403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52901154287128534447082935 79351731430692801670624403)
          ·
            refine ⟨119027597146039202505936605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79351731430692801670624403 119027597146039202505936605)
            ·
              refine ⟨44635348929764700939726227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119027597146039202505936605 44635348929764700939726227)
              ·
                refine ⟨66953023394647051409589341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44635348929764700939726227 66953023394647051409589341)
                ·
                  refine ⟨25107383772992644278596003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66953023394647051409589341 25107383772992644278596003)
                  ·
                    refine ⟨37661075659488966417894005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25107383772992644278596003 37661075659488966417894005)
                    ·
                      refine ⟨3530725843077090601677563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37661075659488966417894005 3530725843077090601677563)
                      ·
                        rfl

theorem cell23_6876064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_6876064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876064 prefixEnd_6876064 := by exact prefixLift 6876064
  have htrace : WordTrace (prefixWord ++ tailWord_6876064) baseStart_6876064 baseEnd_6876064 := by
    simpa [prefixWord, tailWord_6876064, baseEnd_6876064] using wordTrace_append hprefix tailTrace_6876064
  have hstable : (prefixWord ++ tailWord_6876064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876064).length < 2 ^ (prefixWord ++ tailWord_6876064).sum := by decide
  have hdescent : baseEnd_6876064 < baseStart_6876064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876095 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 1, 2, 2]
def baseStart_6876095 : Nat := 118140960795 + 6876095 * 2 ^ 59
def prefixEnd_6876095 : Nat := 4983230072969 + 3 ^ 40 * 6876095 * 2
def baseEnd_6876095 : Nat := 3530741760977379980389921

theorem tailTrace_6876095 : CollatzResearch.WordTrace tailWord_6876095 prefixEnd_6876095 3530741760977379980389921 := by
  unfold tailWord_6876095
  simp only [CollatzResearch.WordTrace]
  refine ⟨250791788024089633376845739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167194525349393088917897159 250791788024089633376845739)
  ·
    refine ⟨376187682036134450065268609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250791788024089633376845739 376187682036134450065268609)
    ·
      refine ⟨282140761527100837548951457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376187682036134450065268609 282140761527100837548951457)
      ·
        refine ⟨211605571145325628161713593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282140761527100837548951457 211605571145325628161713593)
        ·
          refine ⟨158704178358994221121285195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211605571145325628161713593 158704178358994221121285195)
          ·
            refine ⟨238056267538491331681927793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158704178358994221121285195 238056267538491331681927793)
            ·
              refine ⟨178542200653868498761445845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238056267538491331681927793 178542200653868498761445845)
              ·
                refine ⟨4184582827825042939721387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178542200653868498761445845 4184582827825042939721387)
                ·
                  refine ⟨6276874241737564409582081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184582827825042939721387 6276874241737564409582081)
                  ·
                    refine ⟨4707655681303173307186561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276874241737564409582081 4707655681303173307186561)
                    ·
                      refine ⟨3530741760977379980389921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707655681303173307186561 3530741760977379980389921)
                      ·
                        rfl

theorem cell23_6876095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_6876095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876095 prefixEnd_6876095 := by exact prefixLift 6876095
  have htrace : WordTrace (prefixWord ++ tailWord_6876095) baseStart_6876095 baseEnd_6876095 := by
    simpa [prefixWord, tailWord_6876095, baseEnd_6876095] using wordTrace_append hprefix tailTrace_6876095
  have hstable : (prefixWord ++ tailWord_6876095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876095).length < 2 ^ (prefixWord ++ tailWord_6876095).sum := by decide
  have hdescent : baseEnd_6876095 < baseStart_6876095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876118 : List Nat := [5, 2, 1, 1, 2, 2, 2, 8]
def baseStart_6876118 : Nat := 118140960795 + 6876118 * 2 ^ 59
def prefixEnd_6876118 : Nat := 4983230072969 + 3 ^ 40 * 6876118 * 2
def baseEnd_6876118 : Nat := 130768650778979014459345

theorem tailTrace_6876118 : CollatzResearch.WordTrace tailWord_6876118 prefixEnd_6876118 130768650778979014459345 := by
  unfold tailWord_6876118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674539181437894269058313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167195084602004205536622005 15674539181437894269058313)
  ·
    refine ⟨11755904386078420701793735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15674539181437894269058313 11755904386078420701793735)
    ·
      refine ⟨17633856579117631052690603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11755904386078420701793735 17633856579117631052690603)
      ·
        refine ⟨26450784868676446579035905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17633856579117631052690603 26450784868676446579035905)
        ·
          refine ⟨19838088651507334934276929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26450784868676446579035905 19838088651507334934276929)
          ·
            refine ⟨14878566488630501200707697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19838088651507334934276929 14878566488630501200707697)
            ·
              refine ⟨11158924866472875900530773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14878566488630501200707697 11158924866472875900530773)
              ·
                refine ⟨130768650778979014459345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11158924866472875900530773 130768650778979014459345)
                ·
                  rfl

theorem cell23_6876118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_6876118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876118 prefixEnd_6876118 := by exact prefixLift 6876118
  have htrace : WordTrace (prefixWord ++ tailWord_6876118) baseStart_6876118 baseEnd_6876118 := by
    simpa [prefixWord, tailWord_6876118, baseEnd_6876118] using wordTrace_append hprefix tailTrace_6876118
  have hstable : (prefixWord ++ tailWord_6876118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876118).length < 2 ^ (prefixWord ++ tailWord_6876118).sum := by decide
  have hdescent : baseEnd_6876118 < baseStart_6876118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876144 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_6876144 : Nat := 118140960795 + 6876144 * 2 ^ 59
def prefixEnd_6876144 : Nat := 4983230072969 + 3 ^ 40 * 6876144 * 2
def baseEnd_6876144 : Nat := 1176922307176483429559065

theorem tailTrace_6876144 : CollatzResearch.WordTrace tailWord_6876144 prefixEnd_6876144 1176922307176483429559065 := by
  unfold tailWord_6876144
  simp only [CollatzResearch.WordTrace]
  refine ⟨125396787600456057372689743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167195716800608076496919657 125396787600456057372689743)
  ·
    refine ⟨188095181400684086059034615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125396787600456057372689743 188095181400684086059034615)
    ·
      refine ⟨282142772101026129088551923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188095181400684086059034615 282142772101026129088551923)
      ·
        refine ⟨423214158151539193632827885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282142772101026129088551923 423214158151539193632827885)
        ·
          refine ⟨158705309306827197612310457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423214158151539193632827885 158705309306827197612310457)
          ·
            refine ⟨119028981980120398209232843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158705309306827197612310457 119028981980120398209232843)
            ·
              refine ⟨178543472970180597313849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119028981980120398209232843 178543472970180597313849265)
              ·
                refine ⟨133907604727635447985386949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178543472970180597313849265 133907604727635447985386949)
                ·
                  refine ⟨25107675886431646497260053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133907604727635447985386949 25107675886431646497260053)
                  ·
                    refine ⟨1176922307176483429559065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25107675886431646497260053 1176922307176483429559065)
                    ·
                      rfl

theorem cell23_6876144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_6876144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876144 prefixEnd_6876144 := by exact prefixLift 6876144
  have htrace : WordTrace (prefixWord ++ tailWord_6876144) baseStart_6876144 baseEnd_6876144 := by
    simpa [prefixWord, tailWord_6876144, baseEnd_6876144] using wordTrace_append hprefix tailTrace_6876144
  have hstable : (prefixWord ++ tailWord_6876144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876144).length < 2 ^ (prefixWord ++ tailWord_6876144).sum := by decide
  have hdescent : baseEnd_6876144 < baseStart_6876144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876149 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6876149 : Nat := 118140960795 + 6876149 * 2 ^ 59
def prefixEnd_6876149 : Nat := 4983230072969 + 3 ^ 40 * 6876149 * 2
def baseEnd_6876149 : Nat := 3530769488932722769114673

theorem tailTrace_6876149 : CollatzResearch.WordTrace tailWord_6876149 prefixEnd_6876149 3530769488932722769114673 := by
  unfold tailWord_6876149
  simp only [CollatzResearch.WordTrace]
  refine ⟨250793757565894000599311501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167195838377262667066207667 250793757565894000599311501)
  ·
    refine ⟨94047659087210250224741813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250793757565894000599311501 94047659087210250224741813)
    ·
      refine ⟨8816968039425960958569545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94047659087210250224741813 8816968039425960958569545)
      ·
        refine ⟨6612726029569470718927159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816968039425960958569545 6612726029569470718927159)
        ·
          refine ⟨9919089044354206078390739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612726029569470718927159 9919089044354206078390739)
          ·
            refine ⟨14878633566531309117586109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9919089044354206078390739 14878633566531309117586109)
            ·
              refine ⟨5579487587449240919094791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14878633566531309117586109 5579487587449240919094791)
              ·
                refine ⟨8369231381173861378642187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579487587449240919094791 8369231381173861378642187)
                ·
                  refine ⟨12553847071760792067963281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8369231381173861378642187 12553847071760792067963281)
                  ·
                    refine ⟨9415385303820594050972461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12553847071760792067963281 9415385303820594050972461)
                    ·
                      refine ⟨3530769488932722769114673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9415385303820594050972461 3530769488932722769114673)
                      ·
                        rfl

theorem cell23_6876149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6876149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876149 prefixEnd_6876149 := by exact prefixLift 6876149
  have htrace : WordTrace (prefixWord ++ tailWord_6876149) baseStart_6876149 baseEnd_6876149 := by
    simpa [prefixWord, tailWord_6876149, baseEnd_6876149] using wordTrace_append hprefix tailTrace_6876149
  have hstable : (prefixWord ++ tailWord_6876149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876149).length < 2 ^ (prefixWord ++ tailWord_6876149).sum := by decide
  have hdescent : baseEnd_6876149 < baseStart_6876149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876171 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 3]
def baseStart_6876171 : Nat := 118140960795 + 6876171 * 2 ^ 59
def prefixEnd_6876171 : Nat := 4983230072969 + 3 ^ 40 * 6876171 * 2
def baseEnd_6876171 : Nat := 3530780785507121683039571

theorem tailTrace_6876171 : CollatzResearch.WordTrace tailWord_6876171 prefixEnd_6876171 3530780785507121683039571 := by
  unfold tailWord_6876171
  simp only [CollatzResearch.WordTrace]
  refine ⟨250794559971814298356612367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167196373314542865571074911 250794559971814298356612367)
  ·
    refine ⟨376191839957721447534918551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250794559971814298356612367 376191839957721447534918551)
    ·
      refine ⟨564287759936582171302377827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376191839957721447534918551 564287759936582171302377827)
      ·
        refine ⟨846431639904873256953566741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564287759936582171302377827 846431639904873256953566741)
        ·
          refine ⟨39676483120540933919698441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 846431639904873256953566741 39676483120540933919698441)
          ·
            refine ⟨29757362340405700439773831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39676483120540933919698441 29757362340405700439773831)
            ·
              refine ⟨44636043510608550659660747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29757362340405700439773831 44636043510608550659660747)
              ·
                refine ⟨66954065265912825989491121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44636043510608550659660747 66954065265912825989491121)
                ·
                  refine ⟨50215548949434619492118341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66954065265912825989491121 50215548949434619492118341)
                  ·
                    refine ⟨9415415428018991154772189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50215548949434619492118341 9415415428018991154772189)
                    ·
                      refine ⟨3530780785507121683039571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9415415428018991154772189 3530780785507121683039571)
                      ·
                        rfl

theorem cell23_6876171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 3].length) (baseStart_6876171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876171 prefixEnd_6876171 := by exact prefixLift 6876171
  have htrace : WordTrace (prefixWord ++ tailWord_6876171) baseStart_6876171 baseEnd_6876171 := by
    simpa [prefixWord, tailWord_6876171, baseEnd_6876171] using wordTrace_append hprefix tailTrace_6876171
  have hstable : (prefixWord ++ tailWord_6876171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876171).length < 2 ^ (prefixWord ++ tailWord_6876171).sum := by decide
  have hdescent : baseEnd_6876171 < baseStart_6876171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876181 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6876181 : Nat := 118140960795 + 6876181 * 2 ^ 59
def prefixEnd_6876181 : Nat := 4983230072969 + 3 ^ 40 * 6876181 * 2
def baseEnd_6876181 : Nat := 3530785920313666643914525

theorem tailTrace_6876181 : CollatzResearch.WordTrace tailWord_6876181 prefixEnd_6876181 3530785920313666643914525 := by
  unfold tailWord_6876181
  simp only [CollatzResearch.WordTrace]
  refine ⟨250794924701778070064476397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167196616467852046709650931 250794924701778070064476397)
  ·
    refine ⟨94048096763166776274178649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250794924701778070064476397 94048096763166776274178649)
    ·
      refine ⟨70536072572375082205633987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94048096763166776274178649 70536072572375082205633987)
      ·
        refine ⟨105804108858562623308450981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70536072572375082205633987 105804108858562623308450981)
        ·
          refine ⟨19838270410980491870334559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105804108858562623308450981 19838270410980491870334559)
          ·
            refine ⟨29757405616470737805501839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19838270410980491870334559 29757405616470737805501839)
            ·
              refine ⟨44636108424706106708252759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29757405616470737805501839 44636108424706106708252759)
              ·
                refine ⟨66954162637059160062379139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44636108424706106708252759 66954162637059160062379139)
                ·
                  refine ⟨100431243955588740093568709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66954162637059160062379139 100431243955588740093568709)
                  ·
                    refine ⟨18830858241672888767544133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100431243955588740093568709 18830858241672888767544133)
                    ·
                      refine ⟨3530785920313666643914525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18830858241672888767544133 3530785920313666643914525)
                      ·
                        rfl

theorem cell23_6876181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6876181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876181 prefixEnd_6876181 := by exact prefixLift 6876181
  have htrace : WordTrace (prefixWord ++ tailWord_6876181) baseStart_6876181 baseEnd_6876181 := by
    simpa [prefixWord, tailWord_6876181, baseEnd_6876181] using wordTrace_append hprefix tailTrace_6876181
  have hstable : (prefixWord ++ tailWord_6876181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876181).length < 2 ^ (prefixWord ++ tailWord_6876181).sum := by decide
  have hdescent : baseEnd_6876181 < baseStart_6876181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876185 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 2, 2, 2]
def baseStart_6876185 : Nat := 118140960795 + 6876185 * 2 ^ 59
def prefixEnd_6876185 : Nat := 4983230072969 + 3 ^ 40 * 6876185 * 2
def baseEnd_6876185 : Nat := 3530787974236284628264507

theorem tailTrace_6876185 : CollatzResearch.WordTrace tailWord_6876185 prefixEnd_6876185 3530787974236284628264507 := by
  unfold tailWord_6876185
  simp only [CollatzResearch.WordTrace]
  refine ⟨250795070593763578747622009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167196713729175719165081339 250795070593763578747622009)
  ·
    refine ⟨188096302945322684060716507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250795070593763578747622009 188096302945322684060716507)
    ·
      refine ⟨282144454417984026091074761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188096302945322684060716507 282144454417984026091074761)
      ·
        refine ⟨211608340813488019568306071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282144454417984026091074761 211608340813488019568306071)
        ·
          refine ⟨317412511220232029352459107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211608340813488019568306071 317412511220232029352459107)
          ·
            refine ⟨476118766830348044028688661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317412511220232029352459107 476118766830348044028688661)
            ·
              refine ⟨22318067195172564563844781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 476118766830348044028688661 22318067195172564563844781)
              ·
                refine ⟨8369275198189711711441793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22318067195172564563844781 8369275198189711711441793)
                ·
                  refine ⟨6276956398642283783581345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8369275198189711711441793 6276956398642283783581345)
                  ·
                    refine ⟨4707717298981712837686009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6276956398642283783581345 4707717298981712837686009)
                    ·
                      refine ⟨3530787974236284628264507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707717298981712837686009 3530787974236284628264507)
                      ·
                        rfl

theorem cell23_6876185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_6876185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876185 prefixEnd_6876185 := by exact prefixLift 6876185
  have htrace : WordTrace (prefixWord ++ tailWord_6876185) baseStart_6876185 baseEnd_6876185 := by
    simpa [prefixWord, tailWord_6876185, baseEnd_6876185] using wordTrace_append hprefix tailTrace_6876185
  have hstable : (prefixWord ++ tailWord_6876185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876185).length < 2 ^ (prefixWord ++ tailWord_6876185).sum := by decide
  have hdescent : baseEnd_6876185 < baseStart_6876185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876191 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 7]
def baseStart_6876191 : Nat := 118140960795 + 6876191 * 2 ^ 59
def prefixEnd_6876191 : Nat := 4983230072969 + 3 ^ 40 * 6876191 * 2
def baseEnd_6876191 : Nat := 392310117235579067198831

theorem tailTrace_6876191 : CollatzResearch.WordTrace tailWord_6876191 prefixEnd_6876191 392310117235579067198831 := by
  unfold tailWord_6876191
  simp only [CollatzResearch.WordTrace]
  refine ⟨250795289431741841772340427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167196859621161227848226951 250795289431741841772340427)
  ·
    refine ⟨376192934147612762658510641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250795289431741841772340427 376192934147612762658510641)
    ·
      refine ⟨282144700610709571993882981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376192934147612762658510641 282144700610709571993882981)
      ·
        refine ⟨52902131364508044748853059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282144700610709571993882981 52902131364508044748853059)
        ·
          refine ⟨79353197046762067123279589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52902131364508044748853059 79353197046762067123279589)
          ·
            refine ⟨14878724446267887585614923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79353197046762067123279589 14878724446267887585614923)
            ·
              refine ⟨22318086669401831378422385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14878724446267887585614923 22318086669401831378422385)
              ·
                refine ⟨16738565002051373533816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22318086669401831378422385 16738565002051373533816789)
                ·
                  refine ⟨392310117235579067198831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16738565002051373533816789 392310117235579067198831)
                  ·
                    rfl

theorem cell23_6876191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 7].length) (baseStart_6876191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876191 prefixEnd_6876191 := by exact prefixLift 6876191
  have htrace : WordTrace (prefixWord ++ tailWord_6876191) baseStart_6876191 baseEnd_6876191 := by
    simpa [prefixWord, tailWord_6876191, baseEnd_6876191] using wordTrace_append hprefix tailTrace_6876191
  have hstable : (prefixWord ++ tailWord_6876191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876191).length < 2 ^ (prefixWord ++ tailWord_6876191).sum := by decide
  have hdescent : baseEnd_6876191 < baseStart_6876191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876208 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 5]
def baseStart_6876208 : Nat := 118140960795 + 6876208 * 2 ^ 59
def prefixEnd_6876208 : Nat := 4983230072969 + 3 ^ 40 * 6876208 * 2
def baseEnd_6876208 : Nat := 392311087143482004252989

theorem tailTrace_6876208 : CollatzResearch.WordTrace tailWord_6876208 prefixEnd_6876208 392311087143482004252989 := by
  unfold tailWord_6876208
  simp only [CollatzResearch.WordTrace]
  refine ⟨125397954736340126837854639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167197272981786835783806185 125397954736340126837854639)
  ·
    refine ⟨188096932104510190256781959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125397954736340126837854639 188096932104510190256781959)
    ·
      refine ⟨282145398156765285385172939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188096932104510190256781959 282145398156765285385172939)
      ·
        refine ⟨423218097235147928077759409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282145398156765285385172939 423218097235147928077759409)
        ·
          refine ⟨317413572926360946058319557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423218097235147928077759409 317413572926360946058319557)
          ·
            refine ⟨59515044923692677385934917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317413572926360946058319557 59515044923692677385934917)
            ·
              refine ⟨11159070923192377009862797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59515044923692677385934917 11159070923192377009862797)
              ·
                refine ⟨4184651596197141378698549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11159070923192377009862797 4184651596197141378698549)
                ·
                  refine ⟨392311087143482004252989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184651596197141378698549 392311087143482004252989)
                  ·
                    rfl

theorem cell23_6876208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 5].length) (baseStart_6876208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876208 prefixEnd_6876208 := by exact prefixLift 6876208
  have htrace : WordTrace (prefixWord ++ tailWord_6876208) baseStart_6876208 baseEnd_6876208 := by
    simpa [prefixWord, tailWord_6876208, baseEnd_6876208] using wordTrace_append hprefix tailTrace_6876208
  have hstable : (prefixWord ++ tailWord_6876208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876208).length < 2 ^ (prefixWord ++ tailWord_6876208).sum := by decide
  have hdescent : baseEnd_6876208 < baseStart_6876208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876241 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_6876241 : Nat := 118140960795 + 6876241 * 2 ^ 59
def prefixEnd_6876241 : Nat := 4983230072969 + 3 ^ 40 * 6876241 * 2
def baseEnd_6876241 : Nat := 3530816729152936409164249

theorem tailTrace_6876241 : CollatzResearch.WordTrace tailWord_6876241 prefixEnd_6876241 3530816729152936409164249 := by
  unfold tailWord_6876241
  simp only [CollatzResearch.WordTrace]
  refine ⟨250797113081560700311660577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167198075387707133541107051 250797113081560700311660577)
  ·
    refine ⟨188097834811170525233745433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250797113081560700311660577 188097834811170525233745433)
    ·
      refine ⟨141073376108377893925309075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188097834811170525233745433 141073376108377893925309075)
      ·
        refine ⟨211610064162566840887963613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141073376108377893925309075 211610064162566840887963613)
        ·
          refine ⟨79353774060962565332986355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211610064162566840887963613 79353774060962565332986355)
          ·
            refine ⟨119030661091443847999479533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79353774060962565332986355 119030661091443847999479533)
            ·
              refine ⟨44636497909291442999804825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119030661091443847999479533 44636497909291442999804825)
              ·
                refine ⟨33477373431968582249853619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44636497909291442999804825 33477373431968582249853619)
                ·
                  refine ⟨50216060147952873374780429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33477373431968582249853619 50216060147952873374780429)
                  ·
                    refine ⟨18831022555482327515542661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50216060147952873374780429 18831022555482327515542661)
                    ·
                      refine ⟨3530816729152936409164249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18831022555482327515542661 3530816729152936409164249)
                      ·
                        rfl

theorem cell23_6876241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_6876241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876241 prefixEnd_6876241 := by exact prefixLift 6876241
  have htrace : WordTrace (prefixWord ++ tailWord_6876241) baseStart_6876241 baseEnd_6876241 := by
    simpa [prefixWord, tailWord_6876241, baseEnd_6876241] using wordTrace_append hprefix tailTrace_6876241
  have hstable : (prefixWord ++ tailWord_6876241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876241).length < 2 ^ (prefixWord ++ tailWord_6876241).sum := by decide
  have hdescent : baseEnd_6876241 < baseStart_6876241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876298 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_6876298 : Nat := 118140960795 + 6876298 * 2 ^ 59
def prefixEnd_6876298 : Nat := 4983230072969 + 3 ^ 40 * 6876298 * 2
def baseEnd_6876298 : Nat := 392316221950026965127943

theorem tailTrace_6876298 : CollatzResearch.WordTrace tailWord_6876298 prefixEnd_6876298 392316221950026965127943 := by
  unfold tailWord_6876298
  simp only [CollatzResearch.WordTrace]
  refine ⟨62699798010588549761621387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167199461361569466030990365 62699798010588549761621387)
  ·
    refine ⟨94049697015882824642432081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62699798010588549761621387 94049697015882824642432081)
    ·
      refine ⟨70537272761912118481824061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94049697015882824642432081 70537272761912118481824061)
      ·
        refine ⟨26451477285717044430684023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70537272761912118481824061 26451477285717044430684023)
        ·
          refine ⟨39677215928575566646026035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26451477285717044430684023 39677215928575566646026035)
          ·
            refine ⟨59515823892863349969039053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39677215928575566646026035 59515823892863349969039053)
            ·
              refine ⟨22318433959823756238389645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59515823892863349969039053 22318433959823756238389645)
              ·
                refine ⟨8369412734933908589396117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22318433959823756238389645 8369412734933908589396117)
                ·
                  refine ⟨392316221950026965127943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8369412734933908589396117 392316221950026965127943)
                  ·
                    rfl

theorem cell23_6876298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_6876298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876298 prefixEnd_6876298 := by exact prefixLift 6876298
  have htrace : WordTrace (prefixWord ++ tailWord_6876298) baseStart_6876298 baseEnd_6876298 := by
    simpa [prefixWord, tailWord_6876298, baseEnd_6876298] using wordTrace_append hprefix tailTrace_6876298
  have hstable : (prefixWord ++ tailWord_6876298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876298).length < 2 ^ (prefixWord ++ tailWord_6876298).sum := by decide
  have hdescent : baseEnd_6876298 < baseStart_6876298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876335 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 2, 3, 2]
def baseStart_6876335 : Nat := 118140960795 + 6876335 * 2 ^ 59
def prefixEnd_6876335 : Nat := 4983230072969 + 3 ^ 40 * 6876335 * 2
def baseEnd_6876335 : Nat := 3530864996334459041388817

theorem tailTrace_6876335 : CollatzResearch.WordTrace tailWord_6876335 prefixEnd_6876335 3530864996334459041388817 := by
  unfold tailWord_6876335
  simp only [CollatzResearch.WordTrace]
  refine ⟨250800541543220154365582459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167200361028813436243721639 250800541543220154365582459)
  ·
    refine ⟨376200812314830231548373689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250800541543220154365582459 376200812314830231548373689)
    ·
      refine ⟨282150609236122673661280267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376200812314830231548373689 282150609236122673661280267)
      ·
        refine ⟨423225913854184010491920401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282150609236122673661280267 423225913854184010491920401)
        ·
          refine ⟨317419435390638007868940301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423225913854184010491920401 317419435390638007868940301)
          ·
            refine ⟨119032288271489252950852613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317419435390638007868940301 119032288271489252950852613)
            ·
              refine ⟨22318554050904234928284865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119032288271489252950852613 22318554050904234928284865)
              ·
                refine ⟨16738915538178176196213649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22318554050904234928284865 16738915538178176196213649)
                ·
                  refine ⟨12554186653633632147160237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16738915538178176196213649 12554186653633632147160237)
                  ·
                    refine ⟨4707819995112612055185089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12554186653633632147160237 4707819995112612055185089)
                    ·
                      refine ⟨3530864996334459041388817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707819995112612055185089 3530864996334459041388817)
                      ·
                        rfl

theorem cell23_6876335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3, 2].length) (baseStart_6876335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876335 prefixEnd_6876335 := by exact prefixLift 6876335
  have htrace : WordTrace (prefixWord ++ tailWord_6876335) baseStart_6876335 baseEnd_6876335 := by
    simpa [prefixWord, tailWord_6876335, baseEnd_6876335] using wordTrace_append hprefix tailTrace_6876335
  have hstable : (prefixWord ++ tailWord_6876335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876335).length < 2 ^ (prefixWord ++ tailWord_6876335).sum := by decide
  have hdescent : baseEnd_6876335 < baseStart_6876335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876361 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_6876361 : Nat := 118140960795 + 6876361 * 2 ^ 59
def prefixEnd_6876361 : Nat := 4983230072969 + 3 ^ 40 * 6876361 * 2
def baseEnd_6876361 : Nat := 3530878346831475939663697

theorem tailTrace_6876361 : CollatzResearch.WordTrace tailWord_6876361 prefixEnd_6876361 3530878346831475939663697 := by
  unfold tailWord_6876361
  simp only [CollatzResearch.WordTrace]
  refine ⟨250801489841125960806028937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167200993227417307204019291 250801489841125960806028937)
  ·
    refine ⟨188101117380844470604521703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250801489841125960806028937 188101117380844470604521703)
    ·
      refine ⟨282151676071266705906782555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188101117380844470604521703 282151676071266705906782555)
      ·
        refine ⟨423227514106900058860173833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282151676071266705906782555 423227514106900058860173833)
        ·
          refine ⟨317420635580175044145130375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423227514106900058860173833 317420635580175044145130375)
          ·
            refine ⟨476130953370262566217695563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317420635580175044145130375 476130953370262566217695563)
            ·
              refine ⟨714196430055393849326543345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476130953370262566217695563 714196430055393849326543345)
              ·
                refine ⟨535647322541545386994907509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714196430055393849326543345 535647322541545386994907509)
                ·
                  refine ⟨50216936488269880030772579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535647322541545386994907509 50216936488269880030772579)
                  ·
                    refine ⟨75325404732404820046158869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50216936488269880030772579 75325404732404820046158869)
                    ·
                      refine ⟨3530878346831475939663697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75325404732404820046158869 3530878346831475939663697)
                      ·
                        rfl

theorem cell23_6876361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_6876361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876361 prefixEnd_6876361 := by exact prefixLift 6876361
  have htrace : WordTrace (prefixWord ++ tailWord_6876361) baseStart_6876361 baseEnd_6876361 := by
    simpa [prefixWord, tailWord_6876361, baseEnd_6876361] using wordTrace_append hprefix tailTrace_6876361
  have hstable : (prefixWord ++ tailWord_6876361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876361).length < 2 ^ (prefixWord ++ tailWord_6876361).sum := by decide
  have hdescent : baseEnd_6876361 < baseStart_6876361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876399 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 3, 2, 2]
def baseStart_6876399 : Nat := 118140960795 + 6876399 * 2 ^ 59
def prefixEnd_6876399 : Nat := 4983230072969 + 3 ^ 40 * 6876399 * 2
def baseEnd_6876399 : Nat := 3530897859096346790988523

theorem tailTrace_6876399 : CollatzResearch.WordTrace tailWord_6876399 prefixEnd_6876399 3530897859096346790988523 := by
  unfold tailWord_6876399
  simp only [CollatzResearch.WordTrace]
  refine ⟨250802875814988293295912251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167201917209992195530608167 250802875814988293295912251)
  ·
    refine ⟨376204313722482439943868377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250802875814988293295912251 376204313722482439943868377)
    ·
      refine ⟨282153235291861829957901283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376204313722482439943868377 282153235291861829957901283)
      ·
        refine ⟨423229852937792744936851925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282153235291861829957901283 423229852937792744936851925)
        ·
          refine ⟨9919449678229517459457467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 423229852937792744936851925 9919449678229517459457467)
          ·
            refine ⟨14879174517344276189186201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9919449678229517459457467 14879174517344276189186201)
            ·
              refine ⟨11159380888008207141889651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14879174517344276189186201 11159380888008207141889651)
              ·
                refine ⟨16739071332012310712834477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11159380888008207141889651 16739071332012310712834477)
                ·
                  refine ⟨6277151749504616517312929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16739071332012310712834477 6277151749504616517312929)
                  ·
                    refine ⟨4707863812128462387984697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6277151749504616517312929 4707863812128462387984697)
                    ·
                      refine ⟨3530897859096346790988523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4707863812128462387984697 3530897859096346790988523)
                      ·
                        rfl

theorem cell23_6876399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 2, 2].length) (baseStart_6876399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876399 prefixEnd_6876399 := by exact prefixLift 6876399
  have htrace : WordTrace (prefixWord ++ tailWord_6876399) baseStart_6876399 baseEnd_6876399 := by
    simpa [prefixWord, tailWord_6876399, baseEnd_6876399] using wordTrace_append hprefix tailTrace_6876399
  have hstable : (prefixWord ++ tailWord_6876399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876399).length < 2 ^ (prefixWord ++ tailWord_6876399).sum := by decide
  have hdescent : baseEnd_6876399 < baseStart_6876399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876412 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_6876412 : Nat := 118140960795 + 6876412 * 2 ^ 59
def prefixEnd_6876412 : Nat := 4983230072969 + 3 ^ 40 * 6876412 * 2
def baseEnd_6876412 : Nat := 3530904534344855240125963

theorem tailTrace_6876412 : CollatzResearch.WordTrace tailWord_6876412 prefixEnd_6876412 3530904534344855240125963 := by
  unfold tailWord_6876412
  simp only [CollatzResearch.WordTrace]
  refine ⟨125401674981970598258067745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167202233309294131010756993 125401674981970598258067745)
  ·
    refine ⟨94051256236477948693550809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125401674981970598258067745 94051256236477948693550809)
    ·
      refine ⟨70538442177358461520163107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94051256236477948693550809 70538442177358461520163107)
      ·
        refine ⟨105807663266037692280244661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70538442177358461520163107 105807663266037692280244661)
        ·
          refine ⟨9919468431191033651272937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105807663266037692280244661 9919468431191033651272937)
          ·
            refine ⟨7439601323393275238454703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9919468431191033651272937 7439601323393275238454703)
            ·
              refine ⟨11159401985089912857682055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7439601323393275238454703 11159401985089912857682055)
              ·
                refine ⟨16739102977634869286523083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11159401985089912857682055 16739102977634869286523083)
                ·
                  refine ⟨25108654466452303929784625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16739102977634869286523083 25108654466452303929784625)
                  ·
                    refine ⟨18831490849839227947338469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25108654466452303929784625 18831490849839227947338469)
                    ·
                      refine ⟨3530904534344855240125963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18831490849839227947338469 3530904534344855240125963)
                      ·
                        rfl

theorem cell23_6876412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_6876412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876412 prefixEnd_6876412 := by exact prefixLift 6876412
  have htrace : WordTrace (prefixWord ++ tailWord_6876412) baseStart_6876412 baseEnd_6876412 := by
    simpa [prefixWord, tailWord_6876412, baseEnd_6876412] using wordTrace_append hprefix tailTrace_6876412
  have hstable : (prefixWord ++ tailWord_6876412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876412).length < 2 ^ (prefixWord ++ tailWord_6876412).sum := by decide
  have hdescent : baseEnd_6876412 < baseStart_6876412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876415 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_6876415 : Nat := 118140960795 + 6876415 * 2 ^ 59
def prefixEnd_6876415 : Nat := 4983230072969 + 3 ^ 40 * 6876415 * 2
def baseEnd_6876415 : Nat := 3530906074786818728388449

theorem tailTrace_6876415 : CollatzResearch.WordTrace tailWord_6876415 prefixEnd_6876415 3530906074786818728388449 := by
  unfold tailWord_6876415
  simp only [CollatzResearch.WordTrace]
  refine ⟨250803459382930328028494699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167202306255286885352329799 250803459382930328028494699)
  ·
    refine ⟨376205189074395492042742049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250803459382930328028494699 376205189074395492042742049)
    ·
      refine ⟨282153891805796619032056537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376205189074395492042742049 282153891805796619032056537)
      ·
        refine ⟨211615418854347464274042403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282153891805796619032056537 211615418854347464274042403)
        ·
          refine ⟨317423128281521196411063605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211615418854347464274042403 317423128281521196411063605)
          ·
            refine ⟨29758418276392612163537213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 317423128281521196411063605 29758418276392612163537213)
            ·
              refine ⟨11159406853647229561326455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29758418276392612163537213 11159406853647229561326455)
              ·
                refine ⟨16739110280470844341989683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11159406853647229561326455 16739110280470844341989683)
                ·
                  refine ⟨25108665420706266512984525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16739110280470844341989683 25108665420706266512984525)
                  ·
                    refine ⟨9415749532764849942369197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25108665420706266512984525 9415749532764849942369197)
                    ·
                      refine ⟨3530906074786818728388449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9415749532764849942369197 3530906074786818728388449)
                      ·
                        rfl

theorem cell23_6876415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_6876415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876415 prefixEnd_6876415 := by exact prefixLift 6876415
  have htrace : WordTrace (prefixWord ++ tailWord_6876415) baseStart_6876415 baseEnd_6876415 := by
    simpa [prefixWord, tailWord_6876415, baseEnd_6876415] using wordTrace_append hprefix tailTrace_6876415
  have hstable : (prefixWord ++ tailWord_6876415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876415).length < 2 ^ (prefixWord ++ tailWord_6876415).sum := by decide
  have hdescent : baseEnd_6876415 < baseStart_6876415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876428 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6876428 : Nat := 118140960795 + 6876428 * 2 ^ 59
def prefixEnd_6876428 : Nat := 4983230072969 + 3 ^ 40 * 6876428 * 2
def baseEnd_6876428 : Nat := 3530912750035327177525889

theorem tailTrace_6876428 : CollatzResearch.WordTrace tailWord_6876428 prefixEnd_6876428 3530912750035327177525889 := by
  unfold tailWord_6876428
  simp only [CollatzResearch.WordTrace]
  refine ⟨125401966765941615624358969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167202622354588820832478625 125401966765941615624358969)
  ·
    refine ⟨94051475074456211718269227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125401966765941615624358969 94051475074456211718269227)
    ·
      refine ⟨141077212611684317577403841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94051475074456211718269227 141077212611684317577403841)
      ·
        refine ⟨105807909458763238183052881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141077212611684317577403841 105807909458763238183052881)
        ·
          refine ⟨79355932094072428637289661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105807909458763238183052881 79355932094072428637289661)
          ·
            refine ⟨29758474535277160738983623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79355932094072428637289661 29758474535277160738983623)
            ·
              refine ⟨44637711802915741108475435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29758474535277160738983623 44637711802915741108475435)
              ·
                refine ⟨66956567704373611662713153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44637711802915741108475435 66956567704373611662713153)
                ·
                  refine ⟨50217425778280208747034865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66956567704373611662713153 50217425778280208747034865)
                  ·
                    refine ⟨37663069333710156560276149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50217425778280208747034865 37663069333710156560276149)
                    ·
                      refine ⟨3530912750035327177525889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37663069333710156560276149 3530912750035327177525889)
                      ·
                        rfl

theorem cell23_6876428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6876428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876428 prefixEnd_6876428 := by exact prefixLift 6876428
  have htrace : WordTrace (prefixWord ++ tailWord_6876428) baseStart_6876428 baseEnd_6876428 := by
    simpa [prefixWord, tailWord_6876428, baseEnd_6876428] using wordTrace_append hprefix tailTrace_6876428
  have hstable : (prefixWord ++ tailWord_6876428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876428).length < 2 ^ (prefixWord ++ tailWord_6876428).sum := by decide
  have hdescent : baseEnd_6876428 < baseStart_6876428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876466 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_6876466 : Nat := 118140960795 + 6876466 * 2 ^ 59
def prefixEnd_6876466 : Nat := 4983230072969 + 3 ^ 40 * 6876466 * 2
def baseEnd_6876466 : Nat := 3530932262300198028850715

theorem tailTrace_6876466 : CollatzResearch.WordTrace tailWord_6876466 prefixEnd_6876466 3530932262300198028850715 := by
  unfold tailWord_6876466
  simp only [CollatzResearch.WordTrace]
  refine ⟨62701329876436390934650313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167203546337163709159067501 62701329876436390934650313)
  ·
    refine ⟨47025997407327293200987735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62701329876436390934650313 47025997407327293200987735)
    ·
      refine ⟨70538996110990939801481603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47025997407327293200987735 70538996110990939801481603)
      ·
        refine ⟨105808494166486409702222405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70538996110990939801481603 105808494166486409702222405)
        ·
          refine ⟨19839092656216201819166701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105808494166486409702222405 19839092656216201819166701)
          ·
            refine ⟨7439659746081075682187513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19839092656216201819166701 7439659746081075682187513)
            ·
              refine ⟨5579744809560806761640635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7439659746081075682187513 5579744809560806761640635)
              ·
                refine ⟨8369617214341210142460953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579744809560806761640635 8369617214341210142460953)
                ·
                  refine ⟨6277212910755907606845715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8369617214341210142460953 6277212910755907606845715)
                  ·
                    refine ⟨9415819366133861410268573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6277212910755907606845715 9415819366133861410268573)
                    ·
                      refine ⟨3530932262300198028850715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9415819366133861410268573 3530932262300198028850715)
                      ·
                        rfl

theorem cell23_6876466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_6876466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876466 prefixEnd_6876466 := by exact prefixLift 6876466
  have htrace : WordTrace (prefixWord ++ tailWord_6876466) baseStart_6876466 baseEnd_6876466 := by
    simpa [prefixWord, tailWord_6876466, baseEnd_6876466] using wordTrace_append hprefix tailTrace_6876466
  have hstable : (prefixWord ++ tailWord_6876466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876466).length < 2 ^ (prefixWord ++ tailWord_6876466).sum := by decide
  have hdescent : baseEnd_6876466 < baseStart_6876466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876512 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 5]
def baseStart_6876512 : Nat := 118140960795 + 6876512 * 2 ^ 59
def prefixEnd_6876512 : Nat := 4983230072969 + 3 ^ 40 * 6876512 * 2
def baseEnd_6876512 : Nat := 392328431378922760986167

theorem tailTrace_6876512 : CollatzResearch.WordTrace tailWord_6876512 prefixEnd_6876512 392328431378922760986167 := by
  unfold tailWord_6876512
  simp only [CollatzResearch.WordTrace]
  refine ⟨125403498631789456797387895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167204664842385942396517193 125403498631789456797387895)
  ·
    refine ⟨188105247947684185196081843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125403498631789456797387895 188105247947684185196081843)
    ·
      refine ⟨282157871921526277794122765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188105247947684185196081843 282157871921526277794122765)
      ·
        refine ⟨105809201970572354172796037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282157871921526277794122765 105809201970572354172796037)
        ·
          refine ⟨19839225369482316407399257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105809201970572354172796037 19839225369482316407399257)
          ·
            refine ⟨14879419027111737305549443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19839225369482316407399257 14879419027111737305549443)
            ·
              refine ⟨22319128540667605958324165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14879419027111737305549443 22319128540667605958324165)
              ·
                refine ⟨4184836601375176117185781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22319128540667605958324165 4184836601375176117185781)
                ·
                  refine ⟨392328431378922760986167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184836601375176117185781 392328431378922760986167)
                  ·
                    rfl

theorem cell23_6876512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 5].length) (baseStart_6876512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876512 prefixEnd_6876512 := by exact prefixLift 6876512
  have htrace : WordTrace (prefixWord ++ tailWord_6876512) baseStart_6876512 baseEnd_6876512 := by
    simpa [prefixWord, tailWord_6876512, baseEnd_6876512] using wordTrace_append hprefix tailTrace_6876512
  have hstable : (prefixWord ++ tailWord_6876512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876512).length < 2 ^ (prefixWord ++ tailWord_6876512).sum := by decide
  have hdescent : baseEnd_6876512 < baseStart_6876512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876538 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_6876538 : Nat := 118140960795 + 6876538 * 2 ^ 59
def prefixEnd_6876538 : Nat := 4983230072969 + 3 ^ 40 * 6876538 * 2
def baseEnd_6876538 : Nat := 1176989744302440582383461

theorem tailTrace_6876538 : CollatzResearch.WordTrace tailWord_6876538 prefixEnd_6876538 1176989744302440582383461 := by
  unfold tailWord_6876538
  simp only [CollatzResearch.WordTrace]
  refine ⟨62701986390371180008805567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167205297040989813356814845 62701986390371180008805567)
  ·
    refine ⟨94052979585556770013208351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62701986390371180008805567 94052979585556770013208351)
    ·
      refine ⟨141079469378335155019812527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94052979585556770013208351 141079469378335155019812527)
      ·
        refine ⟨211619204067502732529718791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141079469378335155019812527 211619204067502732529718791)
        ·
          refine ⟨317428806101254098794578187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211619204067502732529718791 317428806101254098794578187)
          ·
            refine ⟨476143209151881148191867281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317428806101254098794578187 476143209151881148191867281)
            ·
              refine ⟨357107406863910861143900461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476143209151881148191867281 357107406863910861143900461)
              ·
                refine ⟨133915277573966572928962673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357107406863910861143900461 133915277573966572928962673)
                ·
                  refine ⟨100436458180474929696722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133915277573966572928962673 100436458180474929696722005)
                  ·
                    refine ⟨1176989744302440582383461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100436458180474929696722005 1176989744302440582383461)
                    ·
                      rfl

theorem cell23_6876538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_6876538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876538 prefixEnd_6876538 := by exact prefixLift 6876538
  have htrace : WordTrace (prefixWord ++ tailWord_6876538) baseStart_6876538 baseEnd_6876538 := by
    simpa [prefixWord, tailWord_6876538, baseEnd_6876538] using wordTrace_append hprefix tailTrace_6876538
  have hstable : (prefixWord ++ tailWord_6876538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876538).length < 2 ^ (prefixWord ++ tailWord_6876538).sum := by decide
  have hdescent : baseEnd_6876538 < baseStart_6876538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876546 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_6876546 : Nat := 118140960795 + 6876546 * 2 ^ 59
def prefixEnd_6876546 : Nat := 4983230072969 + 3 ^ 40 * 6876546 * 2
def baseEnd_6876546 : Nat := 392330371194728635094483

theorem tailTrace_6876546 : CollatzResearch.WordTrace tailWord_6876546 prefixEnd_6876546 392330371194728635094483 := by
  unfold tailWord_6876546
  simp only [CollatzResearch.WordTrace]
  refine ⟨62702059336363934350378373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167205491563637158267675661 62702059336363934350378373)
  ·
    refine ⟨11756636125568237690695945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62702059336363934350378373 11756636125568237690695945)
    ·
      refine ⟨8817477094176178268021959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11756636125568237690695945 8817477094176178268021959)
      ·
        refine ⟨13226215641264267402032939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8817477094176178268021959 13226215641264267402032939)
        ·
          refine ⟨19839323461896401103049409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13226215641264267402032939 19839323461896401103049409)
          ·
            refine ⟨14879492596422300827287057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19839323461896401103049409 14879492596422300827287057)
            ·
              refine ⟨11159619447316725620465293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14879492596422300827287057 11159619447316725620465293)
              ·
                refine ⟨4184857292743772107674485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11159619447316725620465293 4184857292743772107674485)
                ·
                  refine ⟨392330371194728635094483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184857292743772107674485 392330371194728635094483)
                  ·
                    rfl

theorem cell23_6876546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_6876546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876546 prefixEnd_6876546 := by exact prefixLift 6876546
  have htrace : WordTrace (prefixWord ++ tailWord_6876546) baseStart_6876546 baseEnd_6876546 := by
    simpa [prefixWord, tailWord_6876546, baseEnd_6876546] using wordTrace_append hprefix tailTrace_6876546
  have hstable : (prefixWord ++ tailWord_6876546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876546).length < 2 ^ (prefixWord ++ tailWord_6876546).sum := by decide
  have hdescent : baseEnd_6876546 < baseStart_6876546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876555 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 5, 4]
def baseStart_6876555 : Nat := 118140960795 + 6876555 * 2 ^ 59
def prefixEnd_6876555 : Nat := 4983230072969 + 3 ^ 40 * 6876555 * 2
def baseEnd_6876555 : Nat := 1176992654026149393545935

theorem tailTrace_6876555 : CollatzResearch.WordTrace tailWord_6876555 prefixEnd_6876555 1176992654026149393545935 := by
  unfold tailWord_6876555
  simp only [CollatzResearch.WordTrace]
  refine ⟨250808565602423131938591119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167205710401615421292394079 250808565602423131938591119)
  ·
    refine ⟨376212848403634697907886679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250808565602423131938591119 376212848403634697907886679)
    ·
      refine ⟨564319272605452046861830019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376212848403634697907886679 564319272605452046861830019)
      ·
        refine ⟨846478908908178070292745029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564319272605452046861830019 846478908908178070292745029)
        ·
          refine ⟨158714795420283388179889693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 846478908908178070292745029 158714795420283388179889693)
          ·
            refine ⟨59518048282606270567458635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158714795420283388179889693 59518048282606270567458635)
            ·
              refine ⟨89277072423909405851187953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59518048282606270567458635 89277072423909405851187953)
              ·
                refine ⟨66957804317932054388390965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89277072423909405851187953 66957804317932054388390965)
                ·
                  refine ⟨6277294154806130098911653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66957804317932054388390965 6277294154806130098911653)
                  ·
                    refine ⟨1176992654026149393545935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6277294154806130098911653 1176992654026149393545935)
                    ·
                      rfl

theorem cell23_6876555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 4].length) (baseStart_6876555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876555 prefixEnd_6876555 := by exact prefixLift 6876555
  have htrace : WordTrace (prefixWord ++ tailWord_6876555) baseStart_6876555 baseEnd_6876555 := by
    simpa [prefixWord, tailWord_6876555, baseEnd_6876555] using wordTrace_append hprefix tailTrace_6876555
  have hstable : (prefixWord ++ tailWord_6876555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876555).length < 2 ^ (prefixWord ++ tailWord_6876555).sum := by decide
  have hdescent : baseEnd_6876555 < baseStart_6876555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876589 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6876589 : Nat := 118140960795 + 6876589 * 2 ^ 59
def prefixEnd_6876589 : Nat := 4983230072969 + 3 ^ 40 * 6876589 * 2
def baseEnd_6876589 : Nat := 1176998473473567015870883

theorem tailTrace_6876589 : CollatzResearch.WordTrace tailWord_6876589 prefixEnd_6876589 1176998473473567015870883 := by
  unfold tailWord_6876589
  simp only [CollatzResearch.WordTrace]
  refine ⟨250809805684299955745328821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167206537122866637163552547 250809805684299955745328821)
  ·
    refine ⟨23513419282903120851124577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250809805684299955745328821 23513419282903120851124577)
    ·
      refine ⟨17635064462177340638343433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23513419282903120851124577 17635064462177340638343433)
      ·
        refine ⟨13226298346633005478757575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17635064462177340638343433 13226298346633005478757575)
        ·
          refine ⟨19839447519949508218136363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13226298346633005478757575 19839447519949508218136363)
          ·
            refine ⟨29759171279924262327204545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19839447519949508218136363 29759171279924262327204545)
            ·
              refine ⟨22319378459943196745403409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29759171279924262327204545 22319378459943196745403409)
              ·
                refine ⟨16739533844957397559052557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22319378459943196745403409 16739533844957397559052557)
                ·
                  refine ⟨6277325191859024084644709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16739533844957397559052557 6277325191859024084644709)
                  ·
                    refine ⟨1176998473473567015870883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6277325191859024084644709 1176998473473567015870883)
                    ·
                      rfl

theorem cell23_6876589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6876589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876589 prefixEnd_6876589 := by exact prefixLift 6876589
  have htrace : WordTrace (prefixWord ++ tailWord_6876589) baseStart_6876589 baseEnd_6876589 := by
    simpa [prefixWord, tailWord_6876589, baseEnd_6876589] using wordTrace_append hprefix tailTrace_6876589
  have hstable : (prefixWord ++ tailWord_6876589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876589).length < 2 ^ (prefixWord ++ tailWord_6876589).sum := by decide
  have hdescent : baseEnd_6876589 < baseStart_6876589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876635 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 4]
def baseStart_6876635 : Nat := 118140960795 + 6876635 * 2 ^ 59
def prefixEnd_6876635 : Nat := 4983230072969 + 3 ^ 40 * 6876635 * 2
def baseEnd_6876635 : Nat := 3531019040530807867637437

theorem tailTrace_6876635 : CollatzResearch.WordTrace tailWord_6876635 prefixEnd_6876635 3531019040530807867637437 := by
  unfold tailWord_6876635
  simp only [CollatzResearch.WordTrace]
  refine ⟨250811483442133305601503359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167207655628088870401002239 250811483442133305601503359)
  ·
    refine ⟨376217225163199958402255039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250811483442133305601503359 376217225163199958402255039)
    ·
      refine ⟨564325837744799937603382559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376217225163199958402255039 564325837744799937603382559)
      ·
        refine ⟨846488756617199906405073839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564325837744799937603382559 846488756617199906405073839)
        ·
          refine ⟨1269733134925799859607610759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846488756617199906405073839 1269733134925799859607610759)
          ·
            refine ⟨1904599702388699789411416139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269733134925799859607610759 1904599702388699789411416139)
            ·
              refine ⟨2856899553583049684117124209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904599702388699789411416139 2856899553583049684117124209)
              ·
                refine ⟨2142674665187287263087843157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856899553583049684117124209 2142674665187287263087843157)
                ·
                  refine ⟨12554734366331761307155331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2142674665187287263087843157 12554734366331761307155331)
                  ·
                    refine ⟨18832101549497641960732997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12554734366331761307155331 18832101549497641960732997)
                    ·
                      refine ⟨3531019040530807867637437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18832101549497641960732997 3531019040530807867637437)
                      ·
                        rfl

theorem cell23_6876635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 4].length) (baseStart_6876635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876635 prefixEnd_6876635 := by exact prefixLift 6876635
  have htrace : WordTrace (prefixWord ++ tailWord_6876635) baseStart_6876635 baseEnd_6876635 := by
    simpa [prefixWord, tailWord_6876635, baseEnd_6876635] using wordTrace_append hprefix tailTrace_6876635
  have hstable : (prefixWord ++ tailWord_6876635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876635).length < 2 ^ (prefixWord ++ tailWord_6876635).sum := by decide
  have hdescent : baseEnd_6876635 < baseStart_6876635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876652 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_6876652 : Nat := 118140960795 + 6876652 * 2 ^ 59
def prefixEnd_6876652 : Nat := 4983230072969 + 3 ^ 40 * 6876652 * 2
def baseEnd_6876652 : Nat := 3531027769701934301124859

theorem tailTrace_6876652 : CollatzResearch.WordTrace tailWord_6876652 prefixEnd_6876652 3531027769701934301124859 := by
  unfold tailWord_6876652
  simp only [CollatzResearch.WordTrace]
  refine ⟨125406051741535858752436105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167208068988714478336581473 125406051741535858752436105)
  ·
    refine ⟨94054538806151894064327079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125406051741535858752436105 94054538806151894064327079)
    ·
      refine ⟨141081808209227841096490619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94054538806151894064327079 141081808209227841096490619)
      ·
        refine ⟨211622712313841761644735929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141081808209227841096490619 211622712313841761644735929)
        ·
          refine ⟨158717034235381321233551947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211622712313841761644735929 158717034235381321233551947)
          ·
            refine ⟨238075551353071981850327921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158717034235381321233551947 238075551353071981850327921)
            ·
              refine ⟨178556663514803986387745941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238075551353071981850327921 178556663514803986387745941)
              ·
                refine ⟨8369843602256436861925591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178556663514803986387745941 8369843602256436861925591)
                ·
                  refine ⟨12554765403384655292888387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8369843602256436861925591 12554765403384655292888387)
                  ·
                    refine ⟨18832148105076982939332581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12554765403384655292888387 18832148105076982939332581)
                    ·
                      refine ⟨3531027769701934301124859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18832148105076982939332581 3531027769701934301124859)
                      ·
                        rfl

theorem cell23_6876652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_6876652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876652 prefixEnd_6876652 := by exact prefixLift 6876652
  have htrace : WordTrace (prefixWord ++ tailWord_6876652) baseStart_6876652 baseEnd_6876652 := by
    simpa [prefixWord, tailWord_6876652, baseEnd_6876652] using wordTrace_append hprefix tailTrace_6876652
  have hstable : (prefixWord ++ tailWord_6876652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876652).length < 2 ^ (prefixWord ++ tailWord_6876652).sum := by decide
  have hdescent : baseEnd_6876652 < baseStart_6876652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876655 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_6876655 : Nat := 118140960795 + 6876655 * 2 ^ 59
def prefixEnd_6876655 : Nat := 4983230072969 + 3 ^ 40 * 6876655 * 2
def baseEnd_6876655 : Nat := 3531029310143897789387345

theorem tailTrace_6876655 : CollatzResearch.WordTrace tailWord_6876655 prefixEnd_6876655 3531029310143897789387345 := by
  unfold tailWord_6876655
  simp only [CollatzResearch.WordTrace]
  refine ⟨250812212902060849017231419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167208141934707232678154279 250812212902060849017231419)
  ·
    refine ⟨376218319353091273525847129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250812212902060849017231419 376218319353091273525847129)
    ·
      refine ⟨282163739514818455144385347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376218319353091273525847129 282163739514818455144385347)
      ·
        refine ⟨423245609272227682716578021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282163739514818455144385347 423245609272227682716578021)
        ·
          refine ⟨79358551738542690509358379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423245609272227682716578021 79358551738542690509358379)
          ·
            refine ⟨119037827607814035764037569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79358551738542690509358379 119037827607814035764037569)
            ·
              refine ⟨89278370705860526823028177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119037827607814035764037569 89278370705860526823028177)
              ·
                refine ⟨66958778029395395117271133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89278370705860526823028177 66958778029395395117271133)
                ·
                  refine ⟨25109541761023273168976675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66958778029395395117271133 25109541761023273168976675)
                  ·
                    refine ⟨37664312641534909753465013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25109541761023273168976675 37664312641534909753465013)
                    ·
                      refine ⟨3531029310143897789387345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37664312641534909753465013 3531029310143897789387345)
                      ·
                        rfl

theorem cell23_6876655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_6876655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876655 prefixEnd_6876655 := by exact prefixLift 6876655
  have htrace : WordTrace (prefixWord ++ tailWord_6876655) baseStart_6876655 baseEnd_6876655 := by
    simpa [prefixWord, tailWord_6876655, baseEnd_6876655] using wordTrace_append hprefix tailTrace_6876655
  have hstable : (prefixWord ++ tailWord_6876655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876655).length < 2 ^ (prefixWord ++ tailWord_6876655).sum := by decide
  have hdescent : baseEnd_6876655 < baseStart_6876655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876662 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_6876662 : Nat := 118140960795 + 6876662 * 2 ^ 59
def prefixEnd_6876662 : Nat := 4983230072969 + 3 ^ 40 * 6876662 * 2
def baseEnd_6876662 : Nat := 1177010968169493087333271

theorem tailTrace_6876662 : CollatzResearch.WordTrace tailWord_6876662 prefixEnd_6876662 1177010968169493087333271 := by
  unfold tailWord_6876662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15675779263314718075796015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167208312142023659475157493 15675779263314718075796015)
  ·
    refine ⟨23513668894972077113694023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15675779263314718075796015 23513668894972077113694023)
    ·
      refine ⟨35270503342458115670541035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23513668894972077113694023 35270503342458115670541035)
      ·
        refine ⟨52905755013687173505811553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35270503342458115670541035 52905755013687173505811553)
        ·
          refine ⟨39679316260265380129358665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52905755013687173505811553 39679316260265380129358665)
          ·
            refine ⟨29759487195199035097018999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39679316260265380129358665 29759487195199035097018999)
            ·
              refine ⟨44639230792798552645528499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29759487195199035097018999 44639230792798552645528499)
              ·
                refine ⟨66958846189197828968292749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44639230792798552645528499 66958846189197828968292749)
                ·
                  refine ⟨25109567320949185863109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66958846189197828968292749 25109567320949185863109781)
                  ·
                    refine ⟨1177010968169493087333271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25109567320949185863109781 1177010968169493087333271)
                    ·
                      rfl

theorem cell23_6876662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_6876662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876662 prefixEnd_6876662 := by exact prefixLift 6876662
  have htrace : WordTrace (prefixWord ++ tailWord_6876662) baseStart_6876662 baseEnd_6876662 := by
    simpa [prefixWord, tailWord_6876662, baseEnd_6876662] using wordTrace_append hprefix tailTrace_6876662
  have hstable : (prefixWord ++ tailWord_6876662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876662).length < 2 ^ (prefixWord ++ tailWord_6876662).sum := by decide
  have hdescent : baseEnd_6876662 < baseStart_6876662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876679 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 2, 4]
def baseStart_6876679 : Nat := 118140960795 + 6876679 * 2 ^ 59
def prefixEnd_6876679 : Nat := 4983230072969 + 3 ^ 40 * 6876679 * 2
def baseEnd_6876679 : Nat := 1177013877893201898495745

theorem tailTrace_6876679 : CollatzResearch.WordTrace tailWord_6876679 prefixEnd_6876679 1177013877893201898495745 := by
  unfold tailWord_6876679
  simp only [CollatzResearch.WordTrace]
  refine ⟨250813088253973901116105091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167208725502649267410736727 250813088253973901116105091)
  ·
    refine ⟨376219632380960851674157637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250813088253973901116105091 376219632380960851674157637)
    ·
      refine ⟨70541181071430159688904557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376219632380960851674157637 70541181071430159688904557)
      ·
        refine ⟨26452942901786309883339209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70541181071430159688904557 26452942901786309883339209)
        ·
          refine ⟨19839707176339732412504407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26452942901786309883339209 19839707176339732412504407)
          ·
            refine ⟨29759560764509598618756611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19839707176339732412504407 29759560764509598618756611)
            ·
              refine ⟨44639341146764397928134917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29759560764509598618756611 44639341146764397928134917)
              ·
                refine ⟨8369876465018324611525297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44639341146764397928134917 8369876465018324611525297)
                ·
                  refine ⟨6277407348763743458643973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8369876465018324611525297 6277407348763743458643973)
                  ·
                    refine ⟨1177013877893201898495745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6277407348763743458643973 1177013877893201898495745)
                    ·
                      rfl

theorem cell23_6876679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_6876679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876679 prefixEnd_6876679 := by exact prefixLift 6876679
  have htrace : WordTrace (prefixWord ++ tailWord_6876679) baseStart_6876679 baseEnd_6876679 := by
    simpa [prefixWord, tailWord_6876679, baseEnd_6876679] using wordTrace_append hprefix tailTrace_6876679
  have hstable : (prefixWord ++ tailWord_6876679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876679).length < 2 ^ (prefixWord ++ tailWord_6876679).sum := by decide
  have hdescent : baseEnd_6876679 < baseStart_6876679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876755 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_6876755 : Nat := 118140960795 + 6876755 * 2 ^ 59
def prefixEnd_6876755 : Nat := 4983230072969 + 3 ^ 40 * 6876755 * 2
def baseEnd_6876755 : Nat := 3531080658209347398136885

theorem tailTrace_6876755 : CollatzResearch.WordTrace tailWord_6876755 prefixEnd_6876755 3531080658209347398136885 := by
  unfold tailWord_6876755
  simp only [CollatzResearch.WordTrace]
  refine ⟨250815860201698566095871719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167210573467799044063914479 250815860201698566095871719)
  ·
    refine ⟨376223790302547849143807579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250815860201698566095871719 376223790302547849143807579)
    ·
      refine ⟨564335685453821773715711369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376223790302547849143807579 564335685453821773715711369)
      ·
        refine ⟨423251764090366330286783527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564335685453821773715711369 423251764090366330286783527)
        ·
          refine ⟨634877646135549495430175291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423251764090366330286783527 634877646135549495430175291)
          ·
            refine ⟨952316469203324243145262937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634877646135549495430175291 952316469203324243145262937)
            ·
              refine ⟨714237351902493182358947203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952316469203324243145262937 714237351902493182358947203)
              ·
                refine ⟨1071356027853739773538420805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714237351902493182358947203 1071356027853739773538420805)
                ·
                  refine ⟨200879255222576207538453901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071356027853739773538420805 200879255222576207538453901)
                  ·
                    refine ⟨75329720708466077826920213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200879255222576207538453901 75329720708466077826920213)
                    ·
                      refine ⟨3531080658209347398136885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75329720708466077826920213 3531080658209347398136885)
                      ·
                        rfl

theorem cell23_6876755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_6876755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876755 prefixEnd_6876755 := by exact prefixLift 6876755
  have htrace : WordTrace (prefixWord ++ tailWord_6876755) baseStart_6876755 baseEnd_6876755 := by
    simpa [prefixWord, tailWord_6876755, baseEnd_6876755] using wordTrace_append hprefix tailTrace_6876755
  have hstable : (prefixWord ++ tailWord_6876755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876755).length < 2 ^ (prefixWord ++ tailWord_6876755).sum := by decide
  have hdescent : baseEnd_6876755 < baseStart_6876755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876762 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_6876762 : Nat := 118140960795 + 6876762 * 2 ^ 59
def prefixEnd_6876762 : Nat := 4983230072969 + 3 ^ 40 * 6876762 * 2
def baseEnd_6876762 : Nat := 3531084252573928870749353

theorem tailTrace_6876762 : CollatzResearch.WordTrace tailWord_6876762 prefixEnd_6876762 3531084252573928870749353 := by
  unfold tailWord_6876762
  simp only [CollatzResearch.WordTrace]
  refine ⟨62704028878168301572844135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167210743675115470860917693 62704028878168301572844135)
  ·
    refine ⟨94056043317252452359266203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62704028878168301572844135 94056043317252452359266203)
    ·
      refine ⟨141084064975878678538899305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94056043317252452359266203 141084064975878678538899305)
      ·
        refine ⟨105813048731909008904174479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141084064975878678538899305 105813048731909008904174479)
        ·
          refine ⟨158719573097863513356261719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105813048731909008904174479 158719573097863513356261719)
          ·
            refine ⟨238079359646795270034392579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158719573097863513356261719 238079359646795270034392579)
            ·
              refine ⟨357119039470192905051588869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238079359646795270034392579 357119039470192905051588869)
              ·
                refine ⟨66959819900661169697172913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357119039470192905051588869 66959819900661169697172913)
                ·
                  refine ⟨50219864925495877272879685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66959819900661169697172913 50219864925495877272879685)
                  ·
                    refine ⟨9416224673530476988664941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50219864925495877272879685 9416224673530476988664941)
                    ·
                      refine ⟨3531084252573928870749353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9416224673530476988664941 3531084252573928870749353)
                      ·
                        rfl

theorem cell23_6876762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_6876762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876762 prefixEnd_6876762 := by exact prefixLift 6876762
  have htrace : WordTrace (prefixWord ++ tailWord_6876762) baseStart_6876762 baseEnd_6876762 := by
    simpa [prefixWord, tailWord_6876762, baseEnd_6876762] using wordTrace_append hprefix tailTrace_6876762
  have hstable : (prefixWord ++ tailWord_6876762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876762).length < 2 ^ (prefixWord ++ tailWord_6876762).sum := by decide
  have hdescent : baseEnd_6876762 < baseStart_6876762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876810 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_6876810 : Nat := 118140960795 + 6876810 * 2 ^ 59
def prefixEnd_6876810 : Nat := 4983230072969 + 3 ^ 40 * 6876810 * 2
def baseEnd_6876810 : Nat := 3531108899645344682949133

theorem tailTrace_6876810 : CollatzResearch.WordTrace tailWord_6876810 prefixEnd_6876810 3531108899645344682949133 := by
  unfold tailWord_6876810
  simp only [CollatzResearch.WordTrace]
  refine ⟨62704466554124827622280971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167211910810999540326082589 62704466554124827622280971)
  ·
    refine ⟨94056699831187241433421457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62704466554124827622280971 94056699831187241433421457)
    ·
      refine ⟨70542524873390431075066093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94056699831187241433421457 70542524873390431075066093)
      ·
        refine ⟨26453446827521411653149785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70542524873390431075066093 26453446827521411653149785)
        ·
          refine ⟨19840085120641058739862339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26453446827521411653149785 19840085120641058739862339)
          ·
            refine ⟨29760127680961588109793509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19840085120641058739862339 29760127680961588109793509)
            ·
              refine ⟨5580023940180297770586283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29760127680961588109793509 5580023940180297770586283)
              ·
                refine ⟨8370035910270446655879425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580023940180297770586283 8370035910270446655879425)
                ·
                  refine ⟨6277526932702834991909569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8370035910270446655879425 6277526932702834991909569)
                  ·
                    refine ⟨4708145199527126243932177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6277526932702834991909569 4708145199527126243932177)
                    ·
                      refine ⟨3531108899645344682949133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708145199527126243932177 3531108899645344682949133)
                      ·
                        rfl

theorem cell23_6876810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_6876810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876810 prefixEnd_6876810 := by exact prefixLift 6876810
  have htrace : WordTrace (prefixWord ++ tailWord_6876810) baseStart_6876810 baseEnd_6876810 := by
    simpa [prefixWord, tailWord_6876810, baseEnd_6876810] using wordTrace_append hprefix tailTrace_6876810
  have hstable : (prefixWord ++ tailWord_6876810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876810).length < 2 ^ (prefixWord ++ tailWord_6876810).sum := by decide
  have hdescent : baseEnd_6876810 < baseStart_6876810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876812 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_6876812 : Nat := 118140960795 + 6876812 * 2 ^ 59
def prefixEnd_6876812 : Nat := 4983230072969 + 3 ^ 40 * 6876812 * 2
def baseEnd_6876812 : Nat := 1177036642202217891708041

theorem tailTrace_6876812 : CollatzResearch.WordTrace tailWord_6876812 prefixEnd_6876812 1177036642202217891708041 := by
  unfold tailWord_6876812
  simp only [CollatzResearch.WordTrace]
  refine ⟨125408969581246032415348345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167211959441661376553797793 125408969581246032415348345)
  ·
    refine ⟨94056727185934524311511259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125408969581246032415348345 94056727185934524311511259)
    ·
      refine ⟨141085090778901786467266889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94056727185934524311511259 141085090778901786467266889)
      ·
        refine ⟨105813818084176339850450167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141085090778901786467266889 105813818084176339850450167)
        ·
          refine ⟨158720727126264509775675251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105813818084176339850450167 158720727126264509775675251)
          ·
            refine ⟨238081090689396764663512877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158720727126264509775675251 238081090689396764663512877)
            ·
              refine ⟨89280409008523786748817329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238081090689396764663512877 89280409008523786748817329)
              ·
                refine ⟨66960306756392840061612997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89280409008523786748817329 66960306756392840061612997)
                ·
                  refine ⟨12555057516823657511552437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66960306756392840061612997 12555057516823657511552437)
                  ·
                    refine ⟨1177036642202217891708041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12555057516823657511552437 1177036642202217891708041)
                    ·
                      rfl

theorem cell23_6876812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_6876812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876812 prefixEnd_6876812 := by exact prefixLift 6876812
  have htrace : WordTrace (prefixWord ++ tailWord_6876812) baseStart_6876812 baseEnd_6876812 := by
    simpa [prefixWord, tailWord_6876812, baseEnd_6876812] using wordTrace_append hprefix tailTrace_6876812
  have hstable : (prefixWord ++ tailWord_6876812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876812).length < 2 ^ (prefixWord ++ tailWord_6876812).sum := by decide
  have hdescent : baseEnd_6876812 < baseStart_6876812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876909 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6876909 : Nat := 118140960795 + 6876909 * 2 ^ 59
def prefixEnd_6876909 : Nat := 4983230072969 + 3 ^ 40 * 6876909 * 2
def baseEnd_6876909 : Nat := 3531159734230139795611177

theorem tailTrace_6876909 : CollatzResearch.WordTrace tailWord_6876909 prefixEnd_6876909 3531159734230139795611177 := by
  unfold tailWord_6876909
  simp only [CollatzResearch.WordTrace]
  refine ⟨250821477043140650396977781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167214318028760433597985187 250821477043140650396977781)
  ·
    refine ⟨23514513472794435974716667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250821477043140650396977781 23514513472794435974716667)
    ·
      refine ⟨35271770209191653962075001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23514513472794435974716667 35271770209191653962075001)
      ·
        refine ⟨26453827656893740471556251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35271770209191653962075001 26453827656893740471556251)
        ·
          refine ⟨39680741485340610707334377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26453827656893740471556251 39680741485340610707334377)
          ·
            refine ⟨29760556114005458030500783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39680741485340610707334377 29760556114005458030500783)
            ·
              refine ⟨44640834171008187045751175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29760556114005458030500783 44640834171008187045751175)
              ·
                refine ⟨66961251256512280568626763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44640834171008187045751175 66961251256512280568626763)
                ·
                  refine ⟨100441876884768420852940145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66961251256512280568626763 100441876884768420852940145)
                  ·
                    refine ⟨75331407663576315639705109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100441876884768420852940145 75331407663576315639705109)
                    ·
                      refine ⟨3531159734230139795611177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75331407663576315639705109 3531159734230139795611177)
                      ·
                        rfl

theorem cell23_6876909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6876909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876909 prefixEnd_6876909 := by exact prefixLift 6876909
  have htrace : WordTrace (prefixWord ++ tailWord_6876909) baseStart_6876909 baseEnd_6876909 := by
    simpa [prefixWord, tailWord_6876909, baseEnd_6876909] using wordTrace_append hprefix tailTrace_6876909
  have hstable : (prefixWord ++ tailWord_6876909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876909).length < 2 ^ (prefixWord ++ tailWord_6876909).sum := by decide
  have hdescent : baseEnd_6876909 < baseStart_6876909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876912 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_6876912 : Nat := 118140960795 + 6876912 * 2 ^ 59
def prefixEnd_6876912 : Nat := 4983230072969 + 3 ^ 40 * 6876912 * 2
def baseEnd_6876912 : Nat := 3531161274672103283873663

theorem tailTrace_6876912 : CollatzResearch.WordTrace tailWord_6876912 prefixEnd_6876912 3531161274672103283873663 := by
  unfold tailWord_6876912
  simp only [CollatzResearch.WordTrace]
  refine ⟨125410793231064890954668495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167214390974753187939557993 125410793231064890954668495)
  ·
    refine ⟨188116189846597336432002743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125410793231064890954668495 188116189846597336432002743)
    ·
      refine ⟨282174284769896004648004115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188116189846597336432002743 282174284769896004648004115)
      ·
        refine ⟨423261427154844006972006173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282174284769896004648004115 423261427154844006972006173)
        ·
          refine ⟨158723035183066502614502315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423261427154844006972006173 158723035183066502614502315)
          ·
            refine ⟨238084552774599753921753473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158723035183066502614502315 238084552774599753921753473)
            ·
              refine ⟨178563414580949815441315105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238084552774599753921753473 178563414580949815441315105)
              ·
                refine ⟨133922560935712361580986329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178563414580949815441315105 133922560935712361580986329)
                ·
                  refine ⟨100441920701784271185739747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133922560935712361580986329 100441920701784271185739747)
                  ·
                    refine ⟨150662881052676406778609621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100441920701784271185739747 150662881052676406778609621)
                    ·
                      refine ⟨3531161274672103283873663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150662881052676406778609621 3531161274672103283873663)
                      ·
                        rfl

theorem cell23_6876912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_6876912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876912 prefixEnd_6876912 := by exact prefixLift 6876912
  have htrace : WordTrace (prefixWord ++ tailWord_6876912) baseStart_6876912 baseEnd_6876912 := by
    simpa [prefixWord, tailWord_6876912, baseEnd_6876912] using wordTrace_append hprefix tailTrace_6876912
  have hstable : (prefixWord ++ tailWord_6876912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876912).length < 2 ^ (prefixWord ++ tailWord_6876912).sum := by decide
  have hdescent : baseEnd_6876912 < baseStart_6876912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876936 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 1, 5]
def baseStart_6876936 : Nat := 118140960795 + 6876936 * 2 ^ 59
def prefixEnd_6876936 : Nat := 4983230072969 + 3 ^ 40 * 6876936 * 2
def baseEnd_6876936 : Nat := 1177057866069270396657851

theorem tailTrace_6876936 : CollatzResearch.WordTrace tailWord_6876936 prefixEnd_6876936 1177057866069270396657851 := by
  unfold tailWord_6876936
  simp only [CollatzResearch.WordTrace]
  refine ⟨125411230907021417004105331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167214974542695222672140441 125411230907021417004105331)
  ·
    refine ⟨188116846360532125506157997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125411230907021417004105331 188116846360532125506157997)
    ·
      refine ⟨70543817385199547064809249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188116846360532125506157997 70543817385199547064809249)
      ·
        refine ⟨52907863038899660298606937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70543817385199547064809249 52907863038899660298606937)
        ·
          refine ⟨39680897279174745223955203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52907863038899660298606937 39680897279174745223955203)
          ·
            refine ⟨59521345918762117835932805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39680897279174745223955203 59521345918762117835932805)
            ·
              refine ⟨11160252359767897094237401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59521345918762117835932805 11160252359767897094237401)
              ·
                refine ⟨8370189269825922820678051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11160252359767897094237401 8370189269825922820678051)
                ·
                  refine ⟨12555283904738884231017077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370189269825922820678051 12555283904738884231017077)
                  ·
                    refine ⟨1177057866069270396657851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12555283904738884231017077 1177057866069270396657851)
                    ·
                      rfl

theorem cell23_6876936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_6876936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876936 prefixEnd_6876936 := by exact prefixLift 6876936
  have htrace : WordTrace (prefixWord ++ tailWord_6876936) baseStart_6876936 baseEnd_6876936 := by
    simpa [prefixWord, tailWord_6876936, baseEnd_6876936] using wordTrace_append hprefix tailTrace_6876936
  have hstable : (prefixWord ++ tailWord_6876936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876936).length < 2 ^ (prefixWord ++ tailWord_6876936).sum := by decide
  have hdescent : baseEnd_6876936 < baseStart_6876936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876939 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 4]
def baseStart_6876939 : Nat := 118140960795 + 6876939 * 2 ^ 59
def prefixEnd_6876939 : Nat := 4983230072969 + 3 ^ 40 * 6876939 * 2
def baseEnd_6876939 : Nat := 3531175138649774678236039

theorem tailTrace_6876939 : CollatzResearch.WordTrace tailWord_6876939 prefixEnd_6876939 3531175138649774678236039 := by
  unfold tailWord_6876939
  simp only [CollatzResearch.WordTrace]
  refine ⟨250822571233031965520569871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167215047488687977013713247 250822571233031965520569871)
  ·
    refine ⟨376233856849547948280854807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250822571233031965520569871 376233856849547948280854807)
    ·
      refine ⟨564350785274321922421282211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376233856849547948280854807 564350785274321922421282211)
      ·
        refine ⟨846526177911482883631923317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564350785274321922421282211 846526177911482883631923317)
        ·
          refine ⟨79361829179201520340492811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 846526177911482883631923317 79361829179201520340492811)
          ·
            refine ⟨119042743768802280510739217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79361829179201520340492811 119042743768802280510739217)
            ·
              refine ⟨89282057826601710383054413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119042743768802280510739217 89282057826601710383054413)
              ·
                refine ⟨33480771684975641393645405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89282057826601710383054413 33480771684975641393645405)
                ·
                  refine ⟨12555289381865865522617027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33480771684975641393645405 12555289381865865522617027)
                  ·
                    refine ⟨18832934072798798283925541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555289381865865522617027 18832934072798798283925541)
                    ·
                      refine ⟨3531175138649774678236039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18832934072798798283925541 3531175138649774678236039)
                      ·
                        rfl

theorem cell23_6876939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 4].length) (baseStart_6876939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876939 prefixEnd_6876939 := by exact prefixLift 6876939
  have htrace : WordTrace (prefixWord ++ tailWord_6876939) baseStart_6876939 baseEnd_6876939 := by
    simpa [prefixWord, tailWord_6876939, baseEnd_6876939] using wordTrace_append hprefix tailTrace_6876939
  have hstable : (prefixWord ++ tailWord_6876939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876939).length < 2 ^ (prefixWord ++ tailWord_6876939).sum := by decide
  have hdescent : baseEnd_6876939 < baseStart_6876939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876956 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6876956 : Nat := 118140960795 + 6876956 * 2 ^ 59
def prefixEnd_6876956 : Nat := 4983230072969 + 3 ^ 40 * 6876956 * 2
def baseEnd_6876956 : Nat := 3531183867820901111723461

theorem tailTrace_6876956 : CollatzResearch.WordTrace tailWord_6876956 prefixEnd_6876956 3531183867820901111723461 := by
  unfold tailWord_6876956
  simp only [CollatzResearch.WordTrace]
  refine ⟨125411595636985188711969361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167215460849313584949292481 125411595636985188711969361)
  ·
    refine ⟨94058696727738891533977021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125411595636985188711969361 94058696727738891533977021)
    ·
      refine ⟨35272011272902084325241383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94058696727738891533977021 35272011272902084325241383)
      ·
        refine ⟨52908016909353126487862075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35272011272902084325241383 52908016909353126487862075)
        ·
          refine ⟨79362025364029689731793113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52908016909353126487862075 79362025364029689731793113)
          ·
            refine ⟨59521519023022267298844835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79362025364029689731793113 59521519023022267298844835)
            ·
              refine ⟨89282278534533400948267253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59521519023022267298844835 89282278534533400948267253)
              ·
                refine ⟨8370213612612506338900055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89282278534533400948267253 8370213612612506338900055)
                ·
                  refine ⟨12555320418918759508350083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370213612612506338900055 12555320418918759508350083)
                  ·
                    refine ⟨18832980628378139262525125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555320418918759508350083 18832980628378139262525125)
                    ·
                      refine ⟨3531183867820901111723461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18832980628378139262525125 3531183867820901111723461)
                      ·
                        rfl

theorem cell23_6876956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6876956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876956 prefixEnd_6876956 := by exact prefixLift 6876956
  have htrace : WordTrace (prefixWord ++ tailWord_6876956) baseStart_6876956 baseEnd_6876956 := by
    simpa [prefixWord, tailWord_6876956, baseEnd_6876956] using wordTrace_append hprefix tailTrace_6876956
  have hstable : (prefixWord ++ tailWord_6876956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876956).length < 2 ^ (prefixWord ++ tailWord_6876956).sum := by decide
  have hdescent : baseEnd_6876956 < baseStart_6876956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6876990 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_6876990 : Nat := 118140960795 + 6876990 * 2 ^ 59
def prefixEnd_6876990 : Nat := 4983230072969 + 3 ^ 40 * 6876990 * 2
def baseEnd_6876990 : Nat := 3531201326163153978698305

theorem tailTrace_6876990 : CollatzResearch.WordTrace tailWord_6876990 prefixEnd_6876990 3531201326163153978698305 := by
  unfold tailWord_6876990
  simp only [CollatzResearch.WordTrace]
  refine ⟨31353053919480900153834553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167216287570564800820450949 31353053919480900153834553)
  ·
    refine ⟨23514790439610675115375915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31353053919480900153834553 23514790439610675115375915)
    ·
      refine ⟨35272185659416012673063873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23514790439610675115375915 35272185659416012673063873)
      ·
        refine ⟨26454139244562009504797905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35272185659416012673063873 26454139244562009504797905)
        ·
          refine ⟨19840604433421507128598429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26454139244562009504797905 19840604433421507128598429)
          ·
            refine ⟨7440226662533065173224411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19840604433421507128598429 7440226662533065173224411)
            ·
              refine ⟨11160339993799597759836617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440226662533065173224411 11160339993799597759836617)
              ·
                refine ⟨8370254995349698319877463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11160339993799597759836617 8370254995349698319877463)
                ·
                  refine ⟨12555382493024547479816195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370254995349698319877463 12555382493024547479816195)
                  ·
                    refine ⟨18833073739536821219724293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555382493024547479816195 18833073739536821219724293)
                    ·
                      refine ⟨3531201326163153978698305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18833073739536821219724293 3531201326163153978698305)
                      ·
                        rfl

theorem cell23_6876990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_6876990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6876990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6876990 prefixEnd_6876990 := by exact prefixLift 6876990
  have htrace : WordTrace (prefixWord ++ tailWord_6876990) baseStart_6876990 baseEnd_6876990 := by
    simpa [prefixWord, tailWord_6876990, baseEnd_6876990] using wordTrace_append hprefix tailTrace_6876990
  have hstable : (prefixWord ++ tailWord_6876990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6876990).length < 2 ^ (prefixWord ++ tailWord_6876990).sum := by decide
  have hdescent : baseEnd_6876990 < baseStart_6876990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6876990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877010 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_6877010 : Nat := 118140960795 + 6877010 * 2 ^ 59
def prefixEnd_6877010 : Nat := 4983230072969 + 3 ^ 40 * 6877010 * 2
def baseEnd_6877010 : Nat := 3531211595776243900448213

theorem tailTrace_6877010 : CollatzResearch.WordTrace tailWord_6877010 prefixEnd_6877010 3531211595776243900448213 := by
  unfold tailWord_6877010
  simp only [CollatzResearch.WordTrace]
  refine ⟨62706290203943686161601121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167216773877183163097602989 62706290203943686161601121)
  ·
    refine ⟨47029717652957764621200841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62706290203943686161601121 47029717652957764621200841)
    ·
      refine ⟨35272288239718323465900631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47029717652957764621200841 35272288239718323465900631)
      ·
        refine ⟨52908432359577485198850947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35272288239718323465900631 52908432359577485198850947)
        ·
          refine ⟨79362648539366227798276421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52908432359577485198850947 79362648539366227798276421)
          ·
            refine ⟨14880496601131167712176829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79362648539366227798276421 14880496601131167712176829)
            ·
              refine ⟨5580186225424187892066311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14880496601131167712176829 5580186225424187892066311)
              ·
                refine ⟨8370279338136281838099467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580186225424187892066311 8370279338136281838099467)
                ·
                  refine ⟨12555419007204422757149201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370279338136281838099467 12555419007204422757149201)
                  ·
                    refine ⟨9416564255403317067861901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12555419007204422757149201 9416564255403317067861901)
                    ·
                      refine ⟨3531211595776243900448213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9416564255403317067861901 3531211595776243900448213)
                      ·
                        rfl

theorem cell23_6877010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_6877010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877010 prefixEnd_6877010 := by exact prefixLift 6877010
  have htrace : WordTrace (prefixWord ++ tailWord_6877010) baseStart_6877010 baseEnd_6877010 := by
    simpa [prefixWord, tailWord_6877010, baseEnd_6877010] using wordTrace_append hprefix tailTrace_6877010
  have hstable : (prefixWord ++ tailWord_6877010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877010).length < 2 ^ (prefixWord ++ tailWord_6877010).sum := by decide
  have hdescent : baseEnd_6877010 < baseStart_6877010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877023 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 3]
def baseStart_6877023 : Nat := 118140960795 + 6877023 * 2 ^ 59
def prefixEnd_6877023 : Nat := 4983230072969 + 3 ^ 40 * 6877023 * 2
def baseEnd_6877023 : Nat := 3531218271024752349585653

theorem tailTrace_6877023 : CollatzResearch.WordTrace tailWord_6877023 prefixEnd_6877023 3531218271024752349585653 := by
  unfold tailWord_6877023
  simp only [CollatzResearch.WordTrace]
  refine ⟨250825634964727647866627723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167217089976485098577751815 250825634964727647866627723)
  ·
    refine ⟨376238452447091471799941585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250825634964727647866627723 376238452447091471799941585)
    ·
      refine ⟨282178839335318603849956189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376238452447091471799941585 282178839335318603849956189)
      ·
        refine ⟨105817064750744476443733571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282178839335318603849956189 105817064750744476443733571)
        ·
          refine ⟨158725597126116714665600357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105817064750744476443733571 158725597126116714665600357)
          ·
            refine ⟨29761049461146883999800067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158725597126116714665600357 29761049461146883999800067)
            ·
              refine ⟨44641574191720325999700101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29761049461146883999800067 44641574191720325999700101)
              ·
                refine ⟨8370295160947561124943769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44641574191720325999700101 8370295160947561124943769)
                ·
                  refine ⟨6277721370710670843707827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8370295160947561124943769 6277721370710670843707827)
                  ·
                    refine ⟨9416582056066006265561741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6277721370710670843707827 9416582056066006265561741)
                    ·
                      refine ⟨3531218271024752349585653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9416582056066006265561741 3531218271024752349585653)
                      ·
                        rfl

theorem cell23_6877023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_6877023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877023 prefixEnd_6877023 := by exact prefixLift 6877023
  have htrace : WordTrace (prefixWord ++ tailWord_6877023) baseStart_6877023 baseEnd_6877023 := by
    simpa [prefixWord, tailWord_6877023, baseEnd_6877023] using wordTrace_append hprefix tailTrace_6877023
  have hstable : (prefixWord ++ tailWord_6877023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877023).length < 2 ^ (prefixWord ++ tailWord_6877023).sum := by decide
  have hdescent : baseEnd_6877023 < baseStart_6877023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877024 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 1, 2, 2]
def baseStart_6877024 : Nat := 118140960795 + 6877024 * 2 ^ 59
def prefixEnd_6877024 : Nat := 4983230072969 + 3 ^ 40 * 6877024 * 2
def baseEnd_6877024 : Nat := 3531218784505406845673149

theorem tailTrace_6877024 : CollatzResearch.WordTrace tailWord_6877024 prefixEnd_6877024 3531218784505406845673149 := by
  unfold tailWord_6877024
  simp only [CollatzResearch.WordTrace]
  refine ⟨125412835718862012518707063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167217114291816016691609417 125412835718862012518707063)
  ·
    refine ⟨188119253578293018778060595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125412835718862012518707063 188119253578293018778060595)
    ·
      refine ⟨282178880367439528167090893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188119253578293018778060595 282178880367439528167090893)
      ·
        refine ⟨105817080137789823062659085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282178880367439528167090893 105817080137789823062659085)
        ·
          refine ⟨39681405051671183648497157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105817080137789823062659085 39681405051671183648497157)
          ·
            refine ⟨7440263447188346934093217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39681405051671183648497157 7440263447188346934093217)
            ·
              refine ⟨5580197585391260200569913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7440263447188346934093217 5580197585391260200569913)
              ·
                refine ⟨4185148189043445150427435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5580197585391260200569913 4185148189043445150427435)
                ·
                  refine ⟨6277722283565167725641153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185148189043445150427435 6277722283565167725641153)
                  ·
                    refine ⟨4708291712673875794230865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6277722283565167725641153 4708291712673875794230865)
                    ·
                      refine ⟨3531218784505406845673149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708291712673875794230865 3531218784505406845673149)
                      ·
                        rfl

theorem cell23_6877024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_6877024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877024 prefixEnd_6877024 := by exact prefixLift 6877024
  have htrace : WordTrace (prefixWord ++ tailWord_6877024) baseStart_6877024 baseEnd_6877024 := by
    simpa [prefixWord, tailWord_6877024, baseEnd_6877024] using wordTrace_append hprefix tailTrace_6877024
  have hstable : (prefixWord ++ tailWord_6877024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877024).length < 2 ^ (prefixWord ++ tailWord_6877024).sum := by decide
  have hdescent : baseEnd_6877024 < baseStart_6877024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877026 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6877026 : Nat := 118140960795 + 6877026 * 2 ^ 59
def prefixEnd_6877026 : Nat := 4983230072969 + 3 ^ 40 * 6877026 * 2
def baseEnd_6877026 : Nat := 1177073270488905279282713

theorem tailTrace_6877026 : CollatzResearch.WordTrace tailWord_6877026 prefixEnd_6877026 1177073270488905279282713 := by
  unfold tailWord_6877026
  simp only [CollatzResearch.WordTrace]
  refine ⟨62706436095929194844746733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167217162922477852919324621 62706436095929194844746733)
  ·
    refine ⟨23514913535973448066780025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62706436095929194844746733 23514913535973448066780025)
    ·
      refine ⟨17636185151980086050085019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23514913535973448066780025 17636185151980086050085019)
      ·
        refine ⟨26454277727970129075127529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17636185151980086050085019 26454277727970129075127529)
        ·
          refine ⟨19840708295977596806345647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26454277727970129075127529 19840708295977596806345647)
          ·
            refine ⟨29761062443966395209518471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19840708295977596806345647 29761062443966395209518471)
            ·
              refine ⟨44641593665949592814277707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29761062443966395209518471 44641593665949592814277707)
              ·
                refine ⟨66962390498924389221416561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44641593665949592814277707 66962390498924389221416561)
                ·
                  refine ⟨50221792874193291916062421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66962390498924389221416561 50221792874193291916062421)
                  ·
                    refine ⟨1177073270488905279282713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50221792874193291916062421 1177073270488905279282713)
                    ·
                      rfl

theorem cell23_6877026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6877026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877026 prefixEnd_6877026 := by exact prefixLift 6877026
  have htrace : WordTrace (prefixWord ++ tailWord_6877026) baseStart_6877026 baseEnd_6877026 := by
    simpa [prefixWord, tailWord_6877026, baseEnd_6877026] using wordTrace_append hprefix tailTrace_6877026
  have hstable : (prefixWord ++ tailWord_6877026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877026).length < 2 ^ (prefixWord ++ tailWord_6877026).sum := by decide
  have hdescent : baseEnd_6877026 < baseStart_6877026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877129 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_6877129 : Nat := 118140960795 + 6877129 * 2 ^ 59
def prefixEnd_6877129 : Nat := 4983230072969 + 3 ^ 40 * 6877129 * 2
def baseEnd_6877129 : Nat := 1177090899991376311620055

theorem tailTrace_6877129 : CollatzResearch.WordTrace tailWord_6877129 prefixEnd_6877129 1177090899991376311620055 := by
  unfold tailWord_6877129
  simp only [CollatzResearch.WordTrace]
  refine ⟨250829501102343627969986441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167219667401562418646657627 250829501102343627969986441)
  ·
    refine ⟨188122125826757720977489831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250829501102343627969986441 188122125826757720977489831)
    ·
      refine ⟨282183188740136581466234747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188122125826757720977489831 282183188740136581466234747)
      ·
        refine ⟨423274783110204872199352121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282183188740136581466234747 423274783110204872199352121)
        ·
          refine ⟨317456087332653654149514091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423274783110204872199352121 317456087332653654149514091)
          ·
            refine ⟨476184130998980481224271137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317456087332653654149514091 476184130998980481224271137)
            ·
              refine ⟨357138098249235360918203353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476184130998980481224271137 357138098249235360918203353)
              ·
                refine ⟨267853573686926520688652515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357138098249235360918203353 267853573686926520688652515)
                ·
                  refine ⟨401780360530389781032978773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267853573686926520688652515 401780360530389781032978773)
                  ·
                    refine ⟨1177090899991376311620055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 401780360530389781032978773 1177090899991376311620055)
                    ·
                      rfl

theorem cell23_6877129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_6877129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877129 prefixEnd_6877129 := by exact prefixLift 6877129
  have htrace : WordTrace (prefixWord ++ tailWord_6877129) baseStart_6877129 baseEnd_6877129 := by
    simpa [prefixWord, tailWord_6877129, baseEnd_6877129] using wordTrace_append hprefix tailTrace_6877129
  have hstable : (prefixWord ++ tailWord_6877129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877129).length < 2 ^ (prefixWord ++ tailWord_6877129).sum := by decide
  have hdescent : baseEnd_6877129 < baseStart_6877129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877136 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_6877136 : Nat := 118140960795 + 6877136 * 2 ^ 59
def prefixEnd_6877136 : Nat := 4983230072969 + 3 ^ 40 * 6877136 * 2
def baseEnd_6877136 : Nat := 3531276294338710407472633

theorem tailTrace_6877136 : CollatzResearch.WordTrace tailWord_6877136 prefixEnd_6877136 3531276294338710407472633 := by
  unfold tailWord_6877136
  simp only [CollatzResearch.WordTrace]
  refine ⟨125414878206659134082745631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167219837608878845443660841 125414878206659134082745631)
  ·
    refine ⟨188122317309988701124118447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125414878206659134082745631 188122317309988701124118447)
    ·
      refine ⟨282183475964983051686177671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188122317309988701124118447 282183475964983051686177671)
      ·
        refine ⟨423275213947474577529266507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282183475964983051686177671 423275213947474577529266507)
        ·
          refine ⟨634912820921211866293899761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423275213947474577529266507 634912820921211866293899761)
          ·
            refine ⟨476184615690908899720424821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634912820921211866293899761 476184615690908899720424821)
            ·
              refine ⟨44642307721022709348789827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476184615690908899720424821 44642307721022709348789827)
              ·
                refine ⟨66963461581534064023184741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44642307721022709348789827 66963461581534064023184741)
                ·
                  refine ⟨12555649046537637004347139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66963461581534064023184741 12555649046537637004347139)
                  ·
                    refine ⟨18833473569806455506520709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555649046537637004347139 18833473569806455506520709)
                    ·
                      refine ⟨3531276294338710407472633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18833473569806455506520709 3531276294338710407472633)
                      ·
                        rfl

theorem cell23_6877136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_6877136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877136 prefixEnd_6877136 := by exact prefixLift 6877136
  have htrace : WordTrace (prefixWord ++ tailWord_6877136) baseStart_6877136 baseEnd_6877136 := by
    simpa [prefixWord, tailWord_6877136, baseEnd_6877136] using wordTrace_append hprefix tailTrace_6877136
  have hstable : (prefixWord ++ tailWord_6877136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877136).length < 2 ^ (prefixWord ++ tailWord_6877136).sum := by decide
  have hdescent : baseEnd_6877136 < baseStart_6877136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877153 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_6877153 : Nat := 118140960795 + 6877153 * 2 ^ 59
def prefixEnd_6877153 : Nat := 4983230072969 + 3 ^ 40 * 6877153 * 2
def baseEnd_6877153 : Nat := 3531285023509836840960055

theorem tailTrace_6877153 : CollatzResearch.WordTrace tailWord_6877153 prefixEnd_6877153 3531285023509836840960055 := by
  unfold tailWord_6877153
  simp only [CollatzResearch.WordTrace]
  refine ⟨250830376454256680068860113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167220250969504453379240075 250830376454256680068860113)
  ·
    refine ⟨188122782340692510051645085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250830376454256680068860113 188122782340692510051645085)
    ·
      refine ⟨70546043377759691269366907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188122782340692510051645085 70546043377759691269366907)
      ·
        refine ⟨105819065066639536904050361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70546043377759691269366907 105819065066639536904050361)
        ·
          refine ⟨79364298799979652678037771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105819065066639536904050361 79364298799979652678037771)
          ·
            refine ⟨119046448199969479017056657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79364298799979652678037771 119046448199969479017056657)
            ·
              refine ⟨89284836149977109262792493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119046448199969479017056657 89284836149977109262792493)
              ·
                refine ⟨33481813556241415973547185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89284836149977109262792493 33481813556241415973547185)
                ·
                  refine ⟨25111360167181061980160389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33481813556241415973547185 25111360167181061980160389)
                  ·
                    refine ⟨4708380031346449121280073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25111360167181061980160389 4708380031346449121280073)
                    ·
                      refine ⟨3531285023509836840960055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708380031346449121280073 3531285023509836840960055)
                      ·
                        rfl

theorem cell23_6877153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_6877153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877153 prefixEnd_6877153 := by exact prefixLift 6877153
  have htrace : WordTrace (prefixWord ++ tailWord_6877153) baseStart_6877153 baseEnd_6877153 := by
    simpa [prefixWord, tailWord_6877153, baseEnd_6877153] using wordTrace_append hprefix tailTrace_6877153
  have hstable : (prefixWord ++ tailWord_6877153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877153).length < 2 ^ (prefixWord ++ tailWord_6877153).sum := by decide
  have hdescent : baseEnd_6877153 < baseStart_6877153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877180 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_6877180 : Nat := 118140960795 + 6877180 * 2 ^ 59
def prefixEnd_6877180 : Nat := 4983230072969 + 3 ^ 40 * 6877180 * 2
def baseEnd_6877180 : Nat := 1177099629162502745107477

theorem tailTrace_6877180 : CollatzResearch.WordTrace tailWord_6877180 prefixEnd_6877180 1177099629162502745107477 := by
  unfold tailWord_6877180
  simp only [CollatzResearch.WordTrace]
  refine ⟨125415680612579431840046497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167220907483439242453395329 125415680612579431840046497)
  ·
    refine ⟨94061760459434573880034873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125415680612579431840046497 94061760459434573880034873)
    ·
      refine ⟨70546320344575930410026155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94061760459434573880034873 70546320344575930410026155)
      ·
        refine ⟨105819480516863895615039233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70546320344575930410026155 105819480516863895615039233)
        ·
          refine ⟨79364610387647921711279425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105819480516863895615039233 79364610387647921711279425)
          ·
            refine ⟨59523457790735941283459569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79364610387647921711279425 59523457790735941283459569)
            ·
              refine ⟨44642593343051955962594677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59523457790735941283459569 44642593343051955962594677)
              ·
                refine ⟨4185243125911120871493251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44642593343051955962594677 4185243125911120871493251)
                ·
                  refine ⟨6277864688866681307239877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185243125911120871493251 6277864688866681307239877)
                  ·
                    refine ⟨1177099629162502745107477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6277864688866681307239877 1177099629162502745107477)
                    ·
                      rfl

theorem cell23_6877180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_6877180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877180 prefixEnd_6877180 := by exact prefixLift 6877180
  have htrace : WordTrace (prefixWord ++ tailWord_6877180) baseStart_6877180 baseEnd_6877180 := by
    simpa [prefixWord, tailWord_6877180, baseEnd_6877180] using wordTrace_append hprefix tailTrace_6877180
  have hstable : (prefixWord ++ tailWord_6877180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877180).length < 2 ^ (prefixWord ++ tailWord_6877180).sum := by decide
  have hdescent : baseEnd_6877180 < baseStart_6877180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877196 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6877196 : Nat := 118140960795 + 6877196 * 2 ^ 59
def prefixEnd_6877196 : Nat := 4983230072969 + 3 ^ 40 * 6877196 * 2
def baseEnd_6877196 : Nat := 3531307103177980172722357

theorem tailTrace_6877196 : CollatzResearch.WordTrace tailWord_6877196 prefixEnd_6877196 3531307103177980172722357 := by
  unfold tailWord_6877196
  simp only [CollatzResearch.WordTrace]
  refine ⟨125415972396550449206337721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167221296528733932275116961 125415972396550449206337721)
  ·
    refine ⟨94061979297412836904753291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125415972396550449206337721 94061979297412836904753291)
    ·
      refine ⟨141092968946119255357129937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94061979297412836904753291 141092968946119255357129937)
      ·
        refine ⟨105819726709589441517847453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141092968946119255357129937 105819726709589441517847453)
        ·
          refine ⟨39682397516096040569192795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105819726709589441517847453 39682397516096040569192795)
          ·
            refine ⟨59523596274144060853789193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39682397516096040569192795 59523596274144060853789193)
            ·
              refine ⟨44642697205608045640341895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59523596274144060853789193 44642697205608045640341895)
              ·
                refine ⟨66964045808412068460512843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44642697205608045640341895 66964045808412068460512843)
                ·
                  refine ⟨100446068712618102690769265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66964045808412068460512843 100446068712618102690769265)
                  ·
                    refine ⟨75334551534463577018076949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100446068712618102690769265 75334551534463577018076949)
                    ·
                      refine ⟨3531307103177980172722357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75334551534463577018076949 3531307103177980172722357)
                      ·
                        rfl

theorem cell23_6877196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6877196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877196 prefixEnd_6877196 := by exact prefixLift 6877196
  have htrace : WordTrace (prefixWord ++ tailWord_6877196) baseStart_6877196 baseEnd_6877196 := by
    simpa [prefixWord, tailWord_6877196, baseEnd_6877196] using wordTrace_append hprefix tailTrace_6877196
  have hstable : (prefixWord ++ tailWord_6877196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877196).length < 2 ^ (prefixWord ++ tailWord_6877196).sum := by decide
  have hdescent : baseEnd_6877196 < baseStart_6877196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877204 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6877204 : Nat := 118140960795 + 6877204 * 2 ^ 59
def prefixEnd_6877204 : Nat := 4983230072969 + 3 ^ 40 * 6877204 * 2
def baseEnd_6877204 : Nat := 3531311211023216141422321

theorem tailTrace_6877204 : CollatzResearch.WordTrace tailWord_6877204 prefixEnd_6877204 3531311211023216141422321 := by
  unfold tailWord_6877204
  simp only [CollatzResearch.WordTrace]
  refine ⟨125416118288535957889483333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167221491051381277185977777 125416118288535957889483333)
  ·
    refine ⟨23515522179100492104278125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125416118288535957889483333 23515522179100492104278125)
    ·
      refine ⟨8818320817162684539104297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23515522179100492104278125 8818320817162684539104297)
      ·
        refine ⟨6613740612872013404328223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8818320817162684539104297 6613740612872013404328223)
        ·
          refine ⟨9920610919308020106492335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613740612872013404328223 9920610919308020106492335)
          ·
            refine ⟨14880916378962030159738503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920610919308020106492335 14880916378962030159738503)
            ·
              refine ⟨22321374568443045239607755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14880916378962030159738503 22321374568443045239607755)
              ·
                refine ⟨33482061852664567859411633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22321374568443045239607755 33482061852664567859411633)
                ·
                  refine ⟨25111546389498425894558725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33482061852664567859411633 25111546389498425894558725)
                  ·
                    refine ⟨4708414948030954855229761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25111546389498425894558725 4708414948030954855229761)
                    ·
                      refine ⟨3531311211023216141422321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708414948030954855229761 3531311211023216141422321)
                      ·
                        rfl

theorem cell23_6877204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6877204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877204 prefixEnd_6877204 := by exact prefixLift 6877204
  have htrace : WordTrace (prefixWord ++ tailWord_6877204) baseStart_6877204 baseEnd_6877204 := by
    simpa [prefixWord, tailWord_6877204, baseEnd_6877204] using wordTrace_append hprefix tailTrace_6877204
  have hstable : (prefixWord ++ tailWord_6877204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877204).length < 2 ^ (prefixWord ++ tailWord_6877204).sum := by decide
  have hdescent : baseEnd_6877204 < baseStart_6877204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877224 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6877224 : Nat := 118140960795 + 6877224 * 2 ^ 59
def prefixEnd_6877224 : Nat := 4983230072969 + 3 ^ 40 * 6877224 * 2
def baseEnd_6877224 : Nat := 3531321480636306063172229

theorem tailTrace_6877224 : CollatzResearch.WordTrace tailWord_6877224 prefixEnd_6877224 3531321480636306063172229 := by
  unfold tailWord_6877224
  simp only [CollatzResearch.WordTrace]
  refine ⟨125416483018499729597347363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167221977357999639463129817 125416483018499729597347363)
  ·
    refine ⟨188124724527749594396021045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125416483018499729597347363 188124724527749594396021045)
    ·
      refine ⟨17636692924476524474626973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188124724527749594396021045 17636692924476524474626973)
      ·
        refine ⟨6613759846678696677985115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17636692924476524474626973 6613759846678696677985115)
        ·
          refine ⟨9920639770018045016977673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613759846678696677985115 9920639770018045016977673)
          ·
            refine ⟨7440479827513533762733255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9920639770018045016977673 7440479827513533762733255)
            ·
              refine ⟨11160719741270300644099883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440479827513533762733255 11160719741270300644099883)
              ·
                refine ⟨16741079611905450966149825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11160719741270300644099883 16741079611905450966149825)
                ·
                  refine ⟨12555809708929088224612369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16741079611905450966149825 12555809708929088224612369)
                  ·
                    refine ⟨9416857281696816168459277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12555809708929088224612369 9416857281696816168459277)
                    ·
                      refine ⟨3531321480636306063172229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9416857281696816168459277 3531321480636306063172229)
                      ·
                        rfl

theorem cell23_6877224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6877224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877224 prefixEnd_6877224 := by exact prefixLift 6877224
  have htrace : WordTrace (prefixWord ++ tailWord_6877224) baseStart_6877224 baseEnd_6877224 := by
    simpa [prefixWord, tailWord_6877224, baseEnd_6877224] using wordTrace_append hprefix tailTrace_6877224
  have hstable : (prefixWord ++ tailWord_6877224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877224).length < 2 ^ (prefixWord ++ tailWord_6877224).sum := by decide
  have hdescent : baseEnd_6877224 < baseStart_6877224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877237 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_6877237 : Nat := 118140960795 + 6877237 * 2 ^ 59
def prefixEnd_6877237 : Nat := 4983230072969 + 3 ^ 40 * 6877237 * 2
def baseEnd_6877237 : Nat := 3531328155884814512309669

theorem tailTrace_6877237 : CollatzResearch.WordTrace tailWord_6877237 prefixEnd_6877237 3531328155884814512309669 := by
  unfold tailWord_6877237
  simp only [CollatzResearch.WordTrace]
  refine ⟨250833440185952362414917965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167222293457301574943278643 250833440185952362414917965)
  ·
    refine ⟨94062540069732135905594237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250833440185952362414917965 94062540069732135905594237)
    ·
      refine ⟨35273452526149550964597839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94062540069732135905594237 35273452526149550964597839)
      ·
        refine ⟨52910178789224326446896759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35273452526149550964597839 52910178789224326446896759)
        ·
          refine ⟨79365268183836489670345139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52910178789224326446896759 79365268183836489670345139)
          ·
            refine ⟨119047902275754734505517709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79365268183836489670345139 119047902275754734505517709)
            ·
              refine ⟨44642963353408025439569141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119047902275754734505517709 44642963353408025439569141)
              ·
                refine ⟨4185277814382002384959607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44642963353408025439569141 4185277814382002384959607)
                ·
                  refine ⟨6277916721573003577439411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185277814382002384959607 6277916721573003577439411)
                  ·
                    refine ⟨9416875082359505366159117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6277916721573003577439411 9416875082359505366159117)
                    ·
                      refine ⟨3531328155884814512309669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9416875082359505366159117 3531328155884814512309669)
                      ·
                        rfl

theorem cell23_6877237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_6877237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877237 prefixEnd_6877237 := by exact prefixLift 6877237
  have htrace : WordTrace (prefixWord ++ tailWord_6877237) baseStart_6877237 baseEnd_6877237 := by
    simpa [prefixWord, tailWord_6877237, baseEnd_6877237] using wordTrace_append hprefix tailTrace_6877237
  have hstable : (prefixWord ++ tailWord_6877237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877237).length < 2 ^ (prefixWord ++ tailWord_6877237).sum := by decide
  have hdescent : baseEnd_6877237 < baseStart_6877237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877240 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 1, 5]
def baseStart_6877240 : Nat := 118140960795 + 6877240 * 2 ^ 59
def prefixEnd_6877240 : Nat := 4983230072969 + 3 ^ 40 * 6877240 * 2
def baseEnd_6877240 : Nat := 1177109898775592666857385

theorem tailTrace_6877240 : CollatzResearch.WordTrace tailWord_6877240 prefixEnd_6877240 1177109898775592666857385 := by
  unfold tailWord_6877240
  simp only [CollatzResearch.WordTrace]
  refine ⟨125416774802470746963638587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167222366403294329284851449 125416774802470746963638587)
  ·
    refine ⟨188125162203706120445457881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125416774802470746963638587 188125162203706120445457881)
    ·
      refine ⟨141093871652779590334093411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188125162203706120445457881 141093871652779590334093411)
      ·
        refine ⟨211640807479169385501140117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141093871652779590334093411 211640807479169385501140117)
        ·
          refine ⟨9920662850586064945365943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211640807479169385501140117 9920662850586064945365943)
          ·
            refine ⟨14880994275879097418048915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920662850586064945365943 14880994275879097418048915)
            ·
              refine ⟨22321491413818646127073373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14880994275879097418048915 22321491413818646127073373)
              ·
                refine ⟨8370559280181992297652515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22321491413818646127073373 8370559280181992297652515)
                ·
                  refine ⟨12555838920272988446478773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370559280181992297652515 12555838920272988446478773)
                  ·
                    refine ⟨1177109898775592666857385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12555838920272988446478773 1177109898775592666857385)
                    ·
                      rfl

theorem cell23_6877240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_6877240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877240 prefixEnd_6877240 := by exact prefixLift 6877240
  have htrace : WordTrace (prefixWord ++ tailWord_6877240) baseStart_6877240 baseEnd_6877240 := by
    simpa [prefixWord, tailWord_6877240, baseEnd_6877240] using wordTrace_append hprefix tailTrace_6877240
  have hstable : (prefixWord ++ tailWord_6877240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877240).length < 2 ^ (prefixWord ++ tailWord_6877240).sum := by decide
  have hdescent : baseEnd_6877240 < baseStart_6877240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877243 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 4]
def baseStart_6877243 : Nat := 118140960795 + 6877243 * 2 ^ 59
def prefixEnd_6877243 : Nat := 4983230072969 + 3 ^ 40 * 6877243 * 2
def baseEnd_6877243 : Nat := 3531331236768741488834641

theorem tailTrace_6877243 : CollatzResearch.WordTrace tailWord_6877243 prefixEnd_6877243 3531331236768741488834641 := by
  unfold tailWord_6877243
  simp only [CollatzResearch.WordTrace]
  refine ⟨250833659023930625439636383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167222439349287083626424255 250833659023930625439636383)
  ·
    refine ⟨376250488535895938159454575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250833659023930625439636383 376250488535895938159454575)
    ·
      refine ⟨564375732803843907239181863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376250488535895938159454575 564375732803843907239181863)
      ·
        refine ⟨846563599205765860858772795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564375732803843907239181863 846563599205765860858772795)
        ·
          refine ⟨1269845398808648791288159193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846563599205765860858772795 1269845398808648791288159193)
          ·
            refine ⟨952384049106486593466119395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269845398808648791288159193 952384049106486593466119395)
            ·
              refine ⟨1428576073659729890199179093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952384049106486593466119395 1428576073659729890199179093)
              ·
                refine ⟨8370562931599979825385815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1428576073659729890199179093 8370562931599979825385815)
                ·
                  refine ⟨12555844397399969738078723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370562931599979825385815 12555844397399969738078723)
                  ·
                    refine ⟨18833766596099954607118085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555844397399969738078723 18833766596099954607118085)
                    ·
                      refine ⟨3531331236768741488834641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18833766596099954607118085 3531331236768741488834641)
                      ·
                        rfl

theorem cell23_6877243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 4].length) (baseStart_6877243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877243 prefixEnd_6877243 := by exact prefixLift 6877243
  have htrace : WordTrace (prefixWord ++ tailWord_6877243) baseStart_6877243 baseEnd_6877243 := by
    simpa [prefixWord, tailWord_6877243, baseEnd_6877243] using wordTrace_append hprefix tailTrace_6877243
  have hstable : (prefixWord ++ tailWord_6877243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877243).length < 2 ^ (prefixWord ++ tailWord_6877243).sum := by decide
  have hdescent : baseEnd_6877243 < baseStart_6877243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877254 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6877254 : Nat := 118140960795 + 6877254 * 2 ^ 59
def prefixEnd_6877254 : Nat := 4983230072969 + 3 ^ 40 * 6877254 * 2
def baseEnd_6877254 : Nat := 3531336885055940945797091

theorem tailTrace_6877254 : CollatzResearch.WordTrace tailWord_6877254 prefixEnd_6877254 3531336885055940945797091 := by
  unfold tailWord_6877254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838564382090336697446463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167222706817927182878857877 7838564382090336697446463)
  ·
    refine ⟨11757846573135505046169695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7838564382090336697446463 11757846573135505046169695)
    ·
      refine ⟨17636769859703257569254543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11757846573135505046169695 17636769859703257569254543)
      ·
        refine ⟨26455154789554886353881815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17636769859703257569254543 26455154789554886353881815)
        ·
          refine ⟨39682732184332329530822723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26455154789554886353881815 39682732184332329530822723)
          ·
            refine ⟨59524098276498494296234085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39682732184332329530822723 59524098276498494296234085)
            ·
              refine ⟨11160768426843467680543891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59524098276498494296234085 11160768426843467680543891)
              ·
                refine ⟨16741152640265201520815837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11160768426843467680543891 16741152640265201520815837)
                ·
                  refine ⟨6277932240099450570305939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16741152640265201520815837 6277932240099450570305939)
                  ·
                    refine ⟨9416898360149175855458909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6277932240099450570305939 9416898360149175855458909)
                    ·
                      refine ⟨3531336885055940945797091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9416898360149175855458909 3531336885055940945797091)
                      ·
                        rfl

theorem cell23_6877254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6877254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877254 prefixEnd_6877254 := by exact prefixLift 6877254
  have htrace : WordTrace (prefixWord ++ tailWord_6877254) baseStart_6877254 baseEnd_6877254 := by
    simpa [prefixWord, tailWord_6877254, baseEnd_6877254] using wordTrace_append hprefix tailTrace_6877254
  have hstable : (prefixWord ++ tailWord_6877254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877254).length < 2 ^ (prefixWord ++ tailWord_6877254).sum := by decide
  have hdescent : baseEnd_6877254 < baseStart_6877254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877277 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6877277 : Nat := 118140960795 + 6877277 * 2 ^ 59
def prefixEnd_6877277 : Nat := 4983230072969 + 3 ^ 40 * 6877277 * 2
def baseEnd_6877277 : Nat := 3531348695110994355809485

theorem tailTrace_6877277 : CollatzResearch.WordTrace tailWord_6877277 prefixEnd_6877277 3531348695110994355809485 := by
  unfold tailWord_6877277
  simp only [CollatzResearch.WordTrace]
  refine ⟨250834899105807449246374085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167223266070538299497582723 250834899105807449246374085)
  ·
    refine ⟨47031543582338896733695141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250834899105807449246374085 47031543582338896733695141)
    ·
      refine ⟨8818414421688543137567839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47031543582338896733695141 8818414421688543137567839)
      ·
        refine ⟨13227621632532814706351759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818414421688543137567839 13227621632532814706351759)
        ·
          refine ⟨19841432448799222059527639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13227621632532814706351759 19841432448799222059527639)
          ·
            refine ⟨29762148673198833089291459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19841432448799222059527639 29762148673198833089291459)
            ·
              refine ⟨44643223009798249633937189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29762148673198833089291459 44643223009798249633937189)
              ·
                refine ⟨8370604314337171806363223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44643223009798249633937189 8370604314337171806363223)
                ·
                  refine ⟨12555906471505757709544835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370604314337171806363223 12555906471505757709544835)
                  ·
                    refine ⟨18833859707258636564317253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12555906471505757709544835 18833859707258636564317253)
                    ·
                      refine ⟨3531348695110994355809485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18833859707258636564317253 3531348695110994355809485)
                      ·
                        rfl

theorem cell23_6877277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6877277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877277 prefixEnd_6877277 := by exact prefixLift 6877277
  have htrace : WordTrace (prefixWord ++ tailWord_6877277) baseStart_6877277 baseEnd_6877277 := by
    simpa [prefixWord, tailWord_6877277, baseEnd_6877277] using wordTrace_append hprefix tailTrace_6877277
  have hstable : (prefixWord ++ tailWord_6877277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877277).length < 2 ^ (prefixWord ++ tailWord_6877277).sum := by decide
  have hdescent : baseEnd_6877277 < baseStart_6877277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877280 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3]
def baseStart_6877280 : Nat := 118140960795 + 6877280 * 2 ^ 59
def prefixEnd_6877280 : Nat := 4983230072969 + 3 ^ 40 * 6877280 * 2
def baseEnd_6877280 : Nat := 3531350235552957844071971

theorem tailTrace_6877280 : CollatzResearch.WordTrace tailWord_6877280 prefixEnd_6877280 3531350235552957844071971 := by
  unfold tailWord_6877280
  simp only [CollatzResearch.WordTrace]
  refine ⟨125417504262398290379366647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167223339016531053839155529 125417504262398290379366647)
  ·
    refine ⟨188126256393597435569049971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125417504262398290379366647 188126256393597435569049971)
    ·
      refine ⟨282189384590396153353574957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188126256393597435569049971 282189384590396153353574957)
      ·
        refine ⟨105821019221398557507590609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282189384590396153353574957 105821019221398557507590609)
        ·
          refine ⟨79365764416048918130692957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105821019221398557507590609 79365764416048918130692957)
          ·
            refine ⟨29762161656018344299009859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79365764416048918130692957 29762161656018344299009859)
            ·
              refine ⟨44643242484027516448514789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29762161656018344299009859 44643242484027516448514789)
              ·
                refine ⟨8370607965755159334096523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44643242484027516448514789 8370607965755159334096523)
                ·
                  refine ⟨12555911948632739001144785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370607965755159334096523 12555911948632739001144785)
                  ·
                    refine ⟨9416933961474554250858589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12555911948632739001144785 9416933961474554250858589)
                    ·
                      refine ⟨3531350235552957844071971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9416933961474554250858589 3531350235552957844071971)
                      ·
                        rfl

theorem cell23_6877280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_6877280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877280 prefixEnd_6877280 := by exact prefixLift 6877280
  have htrace : WordTrace (prefixWord ++ tailWord_6877280) baseStart_6877280 baseEnd_6877280 := by
    simpa [prefixWord, tailWord_6877280, baseEnd_6877280] using wordTrace_append hprefix tailTrace_6877280
  have hstable : (prefixWord ++ tailWord_6877280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877280).length < 2 ^ (prefixWord ++ tailWord_6877280).sum := by decide
  have hdescent : baseEnd_6877280 < baseStart_6877280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877283 : List Nat := [1, 1, 1, 5, 1, 1, 6, 7]
def baseStart_6877283 : Nat := 118140960795 + 6877283 * 2 ^ 59
def prefixEnd_6877283 : Nat := 4983230072969 + 3 ^ 40 * 6877283 * 2
def baseEnd_6877283 : Nat := 130790806518330419716091

theorem tailTrace_6877283 : CollatzResearch.WordTrace tailWord_6877283 prefixEnd_6877283 130790806518330419716091 := by
  unfold tailWord_6877283
  simp only [CollatzResearch.WordTrace]
  refine ⟨250835117943785712271092503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167223411962523808180728335 250835117943785712271092503)
  ·
    refine ⟨376252676915678568406638755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250835117943785712271092503 376252676915678568406638755)
    ·
      refine ⟨564379015373517852609958133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376252676915678568406638755 564379015373517852609958133)
      ·
        refine ⟨52910532691267298682183575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 564379015373517852609958133 52910532691267298682183575)
        ·
          refine ⟨79365799036900948023275363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52910532691267298682183575 79365799036900948023275363)
          ·
            refine ⟨119048698555351422034913045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79365799036900948023275363 119048698555351422034913045)
            ·
              refine ⟨5580407744782097907886549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119048698555351422034913045 5580407744782097907886549)
              ·
                refine ⟨130790806518330419716091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5580407744782097907886549 130790806518330419716091)
                ·
                  rfl

theorem cell23_6877283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 7].length) (baseStart_6877283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877283 prefixEnd_6877283 := by exact prefixLift 6877283
  have htrace : WordTrace (prefixWord ++ tailWord_6877283) baseStart_6877283 baseEnd_6877283 := by
    simpa [prefixWord, tailWord_6877283, baseEnd_6877283] using wordTrace_append hprefix tailTrace_6877283
  have hstable : (prefixWord ++ tailWord_6877283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877283).length < 2 ^ (prefixWord ++ tailWord_6877283).sum := by decide
  have hdescent : baseEnd_6877283 < baseStart_6877283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877363 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4]
def baseStart_6877363 : Nat := 118140960795 + 6877363 * 2 ^ 59
def prefixEnd_6877363 : Nat := 4983230072969 + 3 ^ 40 * 6877363 * 2
def baseEnd_6877363 : Nat := 3531392854447281019334089

theorem tailTrace_6877363 : CollatzResearch.WordTrace tailWord_6877363 prefixEnd_6877363 3531392854447281019334089 := by
  unfold tailWord_6877363
  simp only [CollatzResearch.WordTrace]
  refine ⟨250838035783495885934004743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167225357188997257289336495 250838035783495885934004743)
  ·
    refine ⟨376257053675243828901007115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250838035783495885934004743 376257053675243828901007115)
    ·
      refine ⟨564385580512865743351510673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376257053675243828901007115 564385580512865743351510673)
      ·
        refine ⟨423289185384649307513633005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564385580512865743351510673 423289185384649307513633005)
        ·
          refine ⟨158733444519243490317612377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423289185384649307513633005 158733444519243490317612377)
          ·
            refine ⟨119050083389432617738209283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158733444519243490317612377 119050083389432617738209283)
            ·
              refine ⟨178575125084148926607313925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119050083389432617738209283 178575125084148926607313925)
              ·
                refine ⟨33482835953277923738871361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178575125084148926607313925 33482835953277923738871361)
                ·
                  refine ⟨25112126964958442804153521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33482835953277923738871361 25112126964958442804153521)
                  ·
                    refine ⟨18834095223718832103115141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25112126964958442804153521 18834095223718832103115141)
                    ·
                      refine ⟨3531392854447281019334089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18834095223718832103115141 3531392854447281019334089)
                      ·
                        rfl

theorem cell23_6877363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_6877363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877363 prefixEnd_6877363 := by exact prefixLift 6877363
  have htrace : WordTrace (prefixWord ++ tailWord_6877363) baseStart_6877363 baseEnd_6877363 := by
    simpa [prefixWord, tailWord_6877363, baseEnd_6877363] using wordTrace_append hprefix tailTrace_6877363
  have hstable : (prefixWord ++ tailWord_6877363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877363).length < 2 ^ (prefixWord ++ tailWord_6877363).sum := by decide
  have hdescent : baseEnd_6877363 < baseStart_6877363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877373 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 7]
def baseStart_6877373 : Nat := 118140960795 + 6877373 * 2 ^ 59
def prefixEnd_6877373 : Nat := 4983230072969 + 3 ^ 40 * 6877373 * 2
def baseEnd_6877373 : Nat := 392377554361536220023227

theorem tailTrace_6877373 : CollatzResearch.WordTrace tailWord_6877373 prefixEnd_6877373 392377554361536220023227 := by
  unfold tailWord_6877373
  simp only [CollatzResearch.WordTrace]
  refine ⟨250838400513459657641868773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167225600342306438427912515 250838400513459657641868773)
  ·
    refine ⟨47032200096273685807850395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250838400513459657641868773 47032200096273685807850395)
    ·
      refine ⟨70548300144410528711775593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47032200096273685807850395 70548300144410528711775593)
      ·
        refine ⟨52911225108307896533831695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70548300144410528711775593 52911225108307896533831695)
        ·
          refine ⟨79366837662461844800747543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52911225108307896533831695 79366837662461844800747543)
          ·
            refine ⟨119050256493692767201121315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79366837662461844800747543 119050256493692767201121315)
            ·
              refine ⟨178575384740539150801681973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119050256493692767201121315 178575384740539150801681973)
              ·
                refine ⟨16741442319425545387657685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178575384740539150801681973 16741442319425545387657685)
                ·
                  refine ⟨392377554361536220023227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16741442319425545387657685 392377554361536220023227)
                  ·
                    rfl

theorem cell23_6877373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_6877373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877373 prefixEnd_6877373 := by exact prefixLift 6877373
  have htrace : WordTrace (prefixWord ++ tailWord_6877373) baseStart_6877373 baseEnd_6877373 := by
    simpa [prefixWord, tailWord_6877373, baseEnd_6877373] using wordTrace_append hprefix tailTrace_6877373
  have hstable : (prefixWord ++ tailWord_6877373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877373).length < 2 ^ (prefixWord ++ tailWord_6877373).sum := by decide
  have hdescent : baseEnd_6877373 < baseStart_6877373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877377 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6877377 : Nat := 118140960795 + 6877377 * 2 ^ 59
def prefixEnd_6877377 : Nat := 4983230072969 + 3 ^ 40 * 6877377 * 2
def baseEnd_6877377 : Nat := 1177133347725481321519675

theorem tailTrace_6877377 : CollatzResearch.WordTrace tailWord_6877377 prefixEnd_6877377 1177133347725481321519675 := by
  unfold tailWord_6877377
  simp only [CollatzResearch.WordTrace]
  refine ⟨250838546405445166325014385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167225697603630110883342923 250838546405445166325014385)
  ·
    refine ⟨188128909804083874743760789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250838546405445166325014385 188128909804083874743760789)
    ·
      refine ⟨8818542647066431628613787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188128909804083874743760789 8818542647066431628613787)
      ·
        refine ⟨13227813970599647442920681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818542647066431628613787 13227813970599647442920681)
        ·
          refine ⟨9920860477949735582190511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13227813970599647442920681 9920860477949735582190511)
          ·
            refine ⟨14881290716924603373285767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920860477949735582190511 14881290716924603373285767)
            ·
              refine ⟨22321936075386905059928651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881290716924603373285767 22321936075386905059928651)
              ·
                refine ⟨33482904113080357589892977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22321936075386905059928651 33482904113080357589892977)
                ·
                  refine ⟨25112178084810268192419733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33482904113080357589892977 25112178084810268192419733)
                  ·
                    refine ⟨1177133347725481321519675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25112178084810268192419733 1177133347725481321519675)
                    ·
                      rfl

theorem cell23_6877377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6877377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877377 prefixEnd_6877377 := by exact prefixLift 6877377
  have htrace : WordTrace (prefixWord ++ tailWord_6877377) baseStart_6877377 baseEnd_6877377 := by
    simpa [prefixWord, tailWord_6877377, baseEnd_6877377] using wordTrace_append hprefix tailTrace_6877377
  have hstable : (prefixWord ++ tailWord_6877377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877377).length < 2 ^ (prefixWord ++ tailWord_6877377).sum := by decide
  have hdescent : baseEnd_6877377 < baseStart_6877377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877380 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6877380 : Nat := 118140960795 + 6877380 * 2 ^ 59
def prefixEnd_6877380 : Nat := 4983230072969 + 3 ^ 40 * 6877380 * 2
def baseEnd_6877380 : Nat := 3531401583618407452821511

theorem tailTrace_6877380 : CollatzResearch.WordTrace tailWord_6877380 prefixEnd_6877380 3531401583618407452821511 := by
  unfold tailWord_6877380
  simp only [CollatzResearch.WordTrace]
  refine ⟨125419327912217148918686797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167225770549622865224915729 125419327912217148918686797)
  ·
    refine ⟨47032247967081430844507549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125419327912217148918686797 47032247967081430844507549)
    ·
      refine ⟨17637092987655536566690331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47032247967081430844507549 17637092987655536566690331)
      ·
        refine ⟨26455639481483304850035497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17637092987655536566690331 26455639481483304850035497)
        ·
          refine ⟨19841729611112478637526623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26455639481483304850035497 19841729611112478637526623)
          ·
            refine ⟨29762594416668717956289935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19841729611112478637526623 29762594416668717956289935)
            ·
              refine ⟨44643891625003076934434903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29762594416668717956289935 44643891625003076934434903)
              ·
                refine ⟨66965837437504615401652355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44643891625003076934434903 66965837437504615401652355)
                ·
                  refine ⟨100448756156256923102478533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66965837437504615401652355 100448756156256923102478533)
                  ·
                    refine ⟨18834141779298173081714725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100448756156256923102478533 18834141779298173081714725)
                    ·
                      refine ⟨3531401583618407452821511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18834141779298173081714725 3531401583618407452821511)
                      ·
                        rfl

theorem cell23_6877380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6877380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877380 prefixEnd_6877380 := by exact prefixLift 6877380
  have htrace : WordTrace (prefixWord ++ tailWord_6877380) baseStart_6877380 baseEnd_6877380 := by
    simpa [prefixWord, tailWord_6877380, baseEnd_6877380] using wordTrace_append hprefix tailTrace_6877380
  have hstable : (prefixWord ++ tailWord_6877380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877380).length < 2 ^ (prefixWord ++ tailWord_6877380).sum := by decide
  have hdescent : baseEnd_6877380 < baseStart_6877380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877390 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_6877390 : Nat := 118140960795 + 6877390 * 2 ^ 59
def prefixEnd_6877390 : Nat := 4983230072969 + 3 ^ 40 * 6877390 * 2
def baseEnd_6877390 : Nat := 392378524269439157077385

theorem tailTrace_6877390 : CollatzResearch.WordTrace tailWord_6877390 prefixEnd_6877390 392378524269439157077385 := by
  unfold tailWord_6877390
  simp only [CollatzResearch.WordTrace]
  refine ⟨31354877569299758693154703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167226013702932046363491749 31354877569299758693154703)
  ·
    refine ⟨47032316353949638039732055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31354877569299758693154703 47032316353949638039732055)
    ·
      refine ⟨70548474530924457059598083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47032316353949638039732055 70548474530924457059598083)
      ·
        refine ⟨105822711796386685589397125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70548474530924457059598083 105822711796386685589397125)
        ·
          refine ⟨19841758461822503548011961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105822711796386685589397125 19841758461822503548011961)
          ·
            refine ⟨14881318846366877661008971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19841758461822503548011961 14881318846366877661008971)
            ·
              refine ⟨22321978269550316491513457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881318846366877661008971 22321978269550316491513457)
              ·
                refine ⟨16741483702162737368635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22321978269550316491513457 16741483702162737368635093)
                ·
                  refine ⟨392378524269439157077385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16741483702162737368635093 392378524269439157077385)
                  ·
                    rfl

theorem cell23_6877390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_6877390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877390 prefixEnd_6877390 := by exact prefixLift 6877390
  have htrace : WordTrace (prefixWord ++ tailWord_6877390) baseStart_6877390 baseEnd_6877390 := by
    simpa [prefixWord, tailWord_6877390, baseEnd_6877390] using wordTrace_append hprefix tailTrace_6877390
  have hstable : (prefixWord ++ tailWord_6877390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877390).length < 2 ^ (prefixWord ++ tailWord_6877390).sum := by decide
  have hdescent : baseEnd_6877390 < baseStart_6877390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877430 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6877430 : Nat := 118140960795 + 6877430 * 2 ^ 59
def prefixEnd_6877430 : Nat := 4983230072969 + 3 ^ 40 * 6877430 * 2
def baseEnd_6877430 : Nat := 3531427257651132257196281

theorem tailTrace_6877430 : CollatzResearch.WordTrace tailWord_6877430 prefixEnd_6877430 3531427257651132257196281 := by
  unfold tailWord_6877430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677529967140822273543359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167226986316168770917795829 15677529967140822273543359)
  ·
    refine ⟨23516294950711233410315039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15677529967140822273543359 23516294950711233410315039)
    ·
      refine ⟨35274442426066850115472559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23516294950711233410315039 35274442426066850115472559)
      ·
        refine ⟨52911663639100275173208839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35274442426066850115472559 52911663639100275173208839)
        ·
          refine ⟨79367495458650412759813259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52911663639100275173208839 79367495458650412759813259)
          ·
            refine ⟨119051243187975619139719889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79367495458650412759813259 119051243187975619139719889)
            ·
              refine ⟨89288432390981714354789917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119051243187975619139719889 89288432390981714354789917)
              ·
                refine ⟨33483162146618142883046219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89288432390981714354789917 33483162146618142883046219)
                ·
                  refine ⟨50224743219927214324569329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33483162146618142883046219 50224743219927214324569329)
                  ·
                    refine ⟨37668557414945410743426997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50224743219927214324569329 37668557414945410743426997)
                    ·
                      refine ⟨3531427257651132257196281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37668557414945410743426997 3531427257651132257196281)
                      ·
                        rfl

theorem cell23_6877430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6877430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877430 prefixEnd_6877430 := by exact prefixLift 6877430
  have htrace : WordTrace (prefixWord ++ tailWord_6877430) baseStart_6877430 baseEnd_6877430 := by
    simpa [prefixWord, tailWord_6877430, baseEnd_6877430] using wordTrace_append hprefix tailTrace_6877430
  have hstable : (prefixWord ++ tailWord_6877430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877430).length < 2 ^ (prefixWord ++ tailWord_6877430).sum := by decide
  have hdescent : baseEnd_6877430 < baseStart_6877430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877497 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 6]
def baseStart_6877497 : Nat := 118140960795 + 6877497 * 2 ^ 59
def prefixEnd_6877497 : Nat := 4983230072969 + 3 ^ 40 * 6877497 * 2
def baseEnd_6877497 : Nat := 392384628983887055006497

theorem tailTrace_6877497 : CollatzResearch.WordTrace tailWord_6877497 prefixEnd_6877497 392384628983887055006497 := by
  unfold tailWord_6877497
  simp only [CollatzResearch.WordTrace]
  refine ⟨250842923165010426819382745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167228615443340284546255163 250842923165010426819382745)
  ·
    refine ⟨188132192373757820114537059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250842923165010426819382745 188132192373757820114537059)
    ·
      refine ⟨282198288560636730171805589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188132192373757820114537059 282198288560636730171805589)
      ·
        refine ⟨13228044776279846726803387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 282198288560636730171805589 13228044776279846726803387)
        ·
          refine ⟨19842067164419770090205081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13228044776279846726803387 19842067164419770090205081)
          ·
            refine ⟨14881550373314827567653811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19842067164419770090205081 14881550373314827567653811)
            ·
              refine ⟨22322325559972241351480717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881550373314827567653811 22322325559972241351480717)
              ·
                refine ⟨8370872084989590506805269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22322325559972241351480717 8370872084989590506805269)
                ·
                  refine ⟨392384628983887055006497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8370872084989590506805269 392384628983887055006497)
                  ·
                    rfl

theorem cell23_6877497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_6877497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877497 prefixEnd_6877497 := by exact prefixLift 6877497
  have htrace : WordTrace (prefixWord ++ tailWord_6877497) baseStart_6877497 baseEnd_6877497 := by
    simpa [prefixWord, tailWord_6877497, baseEnd_6877497] using wordTrace_append hprefix tailTrace_6877497
  have hstable : (prefixWord ++ tailWord_6877497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877497).length < 2 ^ (prefixWord ++ tailWord_6877497).sum := by decide
  have hdescent : baseEnd_6877497 < baseStart_6877497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877507 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 3]
def baseStart_6877507 : Nat := 118140960795 + 6877507 * 2 ^ 59
def prefixEnd_6877507 : Nat := 4983230072969 + 3 ^ 40 * 6877507 * 2
def baseEnd_6877507 : Nat := 3531466795661528455933427

theorem tailTrace_6877507 : CollatzResearch.WordTrace tailWord_6877507 prefixEnd_6877507 3531466795661528455933427 := by
  unfold tailWord_6877507
  simp only [CollatzResearch.WordTrace]
  refine ⟨250843287894974198527246775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167228858596649465684831183 250843287894974198527246775)
  ·
    refine ⟨376264931842461297790870163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250843287894974198527246775 376264931842461297790870163)
    ·
      refine ⟨564397397763691946686305245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376264931842461297790870163 564397397763691946686305245)
      ·
        refine ⟨211649024161384480007364467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564397397763691946686305245 211649024161384480007364467)
        ·
          refine ⟨317473536242076720011046701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211649024161384480007364467 317473536242076720011046701)
          ·
            refine ⟨119052576090778770004142513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317473536242076720011046701 119052576090778770004142513)
            ·
              refine ⟨89289432068084077503106885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119052576090778770004142513 89289432068084077503106885)
              ·
                refine ⟨16741768512765764531832541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89289432068084077503106885 16741768512765764531832541)
                ·
                  refine ⟨6278163192287161699437203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16741768512765764531832541 6278163192287161699437203)
                  ·
                    refine ⟨9417244788430742549155805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278163192287161699437203 9417244788430742549155805)
                    ·
                      refine ⟨3531466795661528455933427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9417244788430742549155805 3531466795661528455933427)
                      ·
                        rfl

theorem cell23_6877507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_6877507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877507 prefixEnd_6877507 := by exact prefixLift 6877507
  have htrace : WordTrace (prefixWord ++ tailWord_6877507) baseStart_6877507 baseEnd_6877507 := by
    simpa [prefixWord, tailWord_6877507, baseEnd_6877507] using wordTrace_append hprefix tailTrace_6877507
  have hstable : (prefixWord ++ tailWord_6877507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877507).length < 2 ^ (prefixWord ++ tailWord_6877507).sum := by decide
  have hdescent : baseEnd_6877507 < baseStart_6877507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877540 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_6877540 : Nat := 118140960795 + 6877540 * 2 ^ 59
def prefixEnd_6877540 : Nat := 4983230072969 + 3 ^ 40 * 6877540 * 2
def baseEnd_6877540 : Nat := 1177161246841042275606925

theorem tailTrace_6877540 : CollatzResearch.WordTrace tailWord_6877540 prefixEnd_6877540 1177161246841042275606925 := by
  unfold tailWord_6877540
  simp only [CollatzResearch.WordTrace]
  refine ⟨125422245751927322581599037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167229661002569763442132049 125422245751927322581599037)
  ·
    refine ⟨47033342156972745968099639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125422245751927322581599037 47033342156972745968099639)
    ·
      refine ⟨70550013235459118952149459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47033342156972745968099639 70550013235459118952149459)
      ·
        refine ⟨105825019853188678428224189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70550013235459118952149459 105825019853188678428224189)
        ·
          refine ⟨39684382444945754410584071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105825019853188678428224189 39684382444945754410584071)
          ·
            refine ⟨59526573667418631615876107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39684382444945754410584071 59526573667418631615876107)
            ·
              refine ⟨89289860501127947423814161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59526573667418631615876107 89289860501127947423814161)
              ·
                refine ⟨66967395375845960567860621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89289860501127947423814161 66967395375845960567860621)
                ·
                  refine ⟨25112773265942235212947733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66967395375845960567860621 25112773265942235212947733)
                  ·
                    refine ⟨1177161246841042275606925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25112773265942235212947733 1177161246841042275606925)
                    ·
                      rfl

theorem cell23_6877540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_6877540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877540 prefixEnd_6877540 := by exact prefixLift 6877540
  have htrace : WordTrace (prefixWord ++ tailWord_6877540) baseStart_6877540 baseEnd_6877540 := by
    simpa [prefixWord, tailWord_6877540, baseEnd_6877540] using wordTrace_append hprefix tailTrace_6877540
  have hstable : (prefixWord ++ tailWord_6877540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877540).length < 2 ^ (prefixWord ++ tailWord_6877540).sum := by decide
  have hdescent : baseEnd_6877540 < baseStart_6877540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877541 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 1, 1, 3]
def baseStart_6877541 : Nat := 118140960795 + 6877541 * 2 ^ 59
def prefixEnd_6877541 : Nat := 4983230072969 + 3 ^ 40 * 6877541 * 2
def baseEnd_6877541 : Nat := 3531484254003781322908271

theorem tailTrace_6877541 : CollatzResearch.WordTrace tailWord_6877541 prefixEnd_6877541 3531484254003781322908271 := by
  unfold tailWord_6877541
  simp only [CollatzResearch.WordTrace]
  refine ⟨250844527976851022333984477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167229685317900681555989651 250844527976851022333984477)
  ·
    refine ⟨94066697991319133375244179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250844527976851022333984477 94066697991319133375244179)
    ·
      refine ⟨141100046986978700062866269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94066697991319133375244179 141100046986978700062866269)
      ·
        refine ⟨52912517620117012523574851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141100046986978700062866269 52912517620117012523574851)
        ·
          refine ⟨79368776430175518785362277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52912517620117012523574851 79368776430175518785362277)
          ·
            refine ⟨14881645580657909772255427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79368776430175518785362277 14881645580657909772255427)
            ·
              refine ⟨22322468370986864658383141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881645580657909772255427 22322468370986864658383141)
              ·
                refine ⟨4185462819560037123446839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22322468370986864658383141 4185462819560037123446839)
                ·
                  refine ⟨6278194229340055685170259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185462819560037123446839 6278194229340055685170259)
                  ·
                    refine ⟨9417291344010083527755389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278194229340055685170259 9417291344010083527755389)
                    ·
                      refine ⟨3531484254003781322908271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9417291344010083527755389 3531484254003781322908271)
                      ·
                        rfl

theorem cell23_6877541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_6877541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877541 prefixEnd_6877541 := by exact prefixLift 6877541
  have htrace : WordTrace (prefixWord ++ tailWord_6877541) baseStart_6877541 baseEnd_6877541 := by
    simpa [prefixWord, tailWord_6877541, baseEnd_6877541] using wordTrace_append hprefix tailTrace_6877541
  have hstable : (prefixWord ++ tailWord_6877541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877541).length < 2 ^ (prefixWord ++ tailWord_6877541).sum := by decide
  have hdescent : baseEnd_6877541 < baseStart_6877541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877557 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6877557 : Nat := 118140960795 + 6877557 * 2 ^ 59
def prefixEnd_6877557 : Nat := 4983230072969 + 3 ^ 40 * 6877557 * 2
def baseEnd_6877557 : Nat := 1177164156564751086769399

theorem tailTrace_6877557 : CollatzResearch.WordTrace tailWord_6877557 prefixEnd_6877557 1177164156564751086769399 := by
  unfold tailWord_6877557
  simp only [CollatzResearch.WordTrace]
  refine ⟨250845111544793057066566925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167230074363195371377711283 250845111544793057066566925)
  ·
    refine ⟨94066916829297396399962597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250845111544793057066566925 94066916829297396399962597)
    ·
      refine ⟨17637546905493261824992987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94066916829297396399962597 17637546905493261824992987)
      ·
        refine ⟨26456320358239892737489481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17637546905493261824992987 26456320358239892737489481)
        ·
          refine ⟨19842240268679919553117111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26456320358239892737489481 19842240268679919553117111)
          ·
            refine ⟨29763360403019879329675667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19842240268679919553117111 29763360403019879329675667)
            ·
              refine ⟨44645040604529818994513501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29763360403019879329675667 44645040604529818994513501)
              ·
                refine ⟨16741890226698682122942563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44645040604529818994513501 16741890226698682122942563)
                ·
                  refine ⟨25112835340048023184413845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16741890226698682122942563 25112835340048023184413845)
                  ·
                    refine ⟨1177164156564751086769399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25112835340048023184413845 1177164156564751086769399)
                    ·
                      rfl

theorem cell23_6877557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6877557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877557 prefixEnd_6877557 := by exact prefixLift 6877557
  have htrace : WordTrace (prefixWord ++ tailWord_6877557) baseStart_6877557 baseEnd_6877557 := by
    simpa [prefixWord, tailWord_6877557, baseEnd_6877557] using wordTrace_append hprefix tailTrace_6877557
  have hstable : (prefixWord ++ tailWord_6877557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877557).length < 2 ^ (prefixWord ++ tailWord_6877557).sum := by decide
  have hdescent : baseEnd_6877557 < baseStart_6877557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877558 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6877558 : Nat := 118140960795 + 6877558 * 2 ^ 59
def prefixEnd_6877558 : Nat := 4983230072969 + 3 ^ 40 * 6877558 * 2
def baseEnd_6877558 : Nat := 3531492983174907756395693

theorem tailTrace_6877558 : CollatzResearch.WordTrace tailWord_6877558 prefixEnd_6877558 3531492983174907756395693 := by
  unfold tailWord_6877558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677821751111839639834583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167230098678526289491568885 15677821751111839639834583)
  ·
    refine ⟨23516732626667759459751875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15677821751111839639834583 23516732626667759459751875)
    ·
      refine ⟨35275098940001639189627813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23516732626667759459751875 35275098940001639189627813)
      ·
        refine ⟨6614081051250307348055215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35275098940001639189627813 6614081051250307348055215)
        ·
          refine ⟨9921121576875461022082823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614081051250307348055215 9921121576875461022082823)
          ·
            refine ⟨14881682365313191533124235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921121576875461022082823 14881682365313191533124235)
            ·
              refine ⟨22322523547969787299686353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14881682365313191533124235 22322523547969787299686353)
              ·
                refine ⟨16741892660977340474764765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22322523547969787299686353 16741892660977340474764765)
                ·
                  refine ⟨6278209747866502678036787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16741892660977340474764765 6278209747866502678036787)
                  ·
                    refine ⟨9417314621799754017055181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278209747866502678036787 9417314621799754017055181)
                    ·
                      refine ⟨3531492983174907756395693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9417314621799754017055181 3531492983174907756395693)
                      ·
                        rfl

theorem cell23_6877558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6877558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877558 prefixEnd_6877558 := by exact prefixLift 6877558
  have htrace : WordTrace (prefixWord ++ tailWord_6877558) baseStart_6877558 baseEnd_6877558 := by
    simpa [prefixWord, tailWord_6877558, baseEnd_6877558] using wordTrace_append hprefix tailTrace_6877558
  have hstable : (prefixWord ++ tailWord_6877558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877558).length < 2 ^ (prefixWord ++ tailWord_6877558).sum := by decide
  have hdescent : baseEnd_6877558 < baseStart_6877558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877577 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_6877577 : Nat := 118140960795 + 6877577 * 2 ^ 59
def prefixEnd_6877577 : Nat := 4983230072969 + 3 ^ 40 * 6877577 * 2
def baseEnd_6877577 : Nat := 3531502739307343182058105

theorem tailTrace_6877577 : CollatzResearch.WordTrace tailWord_6877577 prefixEnd_6877577 3531502739307343182058105 := by
  unfold tailWord_6877577
  simp only [CollatzResearch.WordTrace]
  refine ⟨250845841004720600482294985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167230560669813733654863323 250845841004720600482294985)
  ·
    refine ⟨188134380753540450361721239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250845841004720600482294985 188134380753540450361721239)
    ·
      refine ⟨282201571130310675542581859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188134380753540450361721239 282201571130310675542581859)
      ·
        refine ⟨423302356695466013313872789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282201571130310675542581859 423302356695466013313872789)
        ·
          refine ⟨19842297970099969374087787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 423302356695466013313872789 19842297970099969374087787)
          ·
            refine ⟨29763446955149954061131681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19842297970099969374087787 29763446955149954061131681)
            ·
              refine ⟨22322585216362465545848761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29763446955149954061131681 22322585216362465545848761)
              ·
                refine ⟨16741938912271849159386571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22322585216362465545848761 16741938912271849159386571)
                ·
                  refine ⟨25112908368407773739079857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16741938912271849159386571 25112908368407773739079857)
                  ·
                    refine ⟨18834681276305830304309893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25112908368407773739079857 18834681276305830304309893)
                    ·
                      refine ⟨3531502739307343182058105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18834681276305830304309893 3531502739307343182058105)
                      ·
                        rfl

theorem cell23_6877577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_6877577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877577 prefixEnd_6877577 := by exact prefixLift 6877577
  have htrace : WordTrace (prefixWord ++ tailWord_6877577) baseStart_6877577 baseEnd_6877577 := by
    simpa [prefixWord, tailWord_6877577, baseEnd_6877577] using wordTrace_append hprefix tailTrace_6877577
  have hstable : (prefixWord ++ tailWord_6877577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877577).length < 2 ^ (prefixWord ++ tailWord_6877577).sum := by decide
  have hdescent : baseEnd_6877577 < baseStart_6877577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877578 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_6877578 : Nat := 118140960795 + 6877578 * 2 ^ 59
def prefixEnd_6877578 : Nat := 4983230072969 + 3 ^ 40 * 6877578 * 2
def baseEnd_6877578 : Nat := 1177167750929332559381867

theorem tailTrace_6877578 : CollatzResearch.WordTrace tailWord_6877578 prefixEnd_6877578 1177167750929332559381867 := by
  unfold tailWord_6877578
  simp only [CollatzResearch.WordTrace]
  refine ⟨62711469369429244413270347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167230584985144651768720925 62711469369429244413270347)
  ·
    refine ⟨94067204054143866619905521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62711469369429244413270347 94067204054143866619905521)
    ·
      refine ⟨70550403040607899964929141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94067204054143866619905521 70550403040607899964929141)
      ·
        refine ⟨6614100285056990621712107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70550403040607899964929141 6614100285056990621712107)
        ·
          refine ⟨9921150427585485932568161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614100285056990621712107 9921150427585485932568161)
          ·
            refine ⟨7440862820689114449426121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9921150427585485932568161 7440862820689114449426121)
            ·
              refine ⟨5580647115516835837069591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7440862820689114449426121 5580647115516835837069591)
              ·
                refine ⟨8370970673275253755604387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580647115516835837069591 8370970673275253755604387)
                ·
                  refine ⟨12556456009912880633406581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370970673275253755604387 12556456009912880633406581)
                  ·
                    refine ⟨1177167750929332559381867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12556456009912880633406581 1177167750929332559381867)
                    ·
                      rfl

theorem cell23_6877578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_6877578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877578 prefixEnd_6877578 := by exact prefixLift 6877578
  have htrace : WordTrace (prefixWord ++ tailWord_6877578) baseStart_6877578 baseEnd_6877578 := by
    simpa [prefixWord, tailWord_6877578, baseEnd_6877578] using wordTrace_append hprefix tailTrace_6877578
  have hstable : (prefixWord ++ tailWord_6877578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877578).length < 2 ^ (prefixWord ++ tailWord_6877578).sum := by decide
  have hdescent : baseEnd_6877578 < baseStart_6877578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877598 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6877598 : Nat := 118140960795 + 6877598 * 2 ^ 59
def prefixEnd_6877598 : Nat := 4983230072969 + 3 ^ 40 * 6877598 * 2
def baseEnd_6877598 : Nat := 3531513522401087599895509

theorem tailTrace_6877598 : CollatzResearch.WordTrace tailWord_6877598 prefixEnd_6877598 3531513522401087599895509 := by
  unfold tailWord_6877598
  simp only [CollatzResearch.WordTrace]
  refine ⟨31355825867205565133601181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167231071291763014045872965 31355825867205565133601181)
  ·
    refine ⟨11758434700202086925100443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31355825867205565133601181 11758434700202086925100443)
    ·
      refine ⟨17637652050303130387650665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11758434700202086925100443 17637652050303130387650665)
      ·
        refine ⟨13228239037727347790737999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17637652050303130387650665 13228239037727347790737999)
        ·
          refine ⟨19842358556591021686106999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13228239037727347790737999 19842358556591021686106999)
          ·
            refine ⟨29763537834886532529160499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19842358556591021686106999 29763537834886532529160499)
            ·
              refine ⟨44645306752329798793740749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29763537834886532529160499 44645306752329798793740749)
              ·
                refine ⟨16741990032123674547652781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44645306752329798793740749 16741990032123674547652781)
                ·
                  refine ⟨6278246262046377955369793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16741990032123674547652781 6278246262046377955369793)
                  ·
                    refine ⟨4708684696534783466527345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278246262046377955369793 4708684696534783466527345)
                    ·
                      refine ⟨3531513522401087599895509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708684696534783466527345 3531513522401087599895509)
                      ·
                        rfl

theorem cell23_6877598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6877598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877598 prefixEnd_6877598 := by exact prefixLift 6877598
  have htrace : WordTrace (prefixWord ++ tailWord_6877598) baseStart_6877598 baseEnd_6877598 := by
    simpa [prefixWord, tailWord_6877598, baseEnd_6877598] using wordTrace_append hprefix tailTrace_6877598
  have hstable : (prefixWord ++ tailWord_6877598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877598).length < 2 ^ (prefixWord ++ tailWord_6877598).sum := by decide
  have hdescent : baseEnd_6877598 < baseStart_6877598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877608 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6877608 : Nat := 118140960795 + 6877608 * 2 ^ 59
def prefixEnd_6877608 : Nat := 4983230072969 + 3 ^ 40 * 6877608 * 2
def baseEnd_6877608 : Nat := 1177172885735877520256821

theorem tailTrace_6877608 : CollatzResearch.WordTrace tailWord_6877608 prefixEnd_6877608 1177172885735877520256821 := by
  unfold tailWord_6877608
  simp only [CollatzResearch.WordTrace]
  refine ⟨125423485833804146388336739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167231314445072195184448985 125423485833804146388336739)
  ·
    refine ⟨188135228750706219582505109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125423485833804146388336739 188135228750706219582505109)
    ·
      refine ⟨8818838847689354042929927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188135228750706219582505109 8818838847689354042929927)
      ·
        refine ⟨13228258271534031064394891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818838847689354042929927 13228258271534031064394891)
        ·
          refine ⟨19842387407301046596592337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13228258271534031064394891 19842387407301046596592337)
          ·
            refine ⟨14881790555475784947444253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19842387407301046596592337 14881790555475784947444253)
            ·
              refine ⟨5580671458303419355291595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14881790555475784947444253 5580671458303419355291595)
              ·
                refine ⟨8371007187455129032937393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580671458303419355291595 8371007187455129032937393)
                ·
                  refine ⟨6278255390591346774703045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8371007187455129032937393 6278255390591346774703045)
                  ·
                    refine ⟨1177172885735877520256821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6278255390591346774703045 1177172885735877520256821)
                    ·
                      rfl

theorem cell23_6877608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6877608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877608 prefixEnd_6877608 := by exact prefixLift 6877608
  have htrace : WordTrace (prefixWord ++ tailWord_6877608) baseStart_6877608 baseEnd_6877608 := by
    simpa [prefixWord, tailWord_6877608, baseEnd_6877608] using wordTrace_append hprefix tailTrace_6877608
  have hstable : (prefixWord ++ tailWord_6877608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877608).length < 2 ^ (prefixWord ++ tailWord_6877608).sum := by decide
  have hdescent : baseEnd_6877608 < baseStart_6877608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877621 : List Nat := [1, 3, 3, 2, 4, 1, 2, 7]
def baseStart_6877621 : Nat := 118140960795 + 6877621 * 2 ^ 59
def prefixEnd_6877621 : Nat := 4983230072969 + 3 ^ 40 * 6877621 * 2
def baseEnd_6877621 : Nat := 130797234535412629996589

theorem tailTrace_6877621 : CollatzResearch.WordTrace tailWord_6877621 prefixEnd_6877621 130797234535412629996589 := by
  unfold tailWord_6877621
  simp only [CollatzResearch.WordTrace]
  refine ⟨250847445816561195996896717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167231630544374130664597811 250847445816561195996896717)
  ·
    refine ⟨94067792181210448498836269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250847445816561195996896717 94067792181210448498836269)
    ·
      refine ⟨35275422067953918187063601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94067792181210448498836269 35275422067953918187063601)
      ·
        refine ⟨26456566550965438640297701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35275422067953918187063601 26456566550965438640297701)
        ·
          refine ⟨4960606228306019745055819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26456566550965438640297701 4960606228306019745055819)
          ·
            refine ⟨7440909342459029617583729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960606228306019745055819 7440909342459029617583729)
            ·
              refine ⟨5580682006844272213187797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7440909342459029617583729 5580682006844272213187797)
              ·
                refine ⟨130797234535412629996589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5580682006844272213187797 130797234535412629996589)
                ·
                  rfl

theorem cell23_6877621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 7].length) (baseStart_6877621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877621 prefixEnd_6877621 := by exact prefixLift 6877621
  have htrace : WordTrace (prefixWord ++ tailWord_6877621) baseStart_6877621 baseEnd_6877621 := by
    simpa [prefixWord, tailWord_6877621, baseEnd_6877621] using wordTrace_append hprefix tailTrace_6877621
  have hstable : (prefixWord ++ tailWord_6877621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877621).length < 2 ^ (prefixWord ++ tailWord_6877621).sum := by decide
  have hdescent : baseEnd_6877621 < baseStart_6877621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877654 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6877654 : Nat := 118140960795 + 6877654 * 2 ^ 59
def prefixEnd_6877654 : Nat := 4983230072969 + 3 ^ 40 * 6877654 * 2
def baseEnd_6877654 : Nat := 3531542277317739380795251

theorem tailTrace_6877654 : CollatzResearch.WordTrace tailWord_6877654 prefixEnd_6877654 3531542277317739380795251 := by
  unfold tailWord_6877654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678040589090102664553001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167232432950294428421898677 15678040589090102664553001)
  ·
    refine ⟨11758530441817576998414751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15678040589090102664553001 11758530441817576998414751)
    ·
      refine ⟨17637795662726365497622127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11758530441817576998414751 17637795662726365497622127)
      ·
        refine ⟨26456693494089548246433191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17637795662726365497622127 26456693494089548246433191)
        ·
          refine ⟨39685040241134322369649787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26456693494089548246433191 39685040241134322369649787)
          ·
            refine ⟨59527560361701483554474681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39685040241134322369649787 59527560361701483554474681)
            ·
              refine ⟨44645670271276112665856011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59527560361701483554474681 44645670271276112665856011)
              ·
                refine ⟨66968505406914168998784017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44645670271276112665856011 66968505406914168998784017)
                ·
                  refine ⟨50226379055185626749088013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66968505406914168998784017 50226379055185626749088013)
                  ·
                    refine ⟨18834892145694610030908005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50226379055185626749088013 18834892145694610030908005)
                    ·
                      refine ⟨3531542277317739380795251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18834892145694610030908005 3531542277317739380795251)
                      ·
                        rfl

theorem cell23_6877654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6877654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877654 prefixEnd_6877654 := by exact prefixLift 6877654
  have htrace : WordTrace (prefixWord ++ tailWord_6877654) baseStart_6877654 baseEnd_6877654 := by
    simpa [prefixWord, tailWord_6877654, baseEnd_6877654] using wordTrace_append hprefix tailTrace_6877654
  have hstable : (prefixWord ++ tailWord_6877654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877654).length < 2 ^ (prefixWord ++ tailWord_6877654).sum := by decide
  have hdescent : baseEnd_6877654 < baseStart_6877654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877657 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_6877657 : Nat := 118140960795 + 6877657 * 2 ^ 59
def prefixEnd_6877657 : Nat := 4983230072969 + 3 ^ 40 * 6877657 * 2
def baseEnd_6877657 : Nat := 3531543817759702869057737

theorem tailTrace_6877657 : CollatzResearch.WordTrace tailWord_6877657 prefixEnd_6877657 3531543817759702869057737 := by
  unfold tailWord_6877657
  simp only [CollatzResearch.WordTrace]
  refine ⟨250848758844430774145207225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167232505896287182763471483 250848758844430774145207225)
  ·
    refine ⟨188136569133323080608905419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250848758844430774145207225 188136569133323080608905419)
    ·
      refine ⟨282204853699984620913358129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188136569133323080608905419 282204853699984620913358129)
      ·
        refine ⟨211653640274988465685018597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282204853699984620913358129 211653640274988465685018597)
        ·
          refine ⟨39685057551560337315940987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211653640274988465685018597 39685057551560337315940987)
          ·
            refine ⟨59527586327340505973911481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39685057551560337315940987 59527586327340505973911481)
            ·
              refine ⟨44645689745505379480433611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59527586327340505973911481 44645689745505379480433611)
              ·
                refine ⟨66968534618258069220650417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44645689745505379480433611 66968534618258069220650417)
                ·
                  refine ⟨50226400963693551915487813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66968534618258069220650417 50226400963693551915487813)
                  ·
                    refine ⟨9417450180692540984153965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50226400963693551915487813 9417450180692540984153965)
                    ·
                      refine ⟨3531543817759702869057737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9417450180692540984153965 3531543817759702869057737)
                      ·
                        rfl

theorem cell23_6877657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_6877657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877657 prefixEnd_6877657 := by exact prefixLift 6877657
  have htrace : WordTrace (prefixWord ++ tailWord_6877657) baseStart_6877657 baseEnd_6877657 := by
    simpa [prefixWord, tailWord_6877657, baseEnd_6877657] using wordTrace_append hprefix tailTrace_6877657
  have hstable : (prefixWord ++ tailWord_6877657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877657).length < 2 ^ (prefixWord ++ tailWord_6877657).sum := by decide
  have hdescent : baseEnd_6877657 < baseStart_6877657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877717 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6877717 : Nat := 118140960795 + 6877717 * 2 ^ 59
def prefixEnd_6877717 : Nat := 4983230072969 + 3 ^ 40 * 6877717 * 2
def baseEnd_6877717 : Nat := 3531574626598972634307461

theorem tailTrace_6877717 : CollatzResearch.WordTrace tailWord_6877717 prefixEnd_6877717 3531574626598972634307461 := by
  unfold tailWord_6877717
  simp only [CollatzResearch.WordTrace]
  refine ⟨250850947224213404392391405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167233964816142269594927603 250850947224213404392391405)
  ·
    refine ⟨94069105209080026647146777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250850947224213404392391405 94069105209080026647146777)
    ·
      refine ⟨70551828906810019985360083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94069105209080026647146777 70551828906810019985360083)
      ·
        refine ⟨105827743360215029978040125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70551828906810019985360083 105827743360215029978040125)
        ·
          refine ⟨39685403760080636241765047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105827743360215029978040125 39685403760080636241765047)
          ·
            refine ⟨59528105640120954362647571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39685403760080636241765047 59528105640120954362647571)
            ·
              refine ⟨89292158460181431543971357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59528105640120954362647571 89292158460181431543971357)
              ·
                refine ⟨33484559422568036828989259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89292158460181431543971357 33484559422568036828989259)
                ·
                  refine ⟨50226839133852055243483889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33484559422568036828989259 50226839133852055243483889)
                  ·
                    refine ⟨37670129350389041432612917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50226839133852055243483889 37670129350389041432612917)
                    ·
                      refine ⟨3531574626598972634307461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37670129350389041432612917 3531574626598972634307461)
                      ·
                        rfl

theorem cell23_6877717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6877717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877717 prefixEnd_6877717 := by exact prefixLift 6877717
  have htrace : WordTrace (prefixWord ++ tailWord_6877717) baseStart_6877717 baseEnd_6877717 := by
    simpa [prefixWord, tailWord_6877717, baseEnd_6877717] using wordTrace_append hprefix tailTrace_6877717
  have hstable : (prefixWord ++ tailWord_6877717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877717).length < 2 ^ (prefixWord ++ tailWord_6877717).sum := by decide
  have hdescent : baseEnd_6877717 < baseStart_6877717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877727 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_6877727 : Nat := 118140960795 + 6877727 * 2 ^ 59
def prefixEnd_6877727 : Nat := 4983230072969 + 3 ^ 40 * 6877727 * 2
def baseEnd_6877727 : Nat := 3531579761405517595182415

theorem tailTrace_6877727 : CollatzResearch.WordTrace tailWord_6877727 prefixEnd_6877727 3531579761405517595182415 := by
  unfold tailWord_6877727
  simp only [CollatzResearch.WordTrace]
  refine ⟨250851311954177176100255435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167234207969451450733503623 250851311954177176100255435)
  ·
    refine ⟨376276967931265764150383153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250851311954177176100255435 376276967931265764150383153)
    ·
      refine ⟨282207725948449323112787365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376276967931265764150383153 282207725948449323112787365)
      ·
        refine ⟨52913948615334248083647631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282207725948449323112787365 52913948615334248083647631)
        ·
          refine ⟨79370922923001372125471447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52913948615334248083647631 79370922923001372125471447)
          ·
            refine ⟨119056384384502058188207171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79370922923001372125471447 119056384384502058188207171)
            ·
              refine ⟨178584576576753087282310757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119056384384502058188207171 178584576576753087282310757)
              ·
                refine ⟨33484608108141203865433267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178584576576753087282310757 33484608108141203865433267)
                ·
                  refine ⟨50226912162211805798149901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33484608108141203865433267 50226912162211805798149901)
                  ·
                    refine ⟨18835092060829427174306213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50226912162211805798149901 18835092060829427174306213)
                    ·
                      refine ⟨3531579761405517595182415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18835092060829427174306213 3531579761405517595182415)
                      ·
                        rfl

theorem cell23_6877727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_6877727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877727 prefixEnd_6877727 := by exact prefixLift 6877727
  have htrace : WordTrace (prefixWord ++ tailWord_6877727) baseStart_6877727 baseEnd_6877727 := by
    simpa [prefixWord, tailWord_6877727, baseEnd_6877727] using wordTrace_append hprefix tailTrace_6877727
  have hstable : (prefixWord ++ tailWord_6877727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877727).length < 2 ^ (prefixWord ++ tailWord_6877727).sum := by decide
  have hdescent : baseEnd_6877727 < baseStart_6877727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877744 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_6877744 : Nat := 118140960795 + 6877744 * 2 ^ 59
def prefixEnd_6877744 : Nat := 4983230072969 + 3 ^ 40 * 6877744 * 2
def baseEnd_6877744 : Nat := 3531588490576644028669837

theorem tailTrace_6877744 : CollatzResearch.WordTrace tailWord_6877744 prefixEnd_6877744 3531588490576644028669837 := by
  unfold tailWord_6877744
  simp only [CollatzResearch.WordTrace]
  refine ⟨125425965997557794001812143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167234621330077058669082857 125425965997557794001812143)
  ·
    refine ⟨188138948996336691002718215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125425965997557794001812143 188138948996336691002718215)
    ·
      refine ⟨282208423494505036504077323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188138948996336691002718215 282208423494505036504077323)
      ·
        refine ⟨423312635241757554756115985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282208423494505036504077323 423312635241757554756115985)
        ·
          refine ⟨317484476431318166067086989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423312635241757554756115985 317484476431318166067086989)
          ·
            refine ⟨119056678661744312275157621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317484476431318166067086989 119056678661744312275157621)
            ·
              refine ⟨11161563624538529275796027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119056678661744312275157621 11161563624538529275796027)
              ·
                refine ⟨16742345436807793913694041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161563624538529275796027 16742345436807793913694041)
                ·
                  refine ⟨12556759077605845435270531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16742345436807793913694041 12556759077605845435270531)
                  ·
                    refine ⟨18835138616408768152905797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12556759077605845435270531 18835138616408768152905797)
                    ·
                      refine ⟨3531588490576644028669837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18835138616408768152905797 3531588490576644028669837)
                      ·
                        rfl

theorem cell23_6877744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_6877744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877744 prefixEnd_6877744 := by exact prefixLift 6877744
  have htrace : WordTrace (prefixWord ++ tailWord_6877744) baseStart_6877744 baseEnd_6877744 := by
    simpa [prefixWord, tailWord_6877744, baseEnd_6877744] using wordTrace_append hprefix tailTrace_6877744
  have hstable : (prefixWord ++ tailWord_6877744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877744).length < 2 ^ (prefixWord ++ tailWord_6877744).sum := by decide
  have hdescent : baseEnd_6877744 < baseStart_6877744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877761 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_6877761 : Nat := 118140960795 + 6877761 * 2 ^ 59
def prefixEnd_6877761 : Nat := 4983230072969 + 3 ^ 40 * 6877761 * 2
def baseEnd_6877761 : Nat := 3531597219747770462157259

theorem tailTrace_6877761 : CollatzResearch.WordTrace tailWord_6877761 prefixEnd_6877761 3531597219747770462157259 := by
  unfold tailWord_6877761
  simp only [CollatzResearch.WordTrace]
  refine ⟨250852552036053999906993137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167235034690702666604662091 250852552036053999906993137)
  ·
    refine ⟨188139414027040499930244853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250852552036053999906993137 188139414027040499930244853)
    ·
      refine ⟨17638070065035046868460455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188139414027040499930244853 17638070065035046868460455)
      ·
        refine ⟨26457105097552570302690683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17638070065035046868460455 26457105097552570302690683)
        ·
          refine ⟨39685657646328855454036025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26457105097552570302690683 39685657646328855454036025)
          ·
            refine ⟨29764243234746641590527019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39685657646328855454036025 29764243234746641590527019)
            ·
              refine ⟨44646364852119962385790529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29764243234746641590527019 44646364852119962385790529)
              ·
                refine ⟨33484773639089971789342897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44646364852119962385790529 33484773639089971789342897)
                ·
                  refine ⟨25113580229317478842007173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33484773639089971789342897 25113580229317478842007173)
                  ·
                    refine ⟨4708796292997027282876345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25113580229317478842007173 4708796292997027282876345)
                    ·
                      refine ⟨3531597219747770462157259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708796292997027282876345 3531597219747770462157259)
                      ·
                        rfl

theorem cell23_6877761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_6877761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877761 prefixEnd_6877761 := by exact prefixLift 6877761
  have htrace : WordTrace (prefixWord ++ tailWord_6877761) baseStart_6877761 baseEnd_6877761 := by
    simpa [prefixWord, tailWord_6877761, baseEnd_6877761] using wordTrace_append hprefix tailTrace_6877761
  have hstable : (prefixWord ++ tailWord_6877761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877761).length < 2 ^ (prefixWord ++ tailWord_6877761).sum := by decide
  have hdescent : baseEnd_6877761 < baseStart_6877761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877771 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 1, 4]
def baseStart_6877771 : Nat := 118140960795 + 6877771 * 2 ^ 59
def prefixEnd_6877771 : Nat := 4983230072969 + 3 ^ 40 * 6877771 * 2
def baseEnd_6877771 : Nat := 1177200784851438474344071

theorem tailTrace_6877771 : CollatzResearch.WordTrace tailWord_6877771 prefixEnd_6877771 1177200784851438474344071 := by
  unfold tailWord_6877771
  simp only [CollatzResearch.WordTrace]
  refine ⟨250852916766017771614857167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167235277844011847743238111 250852916766017771614857167)
  ·
    refine ⟨376279375149026657422285751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250852916766017771614857167 376279375149026657422285751)
    ·
      refine ⟨564419062723539986133428627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376279375149026657422285751 564419062723539986133428627)
      ·
        refine ⟨846628594085309979200142941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564419062723539986133428627 846628594085309979200142941)
        ·
          refine ⟨317485722781991242200053603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 846628594085309979200142941 317485722781991242200053603)
          ·
            refine ⟨476228584172986863300080405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317485722781991242200053603 476228584172986863300080405)
            ·
              refine ⟨22323214883108759217191269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 476228584172986863300080405 22323214883108759217191269)
              ·
                refine ⟨4185602790582892353223363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22323214883108759217191269 4185602790582892353223363)
                ·
                  refine ⟨6278404185874338529835045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185602790582892353223363 6278404185874338529835045)
                  ·
                    refine ⟨1177200784851438474344071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6278404185874338529835045 1177200784851438474344071)
                    ·
                      rfl

theorem cell23_6877771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 4].length) (baseStart_6877771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877771 prefixEnd_6877771 := by exact prefixLift 6877771
  have htrace : WordTrace (prefixWord ++ tailWord_6877771) baseStart_6877771 baseEnd_6877771 := by
    simpa [prefixWord, tailWord_6877771, baseEnd_6877771] using wordTrace_append hprefix tailTrace_6877771
  have hstable : (prefixWord ++ tailWord_6877771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877771).length < 2 ^ (prefixWord ++ tailWord_6877771).sum := by decide
  have hdescent : baseEnd_6877771 < baseStart_6877771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877805 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_6877805 : Nat := 118140960795 + 6877805 * 2 ^ 59
def prefixEnd_6877805 : Nat := 4983230072969 + 3 ^ 40 * 6877805 * 2
def baseEnd_6877805 : Nat := 1177206604298856096669019

theorem tailTrace_6877805 : CollatzResearch.WordTrace tailWord_6877805 prefixEnd_6877805 1177206604298856096669019 := by
  unfold tailWord_6877805
  simp only [CollatzResearch.WordTrace]
  refine ⟨250854156847894595421594869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167236104565263063614396579 250854156847894595421594869)
  ·
    refine ⟨23517577204490118320774519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250854156847894595421594869 23517577204490118320774519)
    ·
      refine ⟨35276365806735177481161779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23517577204490118320774519 35276365806735177481161779)
      ·
        refine ⟨52914548710102766221742669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35276365806735177481161779 52914548710102766221742669)
        ·
          refine ⟨19842955766288537333153501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52914548710102766221742669 19842955766288537333153501)
          ·
            refine ⟨7441108412358201499932563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19842955766288537333153501 7441108412358201499932563)
            ·
              refine ⟨11161662618537302249898845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441108412358201499932563 11161662618537302249898845)
              ·
                refine ⟨4185623481951488343712067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11161662618537302249898845 4185623481951488343712067)
                ·
                  refine ⟨6278435222927232515568101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185623481951488343712067 6278435222927232515568101)
                  ·
                    refine ⟨1177206604298856096669019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6278435222927232515568101 1177206604298856096669019)
                    ·
                      rfl

theorem cell23_6877805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_6877805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877805 prefixEnd_6877805 := by exact prefixLift 6877805
  have htrace : WordTrace (prefixWord ++ tailWord_6877805) baseStart_6877805 baseEnd_6877805 := by
    simpa [prefixWord, tailWord_6877805, baseEnd_6877805] using wordTrace_append hprefix tailTrace_6877805
  have hstable : (prefixWord ++ tailWord_6877805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877805).length < 2 ^ (prefixWord ++ tailWord_6877805).sum := by decide
  have hdescent : baseEnd_6877805 < baseStart_6877805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877828 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_6877828 : Nat := 118140960795 + 6877828 * 2 ^ 59
def prefixEnd_6877828 : Nat := 4983230072969 + 3 ^ 40 * 6877828 * 2
def baseEnd_6877828 : Nat := 3531631622951621700019451

theorem tailTrace_6877828 : CollatzResearch.WordTrace tailWord_6877828 prefixEnd_6877828 3531631622951621700019451 := by
  unfold tailWord_6877828
  simp only [CollatzResearch.WordTrace]
  refine ⟨125427497863405635174841069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167236663817874180233121425 125427497863405635174841069)
  ·
    refine ⟨47035311698777113190565401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125427497863405635174841069 47035311698777113190565401)
    ·
      refine ⟨35276483774082834892924051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47035311698777113190565401 35276483774082834892924051)
      ·
        refine ⟨52914725661124252339386077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35276483774082834892924051 52914725661124252339386077)
        ·
          refine ⟨19843022122921594627269779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52914725661124252339386077 19843022122921594627269779)
          ·
            refine ⟨29764533184382391940904669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843022122921594627269779 29764533184382391940904669)
            ·
              refine ⟨11161699944143396977839251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29764533184382391940904669 11161699944143396977839251)
              ·
                refine ⟨16742549916215095466758877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161699944143396977839251 16742549916215095466758877)
                ·
                  refine ⟨6278456218580660800034579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16742549916215095466758877 6278456218580660800034579)
                  ·
                    refine ⟨9417684327870991200051869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278456218580660800034579 9417684327870991200051869)
                    ·
                      refine ⟨3531631622951621700019451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9417684327870991200051869 3531631622951621700019451)
                      ·
                        rfl

theorem cell23_6877828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_6877828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877828 prefixEnd_6877828 := by exact prefixLift 6877828
  have htrace : WordTrace (prefixWord ++ tailWord_6877828) baseStart_6877828 baseEnd_6877828 := by
    simpa [prefixWord, tailWord_6877828, baseEnd_6877828] using wordTrace_append hprefix tailTrace_6877828
  have hstable : (prefixWord ++ tailWord_6877828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877828).length < 2 ^ (prefixWord ++ tailWord_6877828).sum := by decide
  have hdescent : baseEnd_6877828 < baseStart_6877828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877851 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 9, 2, 2]
def baseStart_6877851 : Nat := 118140960795 + 6877851 * 2 ^ 59
def prefixEnd_6877851 : Nat := 4983230072969 + 3 ^ 40 * 6877851 * 2
def baseEnd_6877851 : Nat := 3531643433006675110031845

theorem tailTrace_6877851 : CollatzResearch.WordTrace tailWord_6877851 prefixEnd_6877851 3531643433006675110031845 := by
  unfold tailWord_6877851
  simp only [CollatzResearch.WordTrace]
  refine ⟨250855834605727945277769407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167237223070485296851846271 250855834605727945277769407)
  ·
    refine ⟨376283751908591917916654111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250855834605727945277769407 376283751908591917916654111)
    ·
      refine ⟨564425627862887876874981167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376283751908591917916654111 564425627862887876874981167)
      ·
        refine ⟨846638441794331815312471751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564425627862887876874981167 846638441794331815312471751)
        ·
          refine ⟨1269957662691497722968707627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846638441794331815312471751 1269957662691497722968707627)
          ·
            refine ⟨1904936494037246584453061441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269957662691497722968707627 1904936494037246584453061441)
            ·
              refine ⟨1428702370527934938339796081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904936494037246584453061441 1428702370527934938339796081)
              ·
                refine ⟨1071526777895951203754847061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428702370527934938339796081 1071526777895951203754847061)
                ·
                  refine ⟨6278477214234089084501057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1071526777895951203754847061 6278477214234089084501057)
                  ·
                    refine ⟨4708857910675566813375793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278477214234089084501057 4708857910675566813375793)
                    ·
                      refine ⟨3531643433006675110031845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708857910675566813375793 3531643433006675110031845)
                      ·
                        rfl

theorem cell23_6877851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 2, 2].length) (baseStart_6877851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877851 prefixEnd_6877851 := by exact prefixLift 6877851
  have htrace : WordTrace (prefixWord ++ tailWord_6877851) baseStart_6877851 baseEnd_6877851 := by
    simpa [prefixWord, tailWord_6877851, baseEnd_6877851] using wordTrace_append hprefix tailTrace_6877851
  have hstable : (prefixWord ++ tailWord_6877851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877851).length < 2 ^ (prefixWord ++ tailWord_6877851).sum := by decide
  have hdescent : baseEnd_6877851 < baseStart_6877851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877871 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 5]
def baseStart_6877871 : Nat := 118140960795 + 6877871 * 2 ^ 59
def prefixEnd_6877871 : Nat := 4983230072969 + 3 ^ 40 * 6877871 * 2
def baseEnd_6877871 : Nat := 3531653702619765031781753

theorem tailTrace_6877871 : CollatzResearch.WordTrace tailWord_6877871 prefixEnd_6877871 3531653702619765031781753 := by
  unfold tailWord_6877871
  simp only [CollatzResearch.WordTrace]
  refine ⟨250856564065655488693497467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167237709377103659128998311 250856564065655488693497467)
  ·
    refine ⟨376284846098483233040246201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250856564065655488693497467 376284846098483233040246201)
    ·
      refine ⟨282213634573862424780184651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376284846098483233040246201 282213634573862424780184651)
      ·
        refine ⟨423320451860793637170276977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282213634573862424780184651 423320451860793637170276977)
        ·
          refine ⟨317490338895595227877707733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423320451860793637170276977 317490338895595227877707733)
          ·
            refine ⟨7441179817865513153383775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 317490338895595227877707733 7441179817865513153383775)
            ·
              refine ⟨11161769726798269730075663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441179817865513153383775 11161769726798269730075663)
              ·
                refine ⟨16742654590197404595113495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161769726798269730075663 16742654590197404595113495)
                ·
                  refine ⟨25113981885296106892670243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16742654590197404595113495 25113981885296106892670243)
                  ·
                    refine ⟨37670972827944160339005365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25113981885296106892670243 37670972827944160339005365)
                    ·
                      refine ⟨3531653702619765031781753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37670972827944160339005365 3531653702619765031781753)
                      ·
                        rfl

theorem cell23_6877871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_6877871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877871 prefixEnd_6877871 := by exact prefixLift 6877871
  have htrace : WordTrace (prefixWord ++ tailWord_6877871) baseStart_6877871 baseEnd_6877871 := by
    simpa [prefixWord, tailWord_6877871, baseEnd_6877871] using wordTrace_append hprefix tailTrace_6877871
  have hstable : (prefixWord ++ tailWord_6877871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877871).length < 2 ^ (prefixWord ++ tailWord_6877871).sum := by decide
  have hdescent : baseEnd_6877871 < baseStart_6877871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877879 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 1, 1, 3]
def baseStart_6877879 : Nat := 118140960795 + 6877879 * 2 ^ 59
def prefixEnd_6877879 : Nat := 4983230072969 + 3 ^ 40 * 6877879 * 2
def baseEnd_6877879 : Nat := 3531657810465001000481717

theorem tailTrace_6877879 : CollatzResearch.WordTrace tailWord_6877879 prefixEnd_6877879 3531657810465001000481717 := by
  unfold tailWord_6877879
  simp only [CollatzResearch.WordTrace]
  refine ⟨250856855849626506059788691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167237903899751004039859127 250856855849626506059788691)
  ·
    refine ⟨376285283774439759089683037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250856855849626506059788691 376285283774439759089683037)
    ·
      refine ⟨141106981415414909658631139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376285283774439759089683037 141106981415414909658631139)
      ·
        refine ⟨211660472123122364487946709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141106981415414909658631139 211660472123122364487946709)
        ·
          refine ⟨4960792315385680417686251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 211660472123122364487946709 4960792315385680417686251)
          ·
            refine ⟨7441188473078520626529377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960792315385680417686251 7441188473078520626529377)
            ·
              refine ⟨5580891354808890469897033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7441188473078520626529377 5580891354808890469897033)
              ·
                refine ⟨4185668516106667852422775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5580891354808890469897033 4185668516106667852422775)
                ·
                  refine ⟨6278502774160001778634163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185668516106667852422775 6278502774160001778634163)
                  ·
                    refine ⟨9417754161240002667951245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278502774160001778634163 9417754161240002667951245)
                    ·
                      refine ⟨3531657810465001000481717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9417754161240002667951245 3531657810465001000481717)
                      ·
                        rfl

theorem cell23_6877879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_6877879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877879 prefixEnd_6877879 := by exact prefixLift 6877879
  have htrace : WordTrace (prefixWord ++ tailWord_6877879) baseStart_6877879 baseEnd_6877879 := by
    simpa [prefixWord, tailWord_6877879, baseEnd_6877879] using wordTrace_append hprefix tailTrace_6877879
  have hstable : (prefixWord ++ tailWord_6877879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877879).length < 2 ^ (prefixWord ++ tailWord_6877879).sum := by decide
  have hdescent : baseEnd_6877879 < baseStart_6877879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877908 : List Nat := [2, 4, 1, 3, 2, 1, 3, 7]
def baseStart_6877908 : Nat := 118140960795 + 6877908 * 2 ^ 59
def prefixEnd_6877908 : Nat := 4983230072969 + 3 ^ 40 * 6877908 * 2
def baseEnd_6877908 : Nat := 130802692644591903222929

theorem tailTrace_6877908 : CollatzResearch.WordTrace tailWord_6877908 prefixEnd_6877908 130802692644591903222929 := by
  unfold tailWord_6877908
  simp only [CollatzResearch.WordTrace]
  refine ⟨125428956783260722006297189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167238609044347629341729585 125428956783260722006297189)
  ·
    refine ⟨23517929396861385376180723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125428956783260722006297189 23517929396861385376180723)
    ·
      refine ⟨35276894095292078064271085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23517929396861385376180723 35276894095292078064271085)
      ·
        refine ⟨13228835285734529274101657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35276894095292078064271085 13228835285734529274101657)
        ·
          refine ⟨9921626464300896955576243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13228835285734529274101657 9921626464300896955576243)
          ·
            refine ⟨14882439696451345433364365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921626464300896955576243 14882439696451345433364365)
            ·
              refine ⟨5580914886169254537511637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14882439696451345433364365 5580914886169254537511637)
              ·
                refine ⟨130802692644591903222929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5580914886169254537511637 130802692644591903222929)
                ·
                  rfl

theorem cell23_6877908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 7].length) (baseStart_6877908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877908 prefixEnd_6877908 := by exact prefixLift 6877908
  have htrace : WordTrace (prefixWord ++ tailWord_6877908) baseStart_6877908 baseEnd_6877908 := by
    simpa [prefixWord, tailWord_6877908, baseEnd_6877908] using wordTrace_append hprefix tailTrace_6877908
  have hstable : (prefixWord ++ tailWord_6877908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877908).length < 2 ^ (prefixWord ++ tailWord_6877908).sum := by decide
  have hdescent : baseEnd_6877908 < baseStart_6877908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877914 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_6877914 : Nat := 118140960795 + 6877914 * 2 ^ 59
def prefixEnd_6877914 : Nat := 4983230072969 + 3 ^ 40 * 6877914 * 2
def baseEnd_6877914 : Nat := 3531675782287908363544055

theorem tailTrace_6877914 : CollatzResearch.WordTrace tailWord_6877914 prefixEnd_6877914 3531675782287908363544055 := by
  unfold tailWord_6877914
  simp only [CollatzResearch.WordTrace]
  refine ⟨62714533101124926759328199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167238754936333138024875197 62714533101124926759328199)
  ·
    refine ⟨94071799651687390138992299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62714533101124926759328199 94071799651687390138992299)
    ·
      refine ⟨141107699477531085208488449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94071799651687390138992299 141107699477531085208488449)
      ·
        refine ⟨105830774608148313906366337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141107699477531085208488449 105830774608148313906366337)
        ·
          refine ⟨79373080956111235429774753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105830774608148313906366337 79373080956111235429774753)
          ·
            refine ⟨59529810717083426572331065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79373080956111235429774753 59529810717083426572331065)
            ·
              refine ⟨44647358037812569929248299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59529810717083426572331065 44647358037812569929248299)
              ·
                refine ⟨66971037056718854893872449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44647358037812569929248299 66971037056718854893872449)
                ·
                  refine ⟨50228277792539141170404337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66971037056718854893872449 50228277792539141170404337)
                  ·
                    refine ⟨37671208344404355877803253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50228277792539141170404337 37671208344404355877803253)
                    ·
                      refine ⟨3531675782287908363544055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37671208344404355877803253 3531675782287908363544055)
                      ·
                        rfl

theorem cell23_6877914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_6877914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877914 prefixEnd_6877914 := by exact prefixLift 6877914
  have htrace : WordTrace (prefixWord ++ tailWord_6877914) baseStart_6877914 baseEnd_6877914 := by
    simpa [prefixWord, tailWord_6877914, baseEnd_6877914] using wordTrace_append hprefix tailTrace_6877914
  have hstable : (prefixWord ++ tailWord_6877914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877914).length < 2 ^ (prefixWord ++ tailWord_6877914).sum := by decide
  have hdescent : baseEnd_6877914 < baseStart_6877914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877935 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 3]
def baseStart_6877935 : Nat := 118140960795 + 6877935 * 2 ^ 59
def prefixEnd_6877935 : Nat := 4983230072969 + 3 ^ 40 * 6877935 * 2
def baseEnd_6877935 : Nat := 3531686565381652781381459

theorem tailTrace_6877935 : CollatzResearch.WordTrace tailWord_6877935 prefixEnd_6877935 3531686565381652781381459 := by
  unfold tailWord_6877935
  simp only [CollatzResearch.WordTrace]
  refine ⟨250858898337423627623827259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167239265558282418415884839 250858898337423627623827259)
  ·
    refine ⟨376288347506135441435740889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250858898337423627623827259 376288347506135441435740889)
    ·
      refine ⟨282216260629601581076805667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376288347506135441435740889 282216260629601581076805667)
      ·
        refine ⟨423324390944402371615208501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282216260629601581076805667 423324390944402371615208501)
        ·
          refine ⟨39686661651037722338925797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 423324390944402371615208501 39686661651037722338925797)
          ·
            refine ⟨7441249059569572938548587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39686661651037722338925797 7441249059569572938548587)
            ·
              refine ⟨11161873589354359407822881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441249059569572938548587 11161873589354359407822881)
              ·
                refine ⟨8371405192015769555867161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11161873589354359407822881 8371405192015769555867161)
                ·
                  refine ⟨6278553894011827166900371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8371405192015769555867161 6278553894011827166900371)
                  ·
                    refine ⟨9417830841017740750350557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278553894011827166900371 9417830841017740750350557)
                    ·
                      refine ⟨3531686565381652781381459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9417830841017740750350557 3531686565381652781381459)
                      ·
                        rfl

theorem cell23_6877935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_6877935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877935 prefixEnd_6877935 := by exact prefixLift 6877935
  have htrace : WordTrace (prefixWord ++ tailWord_6877935) baseStart_6877935 baseEnd_6877935 := by
    simpa [prefixWord, tailWord_6877935, baseEnd_6877935] using wordTrace_append hprefix tailTrace_6877935
  have hstable : (prefixWord ++ tailWord_6877935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877935).length < 2 ^ (prefixWord ++ tailWord_6877935).sum := by decide
  have hdescent : baseEnd_6877935 < baseStart_6877935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6877998 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_6877998 : Nat := 118140960795 + 6877998 * 2 ^ 59
def prefixEnd_6877998 : Nat := 4983230072969 + 3 ^ 40 * 6877998 * 2
def baseEnd_6877998 : Nat := 392413212740320670543741

theorem tailTrace_6877998 : CollatzResearch.WordTrace tailWord_6877998 prefixEnd_6877998 392413212740320670543741 := by
  unfold tailWord_6877998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31357649517024423672921331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167240797424130259588913765 31357649517024423672921331)
  ·
    refine ⟨47036474275536635509381997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31357649517024423672921331 47036474275536635509381997)
    ·
      refine ⟨17638677853326238316018249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47036474275536635509381997 17638677853326238316018249)
      ·
        refine ⟨13229008389994678737013687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17638677853326238316018249 13229008389994678737013687)
        ·
          refine ⟨19843512584992018105520531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13229008389994678737013687 19843512584992018105520531)
          ·
            refine ⟨29765268877488027158280797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843512584992018105520531 29765268877488027158280797)
            ·
              refine ⟨11161975829058010184355299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29765268877488027158280797 11161975829058010184355299)
              ·
                refine ⟨16742963743587015276532949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161975829058010184355299 16742963743587015276532949)
                ·
                  refine ⟨392413212740320670543741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16742963743587015276532949 392413212740320670543741)
                  ·
                    rfl

theorem cell23_6877998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_6877998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6877998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6877998 prefixEnd_6877998 := by exact prefixLift 6877998
  have htrace : WordTrace (prefixWord ++ tailWord_6877998) baseStart_6877998 baseEnd_6877998 := by
    simpa [prefixWord, tailWord_6877998, baseEnd_6877998] using wordTrace_append hprefix tailTrace_6877998
  have hstable : (prefixWord ++ tailWord_6877998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6877998).length < 2 ^ (prefixWord ++ tailWord_6877998).sum := by decide
  have hdescent : baseEnd_6877998 < baseStart_6877998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6877998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878028 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_6878028 : Nat := 118140960795 + 6878028 * 2 ^ 59
def prefixEnd_6878028 : Nat := 4983230072969 + 3 ^ 40 * 6878028 * 2
def baseEnd_6878028 : Nat := 1177244773027506972506177

theorem tailTrace_6878028 : CollatzResearch.WordTrace tailWord_6878028 prefixEnd_6878028 1177244773027506972506177 := by
  unfold tailWord_6878028
  simp only [CollatzResearch.WordTrace]
  refine ⟨125431145163043352253481369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167241526884057803004641825 125431145163043352253481369)
  ·
    refine ⟨94073358872282514190111027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125431145163043352253481369 94073358872282514190111027)
    ·
      refine ⟨141110038308423771285166541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94073358872282514190111027 141110038308423771285166541)
      ·
        refine ⟨52916264365658914231937453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141110038308423771285166541 52916264365658914231937453)
        ·
          refine ⟨19843599137122092836976545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52916264365658914231937453 19843599137122092836976545)
          ·
            refine ⟨14882699352841569627732409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19843599137122092836976545 14882699352841569627732409)
            ·
              refine ⟨11162024514631177220799307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14882699352841569627732409 11162024514631177220799307)
              ·
                refine ⟨16743036771946765831198961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11162024514631177220799307 16743036771946765831198961)
                ·
                  refine ⟨12557277578960074373399221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16743036771946765831198961 12557277578960074373399221)
                  ·
                    refine ⟨1177244773027506972506177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12557277578960074373399221 1177244773027506972506177)
                    ·
                      rfl

theorem cell23_6878028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_6878028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878028 prefixEnd_6878028 := by exact prefixLift 6878028
  have htrace : WordTrace (prefixWord ++ tailWord_6878028) baseStart_6878028 baseEnd_6878028 := by
    simpa [prefixWord, tailWord_6878028, baseEnd_6878028] using wordTrace_append hprefix tailTrace_6878028
  have hstable : (prefixWord ++ tailWord_6878028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878028).length < 2 ^ (prefixWord ++ tailWord_6878028).sum := by decide
  have hdescent : baseEnd_6878028 < baseStart_6878028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878048 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 2, 4, 2]
def baseStart_6878048 : Nat := 118140960795 + 6878048 * 2 ^ 59
def prefixEnd_6878048 : Nat := 4983230072969 + 3 ^ 40 * 6878048 * 2
def baseEnd_6878048 : Nat := 3531744588695610839268439

theorem tailTrace_6878048 : CollatzResearch.WordTrace tailWord_6878048 prefixEnd_6878048 3531744588695610839268439 := by
  unfold tailWord_6878048
  simp only [CollatzResearch.WordTrace]
  refine ⟨125431509893007123961345399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167242013190676165281793865 125431509893007123961345399)
  ·
    refine ⟨188147264839510685942018099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125431509893007123961345399 188147264839510685942018099)
    ·
      refine ⟨282220897259266028913027149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188147264839510685942018099 282220897259266028913027149)
      ·
        refine ⟨105832836472224760842385181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282220897259266028913027149 105832836472224760842385181)
        ·
          refine ⟨39687313677084285315894443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105832836472224760842385181 39687313677084285315894443)
          ·
            refine ⟨59530970515626427973841665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39687313677084285315894443 59530970515626427973841665)
            ·
              refine ⟨44648227886719820980381249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59530970515626427973841665 44648227886719820980381249)
              ·
                refine ⟨33486170915039865735285937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44648227886719820980381249 33486170915039865735285937)
                ·
                  refine ⟨25114628186279899301464453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33486170915039865735285937 25114628186279899301464453)
                  ·
                    refine ⟨4708992784927481119024585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25114628186279899301464453 4708992784927481119024585)
                    ·
                      refine ⟨3531744588695610839268439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4708992784927481119024585 3531744588695610839268439)
                      ·
                        rfl

theorem cell23_6878048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_6878048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878048 prefixEnd_6878048 := by exact prefixLift 6878048
  have htrace : WordTrace (prefixWord ++ tailWord_6878048) baseStart_6878048 baseEnd_6878048 := by
    simpa [prefixWord, tailWord_6878048, baseEnd_6878048] using wordTrace_append hprefix tailTrace_6878048
  have hstable : (prefixWord ++ tailWord_6878048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878048).length < 2 ^ (prefixWord ++ tailWord_6878048).sum := by decide
  have hdescent : baseEnd_6878048 < baseStart_6878048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878061 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6878061 : Nat := 118140960795 + 6878061 * 2 ^ 59
def prefixEnd_6878061 : Nat := 4983230072969 + 3 ^ 40 * 6878061 * 2
def baseEnd_6878061 : Nat := 3531751263944119288405879

theorem tailTrace_6878061 : CollatzResearch.WordTrace tailWord_6878061 prefixEnd_6878061 3531751263944119288405879 := by
  unfold tailWord_6878061
  simp only [CollatzResearch.WordTrace]
  refine ⟨250863493934967151142914037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167242329289978100761942691 250863493934967151142914037)
  ·
    refine ⟨23518452556403170419648191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250863493934967151142914037 23518452556403170419648191)
    ·
      refine ⟨35277678834604755629472287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23518452556403170419648191 35277678834604755629472287)
      ·
        refine ⟨52916518251907133444208431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35277678834604755629472287 52916518251907133444208431)
        ·
          refine ⟨79374777377860700166312647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52916518251907133444208431 79374777377860700166312647)
          ·
            refine ⟨119062166066791050249468971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79374777377860700166312647 119062166066791050249468971)
            ·
              refine ⟨178593249100186575374203457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119062166066791050249468971 178593249100186575374203457)
              ·
                refine ⟨133944936825139931530652593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178593249100186575374203457 133944936825139931530652593)
                ·
                  refine ⟨100458702618854948647989445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133944936825139931530652593 100458702618854948647989445)
                  ·
                    refine ⟨18836006741035302871498021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100458702618854948647989445 18836006741035302871498021)
                    ·
                      refine ⟨3531751263944119288405879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18836006741035302871498021 3531751263944119288405879)
                      ·
                        rfl

theorem cell23_6878061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6878061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878061 prefixEnd_6878061 := by exact prefixLift 6878061
  have htrace : WordTrace (prefixWord ++ tailWord_6878061) baseStart_6878061 baseEnd_6878061 := by
    simpa [prefixWord, tailWord_6878061, baseEnd_6878061] using wordTrace_append hprefix tailTrace_6878061
  have hstable : (prefixWord ++ tailWord_6878061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878061).length < 2 ^ (prefixWord ++ tailWord_6878061).sum := by decide
  have hdescent : baseEnd_6878061 < baseStart_6878061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878082 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6878082 : Nat := 118140960795 + 6878082 * 2 ^ 59
def prefixEnd_6878082 : Nat := 4983230072969 + 3 ^ 40 * 6878082 * 2
def baseEnd_6878082 : Nat := 3531762047037863706243283

theorem tailTrace_6878082 : CollatzResearch.WordTrace tailWord_6878082 prefixEnd_6878082 3531762047037863706243283 := by
  unfold tailWord_6878082
  simp only [CollatzResearch.WordTrace]
  refine ⟨62716064966972767932357125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167242839911927381152952333 62716064966972767932357125)
  ·
    refine ⟨11759262181307393987316961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62716064966972767932357125 11759262181307393987316961)
    ·
      refine ⟨8819446635980545490487721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11759262181307393987316961 8819446635980545490487721)
      ·
        refine ⟨6614584976985409117865791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8819446635980545490487721 6614584976985409117865791)
        ·
          refine ⟨9921877465478113676798687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614584976985409117865791 9921877465478113676798687)
          ·
            refine ⟨14882816198217170515198031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921877465478113676798687 14882816198217170515198031)
            ·
              refine ⟨22324224297325755772797047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14882816198217170515198031 22324224297325755772797047)
              ·
                refine ⟨33486336445988633659195571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22324224297325755772797047 33486336445988633659195571)
                ·
                  refine ⟨50229504668982950488793357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33486336445988633659195571 50229504668982950488793357)
                  ·
                    refine ⟨18836064250868606433297509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50229504668982950488793357 18836064250868606433297509)
                    ·
                      refine ⟨3531762047037863706243283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18836064250868606433297509 3531762047037863706243283)
                      ·
                        rfl

theorem cell23_6878082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6878082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878082 prefixEnd_6878082 := by exact prefixLift 6878082
  have htrace : WordTrace (prefixWord ++ tailWord_6878082) baseStart_6878082 baseEnd_6878082 := by
    simpa [prefixWord, tailWord_6878082, baseEnd_6878082] using wordTrace_append hprefix tailTrace_6878082
  have hstable : (prefixWord ++ tailWord_6878082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878082).length < 2 ^ (prefixWord ++ tailWord_6878082).sum := by decide
  have hdescent : baseEnd_6878082 < baseStart_6878082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878085 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_6878085 : Nat := 118140960795 + 6878085 * 2 ^ 59
def prefixEnd_6878085 : Nat := 4983230072969 + 3 ^ 40 * 6878085 * 2
def baseEnd_6878085 : Nat := 3531763587479827194505769

theorem tailTrace_6878085 : CollatzResearch.WordTrace tailWord_6878085 prefixEnd_6878085 3531763587479827194505769 := by
  unfold tailWord_6878085
  simp only [CollatzResearch.WordTrace]
  refine ⟨250864369286880203241787709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167242912857920135494525139 250864369286880203241787709)
  ·
    refine ⟨94074138482580076215670391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250864369286880203241787709 94074138482580076215670391)
    ·
      refine ⟨141111207723870114323505587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94074138482580076215670391 141111207723870114323505587)
      ·
        refine ⟨211666811585805171485258381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141111207723870114323505587 211666811585805171485258381)
        ·
          refine ⟨79375054344676939306971893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211666811585805171485258381 79375054344676939306971893)
          ·
            refine ⟨7441411344813463060028615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79375054344676939306971893 7441411344813463060028615)
            ·
              refine ⟨11162117017220194590042923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441411344813463060028615 11162117017220194590042923)
              ·
                refine ⟨16743175525830291885064385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11162117017220194590042923 16743175525830291885064385)
                ·
                  refine ⟨12557381644372718913798289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16743175525830291885064385 12557381644372718913798289)
                  ·
                    refine ⟨9418036233279539185348717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12557381644372718913798289 9418036233279539185348717)
                    ·
                      refine ⟨3531763587479827194505769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9418036233279539185348717 3531763587479827194505769)
                      ·
                        rfl

theorem cell23_6878085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_6878085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878085 prefixEnd_6878085 := by exact prefixLift 6878085
  have htrace : WordTrace (prefixWord ++ tailWord_6878085) baseStart_6878085 baseEnd_6878085 := by
    simpa [prefixWord, tailWord_6878085, baseEnd_6878085] using wordTrace_append hprefix tailTrace_6878085
  have hstable : (prefixWord ++ tailWord_6878085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878085).length < 2 ^ (prefixWord ++ tailWord_6878085).sum := by decide
  have hdescent : baseEnd_6878085 < baseStart_6878085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878131 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 1, 6]
def baseStart_6878131 : Nat := 118140960795 + 6878131 * 2 ^ 59
def prefixEnd_6878131 : Nat := 4983230072969 + 3 ^ 40 * 6878131 * 2
def baseEnd_6878131 : Nat := 1177262402529978004843519

theorem tailTrace_6878131 : CollatzResearch.WordTrace tailWord_6878131 prefixEnd_6878131 1177262402529978004843519 := by
  unfold tailWord_6878131
  simp only [CollatzResearch.WordTrace]
  refine ⟨250866047044713553097962247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167244031363142368731974831 250866047044713553097962247)
  ·
    refine ⟨376299070567070329646943371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250866047044713553097962247 376299070567070329646943371)
    ·
      refine ⟨564448605850605494470415057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376299070567070329646943371 564448605850605494470415057)
      ·
        refine ⟨423336454387954120852811293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564448605850605494470415057 423336454387954120852811293)
        ·
          refine ⟨158751170395482795319804235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423336454387954120852811293 158751170395482795319804235)
          ·
            refine ⟨238126755593224192979706353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158751170395482795319804235 238126755593224192979706353)
            ·
              refine ⟨178595066694918144734779765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238126755593224192979706353 178595066694918144734779765)
              ·
                refine ⟨16743287502648576068885603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178595066694918144734779765 16743287502648576068885603)
                ·
                  refine ⟨25114931253972864103328405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16743287502648576068885603 25114931253972864103328405)
                  ·
                    refine ⟨1177262402529978004843519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25114931253972864103328405 1177262402529978004843519)
                    ·
                      rfl

theorem cell23_6878131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 6].length) (baseStart_6878131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878131 prefixEnd_6878131 := by exact prefixLift 6878131
  have htrace : WordTrace (prefixWord ++ tailWord_6878131) baseStart_6878131 baseEnd_6878131 := by
    simpa [prefixWord, tailWord_6878131, baseEnd_6878131] using wordTrace_append hprefix tailTrace_6878131
  have hstable : (prefixWord ++ tailWord_6878131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878131).length < 2 ^ (prefixWord ++ tailWord_6878131).sum := by decide
  have hdescent : baseEnd_6878131 < baseStart_6878131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878138 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2]
def baseStart_6878138 : Nat := 118140960795 + 6878138 * 2 ^ 59
def prefixEnd_6878138 : Nat := 4983230072969 + 3 ^ 40 * 6878138 * 2
def baseEnd_6878138 : Nat := 3531790801954515487143025

theorem tailTrace_6878138 : CollatzResearch.WordTrace tailWord_6878138 prefixEnd_6878138 3531790801954515487143025 := by
  unfold tailWord_6878138
  simp only [CollatzResearch.WordTrace]
  refine ⟨62716575588922048323366767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167244201570458795528978045 62716575588922048323366767)
  ·
    refine ⟨94074863383383072485050151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62716575588922048323366767 94074863383383072485050151)
    ·
      refine ⟨141112295075074608727575227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94074863383383072485050151 141112295075074608727575227)
      ·
        refine ⟨211668442612611913091362841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141112295075074608727575227 211668442612611913091362841)
        ·
          refine ⟨158751331959458934818522131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211668442612611913091362841 158751331959458934818522131)
          ·
            refine ⟨238126997939188402227783197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158751331959458934818522131 238126997939188402227783197)
            ·
              refine ⟨89297624227195650835418699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238126997939188402227783197 89297624227195650835418699)
              ·
                refine ⟨133946436340793476253128049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89297624227195650835418699 133946436340793476253128049)
                ·
                  refine ⟨100459827255595107189846037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133946436340793476253128049 100459827255595107189846037)
                  ·
                    refine ⟨4709054402606020649524033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100459827255595107189846037 4709054402606020649524033)
                    ·
                      refine ⟨3531790801954515487143025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709054402606020649524033 3531790801954515487143025)
                      ·
                        rfl

theorem cell23_6878138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_6878138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878138 prefixEnd_6878138 := by exact prefixLift 6878138
  have htrace : WordTrace (prefixWord ++ tailWord_6878138) baseStart_6878138 baseEnd_6878138 := by
    simpa [prefixWord, tailWord_6878138, baseEnd_6878138] using wordTrace_append hprefix tailTrace_6878138
  have hstable : (prefixWord ++ tailWord_6878138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878138).length < 2 ^ (prefixWord ++ tailWord_6878138).sum := by decide
  have hdescent : baseEnd_6878138 < baseStart_6878138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878158 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_6878158 : Nat := 118140960795 + 6878158 * 2 ^ 59
def prefixEnd_6878158 : Nat := 4983230072969 + 3 ^ 40 * 6878158 * 2
def baseEnd_6878158 : Nat := 3531801071567605408892933

theorem tailTrace_6878158 : CollatzResearch.WordTrace tailWord_6878158 prefixEnd_6878158 3531801071567605408892933 := by
  unfold tailWord_6878158
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358378976951967088649391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167244687877077157806130085 31358378976951967088649391)
  ·
    refine ⟨47037568465427950632974087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31358378976951967088649391 47037568465427950632974087)
    ·
      refine ⟨70556352698141925949461131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47037568465427950632974087 70556352698141925949461131)
      ·
        refine ⟨105834529047212888924191697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70556352698141925949461131 105834529047212888924191697)
        ·
          refine ⟨79375896785409666693143773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105834529047212888924191697 79375896785409666693143773)
          ·
            refine ⟨29765961294528625009928915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79375896785409666693143773 29765961294528625009928915)
            ·
              refine ⟨44648941941792937514893373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29765961294528625009928915 44648941941792937514893373)
              ·
                refine ⟨16743353228172351568085015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44648941941792937514893373 16743353228172351568085015)
                ·
                  refine ⟨25115029842258527352127523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16743353228172351568085015 25115029842258527352127523)
                  ·
                    refine ⟨37672544763387791028191285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25115029842258527352127523 37672544763387791028191285)
                    ·
                      refine ⟨3531801071567605408892933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37672544763387791028191285 3531801071567605408892933)
                      ·
                        rfl

theorem cell23_6878158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_6878158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878158 prefixEnd_6878158 := by exact prefixLift 6878158
  have htrace : WordTrace (prefixWord ++ tailWord_6878158) baseStart_6878158 baseEnd_6878158 := by
    simpa [prefixWord, tailWord_6878158, baseEnd_6878158] using wordTrace_append hprefix tailTrace_6878158
  have hstable : (prefixWord ++ tailWord_6878158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878158).length < 2 ^ (prefixWord ++ tailWord_6878158).sum := by decide
  have hdescent : baseEnd_6878158 < baseStart_6878158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878222 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_6878222 : Nat := 118140960795 + 6878222 * 2 ^ 59
def prefixEnd_6878222 : Nat := 4983230072969 + 3 ^ 40 * 6878222 * 2
def baseEnd_6878222 : Nat := 3531833934329493158492639

theorem tailTrace_6878222 : CollatzResearch.WordTrace tailWord_6878222 prefixEnd_6878222 3531833934329493158492639 := by
  unfold tailWord_6878222
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358670760922984454940615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167246244058255917093016613 31358670760922984454940615)
  ·
    refine ⟨47038006141384476682410923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31358670760922984454940615 47038006141384476682410923)
    ·
      refine ⟨70557009212076715023616385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47038006141384476682410923 70557009212076715023616385)
      ·
        refine ⟨52917756909057536267712289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70557009212076715023616385 52917756909057536267712289)
        ·
          refine ⟨39688317681793152200784217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52917756909057536267712289 39688317681793152200784217)
          ·
            refine ⟨29766238261344864150588163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39688317681793152200784217 29766238261344864150588163)
            ·
              refine ⟨44649357392017296225882245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29766238261344864150588163 44649357392017296225882245)
              ·
                refine ⟨8371754511003243042352921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44649357392017296225882245 8371754511003243042352921)
                ·
                  refine ⟨6278815883252432281764691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8371754511003243042352921 6278815883252432281764691)
                  ·
                    refine ⟨9418223824878648422647037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278815883252432281764691 9418223824878648422647037)
                    ·
                      refine ⟨3531833934329493158492639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9418223824878648422647037 3531833934329493158492639)
                      ·
                        rfl

theorem cell23_6878222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_6878222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878222 prefixEnd_6878222 := by exact prefixLift 6878222
  have htrace : WordTrace (prefixWord ++ tailWord_6878222) baseStart_6878222 baseEnd_6878222 := by
    simpa [prefixWord, tailWord_6878222, baseEnd_6878222] using wordTrace_append hprefix tailTrace_6878222
  have hstable : (prefixWord ++ tailWord_6878222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878222).length < 2 ^ (prefixWord ++ tailWord_6878222).sum := by decide
  have hdescent : baseEnd_6878222 < baseStart_6878222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878258 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_6878258 : Nat := 118140960795 + 6878258 * 2 ^ 59
def prefixEnd_6878258 : Nat := 4983230072969 + 3 ^ 40 * 6878258 * 2
def baseEnd_6878258 : Nat := 3531852419633055017642473

theorem tailTrace_6878258 : CollatzResearch.WordTrace tailWord_6878258 prefixEnd_6878258 3531852419633055017642473 := by
  unfold tailWord_6878258
  simp only [CollatzResearch.WordTrace]
  refine ⟨62717669778813363446958857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167247119410168969191890285 62717669778813363446958857)
  ·
    refine ⟨47038252334110022585219143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62717669778813363446958857 47038252334110022585219143)
    ·
      refine ⟨70557378501165033877828715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47038252334110022585219143 70557378501165033877828715)
      ·
        refine ⟨105836067751747550816743073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70557378501165033877828715 105836067751747550816743073)
        ·
          refine ⟨79377050813810663112557305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105836067751747550816743073 79377050813810663112557305)
          ·
            refine ⟨59532788110357997334417979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79377050813810663112557305 59532788110357997334417979)
            ·
              refine ⟨89299182165536996001626969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59532788110357997334417979 89299182165536996001626969)
              ·
                refine ⟨66974386624152747001220227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89299182165536996001626969 66974386624152747001220227)
                ·
                  refine ⟨100461579936229120501830341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66974386624152747001220227 100461579936229120501830341)
                  ·
                    refine ⟨18836546238042960094093189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100461579936229120501830341 18836546238042960094093189)
                    ·
                      refine ⟨3531852419633055017642473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18836546238042960094093189 3531852419633055017642473)
                      ·
                        rfl

theorem cell23_6878258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_6878258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878258 prefixEnd_6878258 := by exact prefixLift 6878258
  have htrace : WordTrace (prefixWord ++ tailWord_6878258) baseStart_6878258 baseEnd_6878258 := by
    simpa [prefixWord, tailWord_6878258, baseEnd_6878258] using wordTrace_append hprefix tailTrace_6878258
  have hstable : (prefixWord ++ tailWord_6878258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878258).length < 2 ^ (prefixWord ++ tailWord_6878258).sum := by decide
  have hdescent : baseEnd_6878258 < baseStart_6878258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878279 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_6878279 : Nat := 118140960795 + 6878279 * 2 ^ 59
def prefixEnd_6878279 : Nat := 4983230072969 + 3 ^ 40 * 6878279 * 2
def baseEnd_6878279 : Nat := 3531863202726799435479877

theorem tailTrace_6878279 : CollatzResearch.WordTrace tailWord_6878279 prefixEnd_6878279 3531863202726799435479877 := by
  unfold tailWord_6878279
  simp only [CollatzResearch.WordTrace]
  refine ⟨250871445048177374374349891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167247630032118249582899927 250871445048177374374349891)
  ·
    refine ⟨376307167572266061561524837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250871445048177374374349891 376307167572266061561524837)
    ·
      refine ⟨70557593919799886542785907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376307167572266061561524837 70557593919799886542785907)
      ·
        refine ⟨105836390879699829814178861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70557593919799886542785907 105836390879699829814178861)
        ·
          refine ⟨39688646579887436180317073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105836390879699829814178861 39688646579887436180317073)
          ·
            refine ⟨29766484934915577135237805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39688646579887436180317073 29766484934915577135237805)
            ·
              refine ⟨11162431850593341425714177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29766484934915577135237805 11162431850593341425714177)
              ·
                refine ⟨8371823887945006069285633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11162431850593341425714177 8371823887945006069285633)
                ·
                  refine ⟨6278867915958754551964225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8371823887945006069285633 6278867915958754551964225)
                  ·
                    refine ⟨4709150936969065913973169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278867915958754551964225 4709150936969065913973169)
                    ·
                      refine ⟨3531863202726799435479877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709150936969065913973169 3531863202726799435479877)
                      ·
                        rfl

theorem cell23_6878279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_6878279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878279 prefixEnd_6878279 := by exact prefixLift 6878279
  have htrace : WordTrace (prefixWord ++ tailWord_6878279) baseStart_6878279 baseEnd_6878279 := by
    simpa [prefixWord, tailWord_6878279, baseEnd_6878279] using wordTrace_append hprefix tailTrace_6878279
  have hstable : (prefixWord ++ tailWord_6878279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878279).length < 2 ^ (prefixWord ++ tailWord_6878279).sum := by decide
  have hdescent : baseEnd_6878279 < baseStart_6878279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
