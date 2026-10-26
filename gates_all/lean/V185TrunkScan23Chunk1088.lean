import V185TrunkScan23Chunk1087

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6442147 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 4]
def baseStart_6442147 : Nat := 118140960795 + 6442147 * 2 ^ 59
def prefixEnd_6442147 : Nat := 4983230072969 + 3 ^ 40 * 6442147 * 2
def baseEnd_6442147 : Nat := 3307917857920111803935611

theorem tailTrace_6442147 : CollatzResearch.WordTrace tailWord_6442147 prefixEnd_6442147 3307917857920111803935611 := by
  unfold tailWord_6442147
  simp only [CollatzResearch.WordTrace]
  refine ⟨234964404192209124958836695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156642936128139416639224463 234964404192209124958836695)
  ·
    refine ⟨352446606288313687438255043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234964404192209124958836695 352446606288313687438255043)
    ·
      refine ⟨528669909432470531157382565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352446606288313687438255043 528669909432470531157382565)
      ·
        refine ⟨99125608018588224592009231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528669909432470531157382565 99125608018588224592009231)
        ·
          refine ⟨148688412027882336888013847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99125608018588224592009231 148688412027882336888013847)
          ·
            refine ⟨223032618041823505332020771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148688412027882336888013847 223032618041823505332020771)
            ·
              refine ⟨334548927062735257998031157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223032618041823505332020771 334548927062735257998031157)
              ·
                refine ⟨31363961912131430437315421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334548927062735257998031157 31363961912131430437315421)
                ·
                  refine ⟨11761485717049286413993283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31363961912131430437315421 11761485717049286413993283)
                  ·
                    refine ⟨17642228575573929620989925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11761485717049286413993283 17642228575573929620989925)
                    ·
                      refine ⟨3307917857920111803935611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17642228575573929620989925 3307917857920111803935611)
                      ·
                        rfl

theorem cell23_6442147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_6442147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442147 prefixEnd_6442147 := by exact prefixLift 6442147
  have htrace : WordTrace (prefixWord ++ tailWord_6442147) baseStart_6442147 baseEnd_6442147 := by
    simpa [prefixWord, tailWord_6442147, baseEnd_6442147] using wordTrace_append hprefix tailTrace_6442147
  have hstable : (prefixWord ++ tailWord_6442147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442147).length < 2 ^ (prefixWord ++ tailWord_6442147).sum := by decide
  have hdescent : baseEnd_6442147 < baseStart_6442147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442151 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_6442151 : Nat := 118140960795 + 6442151 * 2 ^ 59
def prefixEnd_6442151 : Nat := 4983230072969 + 3 ^ 40 * 6442151 * 2
def baseEnd_6442151 : Nat := 3307919911842729788285593

theorem tailTrace_6442151 : CollatzResearch.WordTrace tailWord_6442151 prefixEnd_6442151 3307919911842729788285593 := by
  unfold tailWord_6442151
  simp only [CollatzResearch.WordTrace]
  refine ⟨234964550084194633641982307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156643033389463089094654871 234964550084194633641982307)
  ·
    refine ⟨352446825126291950462973461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234964550084194633641982307 352446825126291950462973461)
    ·
      refine ⟨16520944927794935177951881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 352446825126291950462973461 16520944927794935177951881)
      ·
        refine ⟨12390708695846201383463911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16520944927794935177951881 12390708695846201383463911)
        ·
          refine ⟨18586063043769302075195867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390708695846201383463911 18586063043769302075195867)
          ·
            refine ⟨27879094565653953112793801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18586063043769302075195867 27879094565653953112793801)
            ·
              refine ⟨20909320924240464834595351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27879094565653953112793801 20909320924240464834595351)
              ·
                refine ⟨31363981386360697251893027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20909320924240464834595351 31363981386360697251893027)
                ·
                  refine ⟨47045972079541045877839541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31363981386360697251893027 47045972079541045877839541)
                  ·
                    refine ⟨4410559882456973051047457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47045972079541045877839541 4410559882456973051047457)
                    ·
                      refine ⟨3307919911842729788285593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410559882456973051047457 3307919911842729788285593)
                      ·
                        rfl

theorem cell23_6442151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_6442151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442151 prefixEnd_6442151 := by exact prefixLift 6442151
  have htrace : WordTrace (prefixWord ++ tailWord_6442151) baseStart_6442151 baseEnd_6442151 := by
    simpa [prefixWord, tailWord_6442151, baseEnd_6442151] using wordTrace_append hprefix tailTrace_6442151
  have hstable : (prefixWord ++ tailWord_6442151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442151).length < 2 ^ (prefixWord ++ tailWord_6442151).sum := by decide
  have hdescent : baseEnd_6442151 < baseStart_6442151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442182 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_6442182 : Nat := 118140960795 + 6442182 * 2 ^ 59
def prefixEnd_6442182 : Nat := 4983230072969 + 3 ^ 40 * 6442182 * 2
def baseEnd_6442182 : Nat := 367548425527002129666439

theorem tailTrace_6442182 : CollatzResearch.WordTrace tailWord_6442182 prefixEnd_6442182 367548425527002129666439 := by
  unfold tailWord_6442182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7342677523346322685511275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156643787164721550624240533 7342677523346322685511275)
  ·
    refine ⟨11014016285019484028266913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7342677523346322685511275 11014016285019484028266913)
    ·
      refine ⟨8260512213764613021200185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11014016285019484028266913 8260512213764613021200185)
      ·
        refine ⟨6195384160323459765900139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8260512213764613021200185 6195384160323459765900139)
        ·
          refine ⟨9293076240485189648850209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195384160323459765900139 9293076240485189648850209)
          ·
            refine ⟨6969807180363892236637657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9293076240485189648850209 6969807180363892236637657)
            ·
              refine ⟨5227355385272919177478243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6969807180363892236637657 5227355385272919177478243)
              ·
                refine ⟨7841033077909378766217365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227355385272919177478243 7841033077909378766217365)
                ·
                  refine ⟨367548425527002129666439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7841033077909378766217365 367548425527002129666439)
                  ·
                    rfl

theorem cell23_6442182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_6442182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442182 prefixEnd_6442182 := by exact prefixLift 6442182
  have htrace : WordTrace (prefixWord ++ tailWord_6442182) baseStart_6442182 baseEnd_6442182 := by
    simpa [prefixWord, tailWord_6442182, baseEnd_6442182] using wordTrace_append hprefix tailTrace_6442182
  have hstable : (prefixWord ++ tailWord_6442182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442182).length < 2 ^ (prefixWord ++ tailWord_6442182).sum := by decide
  have hdescent : baseEnd_6442182 < baseStart_6442182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442194 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6442194 : Nat := 118140960795 + 6442194 * 2 ^ 59
def prefixEnd_6442194 : Nat := 4983230072969 + 3 ^ 40 * 6442194 * 2
def baseEnd_6442194 : Nat := 3307941991510873120047895

theorem tailTrace_6442194 : CollatzResearch.WordTrace tailWord_6442194 prefixEnd_6442194 3307941991510873120047895 := by
  unfold tailWord_6442194
  simp only [CollatzResearch.WordTrace]
  refine ⟨58741529605759712996449409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156644078948692567990531757 58741529605759712996449409)
  ·
    refine ⟨44056147204319784747337057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58741529605759712996449409 44056147204319784747337057)
    ·
      refine ⟨33042110403239838560502793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44056147204319784747337057 33042110403239838560502793)
      ·
        refine ⟨24781582802429878920377095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33042110403239838560502793 24781582802429878920377095)
        ·
          refine ⟨37172374203644818380565643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24781582802429878920377095 37172374203644818380565643)
          ·
            refine ⟨55758561305467227570848465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37172374203644818380565643 55758561305467227570848465)
            ·
              refine ⟨41818920979100420678136349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55758561305467227570848465 41818920979100420678136349)
              ·
                refine ⟨15682095367162657754301131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41818920979100420678136349 15682095367162657754301131)
                ·
                  refine ⟨23523143050743986631451697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15682095367162657754301131 23523143050743986631451697)
                  ·
                    refine ⟨17642357288057989973588773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23523143050743986631451697 17642357288057989973588773)
                    ·
                      refine ⟨3307941991510873120047895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17642357288057989973588773 3307941991510873120047895)
                      ·
                        rfl

theorem cell23_6442194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6442194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442194 prefixEnd_6442194 := by exact prefixLift 6442194
  have htrace : WordTrace (prefixWord ++ tailWord_6442194) baseStart_6442194 baseEnd_6442194 := by
    simpa [prefixWord, tailWord_6442194, baseEnd_6442194] using wordTrace_append hprefix tailTrace_6442194
  have hstable : (prefixWord ++ tailWord_6442194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442194).length < 2 ^ (prefixWord ++ tailWord_6442194).sum := by decide
  have hdescent : baseEnd_6442194 < baseStart_6442194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442198 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6442198 : Nat := 118140960795 + 6442198 * 2 ^ 59
def prefixEnd_6442198 : Nat := 4983230072969 + 3 ^ 40 * 6442198 * 2
def baseEnd_6442198 : Nat := 3307944045433491104397877

theorem tailTrace_6442198 : CollatzResearch.WordTrace tailWord_6442198 prefixEnd_6442198 3307944045433491104397877 := by
  unfold tailWord_6442198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14685391519689022541808953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156644176210016240445962165 14685391519689022541808953)
  ·
    refine ⟨11014043639766766906356715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14685391519689022541808953 11014043639766766906356715)
    ·
      refine ⟨16521065459650150359535073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014043639766766906356715 16521065459650150359535073)
      ·
        refine ⟨12390799094737612769651305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16521065459650150359535073 12390799094737612769651305)
        ·
          refine ⟨9293099321053209577238479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12390799094737612769651305 9293099321053209577238479)
          ·
            refine ⟨13939648981579814365857719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9293099321053209577238479 13939648981579814365857719)
            ·
              refine ⟨20909473472369721548786579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13939648981579814365857719 20909473472369721548786579)
              ·
                refine ⟨31364210208554582323179869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20909473472369721548786579 31364210208554582323179869)
                ·
                  refine ⟨11761578828207968371192451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31364210208554582323179869 11761578828207968371192451)
                  ·
                    refine ⟨17642368242311952556788677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11761578828207968371192451 17642368242311952556788677)
                    ·
                      refine ⟨3307944045433491104397877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17642368242311952556788677 3307944045433491104397877)
                      ·
                        rfl

theorem cell23_6442198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6442198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442198 prefixEnd_6442198 := by exact prefixLift 6442198
  have htrace : WordTrace (prefixWord ++ tailWord_6442198) baseStart_6442198 baseEnd_6442198 := by
    simpa [prefixWord, tailWord_6442198, baseEnd_6442198] using wordTrace_append hprefix tailTrace_6442198
  have hstable : (prefixWord ++ tailWord_6442198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442198).length < 2 ^ (prefixWord ++ tailWord_6442198).sum := by decide
  have hdescent : baseEnd_6442198 < baseStart_6442198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442218 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_6442218 : Nat := 118140960795 + 6442218 * 2 ^ 59
def prefixEnd_6442218 : Nat := 4983230072969 + 3 ^ 40 * 6442218 * 2
def baseEnd_6442218 : Nat := 3307954315046581026147785

theorem tailTrace_6442218 : CollatzResearch.WordTrace tailWord_6442218 prefixEnd_6442218 3307954315046581026147785 := by
  unfold tailWord_6442218
  simp only [CollatzResearch.WordTrace]
  refine ⟨58741748443737976021167827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156644662516634602723114205 58741748443737976021167827)
  ·
    refine ⟨88112622665606964031751741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58741748443737976021167827 88112622665606964031751741)
    ·
      refine ⟨33042233499602611511906903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88112622665606964031751741 33042233499602611511906903)
      ·
        refine ⟨49563350249403917267860355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33042233499602611511906903 49563350249403917267860355)
        ·
          refine ⟨74345025374105875901790533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49563350249403917267860355 74345025374105875901790533)
          ·
            refine ⟨13939692257644851731585725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74345025374105875901790533 13939692257644851731585725)
            ·
              refine ⟨5227384596616819399344647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13939692257644851731585725 5227384596616819399344647)
              ·
                refine ⟨7841076894925229099016971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227384596616819399344647 7841076894925229099016971)
                ·
                  refine ⟨11761615342387843648525457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841076894925229099016971 11761615342387843648525457)
                  ·
                    refine ⟨8821211506790882736394093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11761615342387843648525457 8821211506790882736394093)
                    ·
                      refine ⟨3307954315046581026147785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821211506790882736394093 3307954315046581026147785)
                      ·
                        rfl

theorem cell23_6442218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_6442218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442218 prefixEnd_6442218 := by exact prefixLift 6442218
  have htrace : WordTrace (prefixWord ++ tailWord_6442218) baseStart_6442218 baseEnd_6442218 := by
    simpa [prefixWord, tailWord_6442218, baseEnd_6442218] using wordTrace_append hprefix tailTrace_6442218
  have hstable : (prefixWord ++ tailWord_6442218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442218).length < 2 ^ (prefixWord ++ tailWord_6442218).sum := by decide
  have hdescent : baseEnd_6442218 < baseStart_6442218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442241 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_6442241 : Nat := 118140960795 + 6442241 * 2 ^ 59
def prefixEnd_6442241 : Nat := 4983230072969 + 3 ^ 40 * 6442241 * 2
def baseEnd_6442241 : Nat := 3307966125101634436160179

theorem tailTrace_6442241 : CollatzResearch.WordTrace tailWord_6442241 prefixEnd_6442241 3307966125101634436160179 := by
  unfold tailWord_6442241
  simp only [CollatzResearch.WordTrace]
  refine ⟨234967832653868579012758577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156645221769245719341839051 234967832653868579012758577)
  ·
    refine ⟨176225874490401434259568933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234967832653868579012758577 176225874490401434259568933)
    ·
      refine ⟨33042351466950268923669175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176225874490401434259568933 33042351466950268923669175)
      ·
        refine ⟨49563527200425403385503763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33042351466950268923669175 49563527200425403385503763)
        ·
          refine ⟨74345290800638105078255645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49563527200425403385503763 74345290800638105078255645)
          ·
            refine ⟨27879484050239289404345867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74345290800638105078255645 27879484050239289404345867)
            ·
              refine ⟨41819226075358934106518801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27879484050239289404345867 41819226075358934106518801)
              ·
                refine ⟨31364419556519200579889101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41819226075358934106518801 31364419556519200579889101)
                ·
                  refine ⟨11761657333694700217458413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31364419556519200579889101 11761657333694700217458413)
                  ·
                    refine ⟨4410621500135512581546905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11761657333694700217458413 4410621500135512581546905)
                    ·
                      refine ⟨3307966125101634436160179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410621500135512581546905 3307966125101634436160179)
                      ·
                        rfl

theorem cell23_6442241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_6442241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442241 prefixEnd_6442241 := by exact prefixLift 6442241
  have htrace : WordTrace (prefixWord ++ tailWord_6442241) baseStart_6442241 baseEnd_6442241 := by
    simpa [prefixWord, tailWord_6442241, baseEnd_6442241] using wordTrace_append hprefix tailTrace_6442241
  have hstable : (prefixWord ++ tailWord_6442241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442241).length < 2 ^ (prefixWord ++ tailWord_6442241).sum := by decide
  have hdescent : baseEnd_6442241 < baseStart_6442241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442267 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4]
def baseStart_6442267 : Nat := 118140960795 + 6442267 * 2 ^ 59
def prefixEnd_6442267 : Nat := 4983230072969 + 3 ^ 40 * 6442267 * 2
def baseEnd_6442267 : Nat := 3307979475598651334435059

theorem tailTrace_6442267 : CollatzResearch.WordTrace tailWord_6442267 prefixEnd_6442267 3307979475598651334435059 := by
  unfold tailWord_6442267
  simp only [CollatzResearch.WordTrace]
  refine ⟨234968780951774385453205055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156645853967849590302136703 234968780951774385453205055)
  ·
    refine ⟨352453171427661578179807583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234968780951774385453205055 352453171427661578179807583)
    ·
      refine ⟨528679757141492367269711375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352453171427661578179807583 528679757141492367269711375)
      ·
        refine ⟨793019635712238550904567063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528679757141492367269711375 793019635712238550904567063)
        ·
          refine ⟨1189529453568357826356850595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793019635712238550904567063 1189529453568357826356850595)
          ·
            refine ⟨1784294180352536739535275893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189529453568357826356850595 1784294180352536739535275893)
            ·
              refine ⟨167277579408050319331432115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1784294180352536739535275893 167277579408050319331432115)
              ·
                refine ⟨250916369112075478997148173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167277579408050319331432115 250916369112075478997148173)
                ·
                  refine ⟨94093638417028304623930565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250916369112075478997148173 94093638417028304623930565)
                  ·
                    refine ⟨17642557203192807116986981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94093638417028304623930565 17642557203192807116986981)
                    ·
                      refine ⟨3307979475598651334435059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17642557203192807116986981 3307979475598651334435059)
                      ·
                        rfl

theorem cell23_6442267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_6442267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442267 prefixEnd_6442267 := by exact prefixLift 6442267
  have htrace : WordTrace (prefixWord ++ tailWord_6442267) baseStart_6442267 baseEnd_6442267 := by
    simpa [prefixWord, tailWord_6442267, baseEnd_6442267] using wordTrace_append hprefix tailTrace_6442267
  have hstable : (prefixWord ++ tailWord_6442267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442267).length < 2 ^ (prefixWord ++ tailWord_6442267).sum := by decide
  have hdescent : baseEnd_6442267 < baseStart_6442267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442275 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 1, 3, 2]
def baseStart_6442275 : Nat := 118140960795 + 6442275 * 2 ^ 59
def prefixEnd_6442275 : Nat := 4983230072969 + 3 ^ 40 * 6442275 * 2
def baseEnd_6442275 : Nat := 3307983583443887303135023

theorem tailTrace_6442275 : CollatzResearch.WordTrace tailWord_6442275 prefixEnd_6442275 3307983583443887303135023 := by
  unfold tailWord_6442275
  simp only [CollatzResearch.WordTrace]
  refine ⟨234969072735745402819496279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156646048490496935212997519 234969072735745402819496279)
  ·
    refine ⟨352453609103618104229244419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234969072735745402819496279 352453609103618104229244419)
    ·
      refine ⟨528680413655427156343866629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352453609103618104229244419 528680413655427156343866629)
      ·
        refine ⟨99127577560392591814474993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528680413655427156343866629 99127577560392591814474993)
        ·
          refine ⟨74345683170294443860856245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99127577560392591814474993 74345683170294443860856245)
          ·
            refine ⟨6969907797215104111955273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74345683170294443860856245 6969907797215104111955273)
            ·
              refine ⟨5227430847911328083966455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6969907797215104111955273 5227430847911328083966455)
              ·
                refine ⟨7841146271866992125949683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227430847911328083966455 7841146271866992125949683)
                ·
                  refine ⟨11761719407800488188924525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841146271866992125949683 11761719407800488188924525)
                  ·
                    refine ⟨4410644777925183070846697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11761719407800488188924525 4410644777925183070846697)
                    ·
                      refine ⟨3307983583443887303135023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410644777925183070846697 3307983583443887303135023)
                      ·
                        rfl

theorem cell23_6442275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_6442275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442275 prefixEnd_6442275 := by exact prefixLift 6442275
  have htrace : WordTrace (prefixWord ++ tailWord_6442275) baseStart_6442275 baseEnd_6442275 := by
    simpa [prefixWord, tailWord_6442275, baseEnd_6442275] using wordTrace_append hprefix tailTrace_6442275
  have hstable : (prefixWord ++ tailWord_6442275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442275).length < 2 ^ (prefixWord ++ tailWord_6442275).sum := by decide
  have hdescent : baseEnd_6442275 < baseStart_6442275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442304 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_6442304 : Nat := 118140960795 + 6442304 * 2 ^ 59
def prefixEnd_6442304 : Nat := 4983230072969 + 3 ^ 40 * 6442304 * 2
def baseEnd_6442304 : Nat := 3307998474382867689672389

theorem tailTrace_6442304 : CollatzResearch.WordTrace tailWord_6442304 prefixEnd_6442304 3307998474382867689672389 := by
  unfold tailWord_6442304
  simp only [CollatzResearch.WordTrace]
  refine ⟨117485065226320170386150983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156646753635093560514867977 117485065226320170386150983)
  ·
    refine ⟨176227597839480255579226475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117485065226320170386150983 176227597839480255579226475)
    ·
      refine ⟨264341396759220383368839713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176227597839480255579226475 264341396759220383368839713)
      ·
        refine ⟨198256047569415287526629785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264341396759220383368839713 198256047569415287526629785)
        ·
          refine ⟨148692035677061465644972339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198256047569415287526629785 148692035677061465644972339)
          ·
            refine ⟨223038053515592198467458509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148692035677061465644972339 223038053515592198467458509)
            ·
              refine ⟨83639270068347074425296941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223038053515592198467458509 83639270068347074425296941)
              ·
                refine ⟨31364726275630152909486353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83639270068347074425296941 31364726275630152909486353)
                ·
                  refine ⟨23523544706722614682114765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31364726275630152909486353 23523544706722614682114765)
                  ·
                    refine ⟨8821329265020980505793037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23523544706722614682114765 8821329265020980505793037)
                    ·
                      refine ⟨3307998474382867689672389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821329265020980505793037 3307998474382867689672389)
                      ·
                        rfl

theorem cell23_6442304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_6442304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442304 prefixEnd_6442304 := by exact prefixLift 6442304
  have htrace : WordTrace (prefixWord ++ tailWord_6442304) baseStart_6442304 baseEnd_6442304 := by
    simpa [prefixWord, tailWord_6442304, baseEnd_6442304] using wordTrace_append hprefix tailTrace_6442304
  have hstable : (prefixWord ++ tailWord_6442304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442304).length < 2 ^ (prefixWord ++ tailWord_6442304).sum := by decide
  have hdescent : baseEnd_6442304 < baseStart_6442304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442305 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6442305 : Nat := 118140960795 + 6442305 * 2 ^ 59
def prefixEnd_6442305 : Nat := 4983230072969 + 3 ^ 40 * 6442305 * 2
def baseEnd_6442305 : Nat := 3307998987863522185759885

theorem tailTrace_6442305 : CollatzResearch.WordTrace tailWord_6442305 prefixEnd_6442305 3307998987863522185759885 := by
  unfold tailWord_6442305
  simp only [CollatzResearch.WordTrace]
  refine ⟨234970166925636717943088369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156646777950424478628725579 234970166925636717943088369)
  ·
    refine ⟨176227625194227538457316277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234970166925636717943088369 176227625194227538457316277)
    ·
      refine ⟨16521339861958831730373401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176227625194227538457316277 16521339861958831730373401)
      ·
        refine ⟨12391004896469123797780051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16521339861958831730373401 12391004896469123797780051)
        ·
          refine ⟨18586507344703685696670077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12391004896469123797780051 18586507344703685696670077)
          ·
            refine ⟨6969940254263882136251279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18586507344703685696670077 6969940254263882136251279)
            ·
              refine ⟨10454910381395823204376919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6969940254263882136251279 10454910381395823204376919)
              ·
                refine ⟨15682365572093734806565379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10454910381395823204376919 15682365572093734806565379)
                ·
                  refine ⟨23523548358140602209848069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15682365572093734806565379 23523548358140602209848069)
                  ·
                    refine ⟨4410665317151362914346513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23523548358140602209848069 4410665317151362914346513)
                    ·
                      refine ⟨3307998987863522185759885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410665317151362914346513 3307998987863522185759885)
                      ·
                        rfl

theorem cell23_6442305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6442305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442305 prefixEnd_6442305 := by exact prefixLift 6442305
  have htrace : WordTrace (prefixWord ++ tailWord_6442305) baseStart_6442305 baseEnd_6442305 := by
    simpa [prefixWord, tailWord_6442305, baseEnd_6442305] using wordTrace_append hprefix tailTrace_6442305
  have hstable : (prefixWord ++ tailWord_6442305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442305).length < 2 ^ (prefixWord ++ tailWord_6442305).sum := by decide
  have hdescent : baseEnd_6442305 < baseStart_6442305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442324 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_6442324 : Nat := 118140960795 + 6442324 * 2 ^ 59
def prefixEnd_6442324 : Nat := 4983230072969 + 3 ^ 40 * 6442324 * 2
def baseEnd_6442324 : Nat := 1102669581331985870474099

theorem tailTrace_6442324 : CollatzResearch.WordTrace tailWord_6442324 prefixEnd_6442324 1102669581331985870474099 := by
  unfold tailWord_6442324
  simp only [CollatzResearch.WordTrace]
  refine ⟨117485429956283942094015013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156647239941711922792020017 117485429956283942094015013)
  ·
    refine ⟨22028518116803239142627815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117485429956283942094015013 22028518116803239142627815)
    ·
      refine ⟨33042777175204858713941723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22028518116803239142627815 33042777175204858713941723)
      ·
        refine ⟨49564165762807288070912585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33042777175204858713941723 49564165762807288070912585)
        ·
          refine ⟨37173124322105466053184439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49564165762807288070912585 37173124322105466053184439)
          ·
            refine ⟨55759686483158199079776659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37173124322105466053184439 55759686483158199079776659)
            ·
              refine ⟨83639529724737298619664989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55759686483158199079776659 83639529724737298619664989)
              ·
                refine ⟨31364823646776486982374371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83639529724737298619664989 31364823646776486982374371)
                ·
                  refine ⟨47047235470164730473561557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31364823646776486982374371 47047235470164730473561557)
                  ·
                    refine ⟨1102669581331985870474099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47047235470164730473561557 1102669581331985870474099)
                    ·
                      rfl

theorem cell23_6442324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_6442324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442324 prefixEnd_6442324 := by exact prefixLift 6442324
  have htrace : WordTrace (prefixWord ++ tailWord_6442324) baseStart_6442324 baseEnd_6442324 := by
    simpa [prefixWord, tailWord_6442324, baseEnd_6442324] using wordTrace_append hprefix tailTrace_6442324
  have hstable : (prefixWord ++ tailWord_6442324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442324).length < 2 ^ (prefixWord ++ tailWord_6442324).sum := by decide
  have hdescent : baseEnd_6442324 < baseStart_6442324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442361 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 2, 4, 2]
def baseStart_6442361 : Nat := 118140960795 + 6442361 * 2 ^ 59
def prefixEnd_6442361 : Nat := 4983230072969 + 3 ^ 40 * 6442361 * 2
def baseEnd_6442361 : Nat := 3308027742780173966659627

theorem tailTrace_6442361 : CollatzResearch.WordTrace tailWord_6442361 prefixEnd_6442361 3308027742780173966659627 := by
  unfold tailWord_6442361
  simp only [CollatzResearch.WordTrace]
  refine ⟨234972209413433839507126937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156648139608955893004751291 234972209413433839507126937)
  ·
    refine ⟨176229157060075379630345203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234972209413433839507126937 176229157060075379630345203)
    ·
      refine ⟨264343735590113069445517805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176229157060075379630345203 264343735590113069445517805)
      ·
        refine ⟨99128900846292401042069177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264343735590113069445517805 99128900846292401042069177)
        ·
          refine ⟨74346675634719300781551883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99128900846292401042069177 74346675634719300781551883)
          ·
            refine ⟨111520013452078951172327825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74346675634719300781551883 111520013452078951172327825)
            ·
              refine ⟨83640010089059213379245869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111520013452078951172327825 83640010089059213379245869)
              ·
                refine ⟨31365003783397205017217201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83640010089059213379245869 31365003783397205017217201)
                ·
                  refine ⟨23523752837547903762912901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31365003783397205017217201 23523752837547903762912901)
                  ·
                    refine ⟨4410703657040231955546169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23523752837547903762912901 4410703657040231955546169)
                    ·
                      refine ⟨3308027742780173966659627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410703657040231955546169 3308027742780173966659627)
                      ·
                        rfl

theorem cell23_6442361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_6442361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442361 prefixEnd_6442361 := by exact prefixLift 6442361
  have htrace : WordTrace (prefixWord ++ tailWord_6442361) baseStart_6442361 baseEnd_6442361 := by
    simpa [prefixWord, tailWord_6442361, baseEnd_6442361] using wordTrace_append hprefix tailTrace_6442361
  have hstable : (prefixWord ++ tailWord_6442361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442361).length < 2 ^ (prefixWord ++ tailWord_6442361).sum := by decide
  have hdescent : baseEnd_6442361 < baseStart_6442361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442404 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_6442404 : Nat := 118140960795 + 6442404 * 2 ^ 59
def prefixEnd_6442404 : Nat := 4983230072969 + 3 ^ 40 * 6442404 * 2
def baseEnd_6442404 : Nat := 3308049822448317298421929

theorem tailTrace_6442404 : CollatzResearch.WordTrace tailWord_6442404 prefixEnd_6442404 3308049822448317298421929 := by
  unfold tailWord_6442404
  simp only [CollatzResearch.WordTrace]
  refine ⟨117486888876139028925471133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156649185168185371900628177 117486888876139028925471133)
  ·
    refine ⟨44057583328552135847051675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117486888876139028925471133 44057583328552135847051675)
    ·
      refine ⟨66086374992828203770577513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44057583328552135847051675 66086374992828203770577513)
      ·
        refine ⟨49564781244621152827933135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66086374992828203770577513 49564781244621152827933135)
        ·
          refine ⟨74347171866931729241899703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49564781244621152827933135 74347171866931729241899703)
          ·
            refine ⟨111520757800397593862849555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74347171866931729241899703 111520757800397593862849555)
            ·
              refine ⟨167281136700596390794274333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111520757800397593862849555 167281136700596390794274333)
              ·
                refine ⟨62730426262723646547852875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167281136700596390794274333 62730426262723646547852875)
                ·
                  refine ⟨94095639394085469821779313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62730426262723646547852875 94095639394085469821779313)
                  ·
                    refine ⟨70571729545564102366334485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94095639394085469821779313 70571729545564102366334485)
                    ·
                      refine ⟨3308049822448317298421929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70571729545564102366334485 3308049822448317298421929)
                      ·
                        rfl

theorem cell23_6442404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_6442404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442404 prefixEnd_6442404 := by exact prefixLift 6442404
  have htrace : WordTrace (prefixWord ++ tailWord_6442404) baseStart_6442404 baseEnd_6442404 := by
    simpa [prefixWord, tailWord_6442404, baseEnd_6442404] using wordTrace_append hprefix tailTrace_6442404
  have hstable : (prefixWord ++ tailWord_6442404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442404).length < 2 ^ (prefixWord ++ tailWord_6442404).sum := by decide
  have hdescent : baseEnd_6442404 < baseStart_6442404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442471 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6442471 : Nat := 118140960795 + 6442471 * 2 ^ 59
def prefixEnd_6442471 : Nat := 4983230072969 + 3 ^ 40 * 6442471 * 2
def baseEnd_6442471 : Nat := 3308084225652168536284121

theorem tailTrace_6442471 : CollatzResearch.WordTrace tailWord_6442471 prefixEnd_6442471 3308084225652168536284121 := by
  unfold tailWord_6442471
  simp only [CollatzResearch.WordTrace]
  refine ⟨234976221443035328293631267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156650814295356885529087511 234976221443035328293631267)
  ·
    refine ⟨352464332164552992440446901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234976221443035328293631267 352464332164552992440446901)
    ·
      refine ⟨33043531140426843041291897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352464332164552992440446901 33043531140426843041291897)
      ·
        refine ⟨24782648355320132280968923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33043531140426843041291897 24782648355320132280968923)
        ·
          refine ⟨37173972532980198421453385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24782648355320132280968923 37173972532980198421453385)
          ·
            refine ⟨27880479399735148816090039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37173972532980198421453385 27880479399735148816090039)
            ·
              refine ⟨41820719099602723224135059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27880479399735148816090039 41820719099602723224135059)
              ·
                refine ⟨62731078649404084836202589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41820719099602723224135059 62731078649404084836202589)
                ·
                  refine ⟨23524154493526531813575971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62731078649404084836202589 23524154493526531813575971)
                  ·
                    refine ⟨35286231740289797720363957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23524154493526531813575971 35286231740289797720363957)
                    ·
                      refine ⟨3308084225652168536284121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35286231740289797720363957 3308084225652168536284121)
                      ·
                        rfl

theorem cell23_6442471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6442471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442471 prefixEnd_6442471 := by exact prefixLift 6442471
  have htrace : WordTrace (prefixWord ++ tailWord_6442471) baseStart_6442471 baseEnd_6442471 := by
    simpa [prefixWord, tailWord_6442471, baseEnd_6442471] using wordTrace_append hprefix tailTrace_6442471
  have hstable : (prefixWord ++ tailWord_6442471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442471).length < 2 ^ (prefixWord ++ tailWord_6442471).sum := by decide
  have hdescent : baseEnd_6442471 < baseStart_6442471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442481 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_6442481 : Nat := 118140960795 + 6442481 * 2 ^ 59
def prefixEnd_6442481 : Nat := 4983230072969 + 3 ^ 40 * 6442481 * 2
def baseEnd_6442481 : Nat := 3308089360458713497159075

theorem tailTrace_6442481 : CollatzResearch.WordTrace tailWord_6442481 prefixEnd_6442481 3308089360458713497159075 := by
  unfold tailWord_6442481
  simp only [CollatzResearch.WordTrace]
  refine ⟨234976586172999100001495297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156651057448666066667663531 234976586172999100001495297)
  ·
    refine ⟨176232439629749325001121473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234976586172999100001495297 176232439629749325001121473)
    ·
      refine ⟨132174329722311993750841105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176232439629749325001121473 132174329722311993750841105)
      ·
        refine ⟨99130747291733995313130829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132174329722311993750841105 99130747291733995313130829)
        ·
          refine ⟨37174030234400248242424061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99130747291733995313130829 37174030234400248242424061)
          ·
            refine ⟨13940261337900093090909023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37174030234400248242424061 13940261337900093090909023)
            ·
              refine ⟨20910392006850139636363535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13940261337900093090909023 20910392006850139636363535)
              ·
                refine ⟨31365588010275209454545303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20910392006850139636363535 31365588010275209454545303)
                ·
                  refine ⟨47048382015412814181817955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31365588010275209454545303 47048382015412814181817955)
                  ·
                    refine ⟨70572573023119221272726933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47048382015412814181817955 70572573023119221272726933)
                    ·
                      refine ⟨3308089360458713497159075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70572573023119221272726933 3308089360458713497159075)
                      ·
                        rfl

theorem cell23_6442481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_6442481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442481 prefixEnd_6442481 := by exact prefixLift 6442481
  have htrace : WordTrace (prefixWord ++ tailWord_6442481) baseStart_6442481 baseEnd_6442481 := by
    simpa [prefixWord, tailWord_6442481, baseEnd_6442481] using wordTrace_append hprefix tailTrace_6442481
  have hstable : (prefixWord ++ tailWord_6442481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442481).length < 2 ^ (prefixWord ++ tailWord_6442481).sum := by decide
  have hdescent : baseEnd_6442481 < baseStart_6442481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442485 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6442485 : Nat := 118140960795 + 6442485 * 2 ^ 59
def prefixEnd_6442485 : Nat := 4983230072969 + 3 ^ 40 * 6442485 * 2
def baseEnd_6442485 : Nat := 3308091414381331481509057

theorem tailTrace_6442485 : CollatzResearch.WordTrace tailWord_6442485 prefixEnd_6442485 3308091414381331481509057 := by
  unfold tailWord_6442485
  simp only [CollatzResearch.WordTrace]
  refine ⟨234976732064984608684640909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156651154709989739123093939 234976732064984608684640909)
  ·
    refine ⟨88116274524369228256740341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234976732064984608684640909 88116274524369228256740341)
    ·
      refine ⟨8260900736659615149069407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88116274524369228256740341 8260900736659615149069407)
      ·
        refine ⟨12391351104989422723604111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8260900736659615149069407 12391351104989422723604111)
        ·
          refine ⟨18587026657484134085406167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12391351104989422723604111 18587026657484134085406167)
          ·
            refine ⟨27880539986226201128109251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18587026657484134085406167 27880539986226201128109251)
            ·
              refine ⟨41820809979339301692163877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27880539986226201128109251 41820809979339301692163877)
              ·
                refine ⟨7841401871126119067280727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41820809979339301692163877 7841401871126119067280727)
                ·
                  refine ⟨11762102806689178600921091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841401871126119067280727 11762102806689178600921091)
                  ·
                    refine ⟨17643154210033767901381637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11762102806689178600921091 17643154210033767901381637)
                    ·
                      refine ⟨3308091414381331481509057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17643154210033767901381637 3308091414381331481509057)
                      ·
                        rfl

theorem cell23_6442485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6442485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442485 prefixEnd_6442485 := by exact prefixLift 6442485
  have htrace : WordTrace (prefixWord ++ tailWord_6442485) baseStart_6442485 baseEnd_6442485 := by
    simpa [prefixWord, tailWord_6442485, baseEnd_6442485] using wordTrace_append hprefix tailTrace_6442485
  have hstable : (prefixWord ++ tailWord_6442485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442485).length < 2 ^ (prefixWord ++ tailWord_6442485).sum := by decide
  have hdescent : baseEnd_6442485 < baseStart_6442485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442488 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_6442488 : Nat := 118140960795 + 6442488 * 2 ^ 59
def prefixEnd_6442488 : Nat := 4983230072969 + 3 ^ 40 * 6442488 * 2
def baseEnd_6442488 : Nat := 3308092954823294969771543

theorem tailTrace_6442488 : CollatzResearch.WordTrace tailWord_6442488 prefixEnd_6442488 3308092954823294969771543 := by
  unfold tailWord_6442488
  simp only [CollatzResearch.WordTrace]
  refine ⟨117488420741986870098500059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156651227655982493464666745 117488420741986870098500059)
  ·
    refine ⟨176232631112980305147750089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117488420741986870098500059 176232631112980305147750089)
    ·
      refine ⟨132174473334735228860812567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176232631112980305147750089 132174473334735228860812567)
      ·
        refine ⟨198261710002102843291218851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132174473334735228860812567 198261710002102843291218851)
        ·
          refine ⟨297392565003154264936828277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198261710002102843291218851 297392565003154264936828277)
          ·
            refine ⟨27880552969045712337827651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297392565003154264936828277 27880552969045712337827651)
            ·
              refine ⟨41820829453568568506741477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27880552969045712337827651 41820829453568568506741477)
              ·
                refine ⟨7841405522544106595014027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41820829453568568506741477 7841405522544106595014027)
                ·
                  refine ⟨11762108283816159892521041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841405522544106595014027 11762108283816159892521041)
                  ·
                    refine ⟨8821581212862119919390781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11762108283816159892521041 8821581212862119919390781)
                    ·
                      refine ⟨3308092954823294969771543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821581212862119919390781 3308092954823294969771543)
                      ·
                        rfl

theorem cell23_6442488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_6442488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442488 prefixEnd_6442488 := by exact prefixLift 6442488
  have htrace : WordTrace (prefixWord ++ tailWord_6442488) baseStart_6442488 baseEnd_6442488 := by
    simpa [prefixWord, tailWord_6442488, baseEnd_6442488] using wordTrace_append hprefix tailTrace_6442488
  have hstable : (prefixWord ++ tailWord_6442488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442488).length < 2 ^ (prefixWord ++ tailWord_6442488).sum := by decide
  have hdescent : baseEnd_6442488 < baseStart_6442488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442501 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_6442501 : Nat := 118140960795 + 6442501 * 2 ^ 59
def prefixEnd_6442501 : Nat := 4983230072969 + 3 ^ 40 * 6442501 * 2
def baseEnd_6442501 : Nat := 3308099630071803418908983

theorem tailTrace_6442501 : CollatzResearch.WordTrace tailWord_6442501 prefixEnd_6442501 3308099630071803418908983 := by
  unfold tailWord_6442501
  simp only [CollatzResearch.WordTrace]
  refine ⟨234977315632926643417223357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156651543755284428944815571 234977315632926643417223357)
  ·
    refine ⟨88116493362347491281458759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234977315632926643417223357 88116493362347491281458759)
    ·
      refine ⟨132174740043521236922188139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88116493362347491281458759 132174740043521236922188139)
      ·
        refine ⟨198262110065281855383282209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132174740043521236922188139 198262110065281855383282209)
        ·
          refine ⟨148696582548961391537461657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198262110065281855383282209 148696582548961391537461657)
          ·
            refine ⟨111522436911721043653096243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148696582548961391537461657 111522436911721043653096243)
            ·
              refine ⟨167283655367581565479644365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111522436911721043653096243 167283655367581565479644365)
              ·
                refine ⟨62731370762843087054866637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167283655367581565479644365 62731370762843087054866637)
                ·
                  refine ⟨23524264036066157645574989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62731370762843087054866637 23524264036066157645574989)
                  ·
                    refine ⟨8821599013524809117090621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23524264036066157645574989 8821599013524809117090621)
                    ·
                      refine ⟨3308099630071803418908983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821599013524809117090621 3308099630071803418908983)
                      ·
                        rfl

theorem cell23_6442501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_6442501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442501 prefixEnd_6442501 := by exact prefixLift 6442501
  have htrace : WordTrace (prefixWord ++ tailWord_6442501) baseStart_6442501 baseEnd_6442501 := by
    simpa [prefixWord, tailWord_6442501, baseEnd_6442501] using wordTrace_append hprefix tailTrace_6442501
  have hstable : (prefixWord ++ tailWord_6442501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442501).length < 2 ^ (prefixWord ++ tailWord_6442501).sum := by decide
  have hdescent : baseEnd_6442501 < baseStart_6442501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442508 : List Nat := [2, 2, 1, 2, 6, 1, 9]
def baseStart_6442508 : Nat := 118140960795 + 6442508 * 2 ^ 59
def prefixEnd_6442508 : Nat := 4983230072969 + 3 ^ 40 * 6442508 * 2
def baseEnd_6442508 : Nat := 40840780548597344339771

theorem tailTrace_6442508 : CollatzResearch.WordTrace tailWord_6442508 prefixEnd_6442508 40840780548597344339771 := by
  unfold tailWord_6442508
  simp only [CollatzResearch.WordTrace]
  refine ⟨117488785471950641806364089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156651713962600855741818785 117488785471950641806364089)
  ·
    refine ⟨88116589103962981354773067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117488785471950641806364089 88116589103962981354773067)
    ·
      refine ⟨132174883655944472032159601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88116589103962981354773067 132174883655944472032159601)
      ·
        refine ⟨99131162741958354024119701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132174883655944472032159601 99131162741958354024119701)
        ·
          refine ⟨4646773253529297844880611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99131162741958354024119701 4646773253529297844880611)
          ·
            refine ⟨6970159880293946767320917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646773253529297844880611 6970159880293946767320917)
            ·
              refine ⟨40840780548597344339771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6970159880293946767320917 40840780548597344339771)
              ·
                rfl

theorem cell23_6442508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 9].length) (baseStart_6442508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442508 prefixEnd_6442508 := by exact prefixLift 6442508
  have htrace : WordTrace (prefixWord ++ tailWord_6442508) baseStart_6442508 baseEnd_6442508 := by
    simpa [prefixWord, tailWord_6442508, baseEnd_6442508] using wordTrace_append hprefix tailTrace_6442508
  have hstable : (prefixWord ++ tailWord_6442508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442508).length < 2 ^ (prefixWord ++ tailWord_6442508).sum := by decide
  have hdescent : baseEnd_6442508 < baseStart_6442508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442571 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4]
def baseStart_6442571 : Nat := 118140960795 + 6442571 * 2 ^ 59
def prefixEnd_6442571 : Nat := 4983230072969 + 3 ^ 40 * 6442571 * 2
def baseEnd_6442571 : Nat := 3308135573717618145033661

theorem tailTrace_6442571 : CollatzResearch.WordTrace tailWord_6442571 prefixEnd_6442571 3308135573717618145033661 := by
  unfold tailWord_6442571
  simp only [CollatzResearch.WordTrace]
  refine ⟨234979868742673045372271567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156653245828448696914847711 234979868742673045372271567)
  ·
    refine ⟨352469803114009568058407351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234979868742673045372271567 352469803114009568058407351)
    ·
      refine ⟨528704704671014352087611027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352469803114009568058407351 528704704671014352087611027)
      ·
        refine ⟨793057057006521528131416541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528704704671014352087611027 793057057006521528131416541)
        ·
          refine ⟨297396396377445573049281203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 793057057006521528131416541 297396396377445573049281203)
          ·
            refine ⟨446094594566168359573921805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297396396377445573049281203 446094594566168359573921805)
            ·
              refine ⟨167285472962313134840220677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446094594566168359573921805 167285472962313134840220677)
              ·
                refine ⟨31366026180433712782541377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167285472962313134840220677 31366026180433712782541377)
                ·
                  refine ⟨23524519635325284586906033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31366026180433712782541377 23524519635325284586906033)
                  ·
                    refine ⟨17643389726493963440179525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23524519635325284586906033 17643389726493963440179525)
                    ·
                      refine ⟨3308135573717618145033661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17643389726493963440179525 3308135573717618145033661)
                      ·
                        rfl

theorem cell23_6442571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_6442571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442571 prefixEnd_6442571 := by exact prefixLift 6442571
  have htrace : WordTrace (prefixWord ++ tailWord_6442571) baseStart_6442571 baseEnd_6442571 := by
    simpa [prefixWord, tailWord_6442571, baseEnd_6442571] using wordTrace_append hprefix tailTrace_6442571
  have hstable : (prefixWord ++ tailWord_6442571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442571).length < 2 ^ (prefixWord ++ tailWord_6442571).sum := by decide
  have hdescent : baseEnd_6442571 < baseStart_6442571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442578 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_6442578 : Nat := 118140960795 + 6442578 * 2 ^ 59
def prefixEnd_6442578 : Nat := 4983230072969 + 3 ^ 40 * 6442578 * 2
def baseEnd_6442578 : Nat := 3308139168082199617646129

theorem tailTrace_6442578 : CollatzResearch.WordTrace tailWord_6442578 prefixEnd_6442578 3308139168082199617646129 := by
  unfold tailWord_6442578
  simp only [CollatzResearch.WordTrace]
  refine ⟨58745031013411921391944097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156653416035765123711850925 58745031013411921391944097)
  ·
    refine ⟨44058773260058941043958073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58745031013411921391944097 44058773260058941043958073)
    ·
      refine ⟨33044079945044205782968555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44058773260058941043958073 33044079945044205782968555)
      ·
        refine ⟨49566119917566308674452833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33044079945044205782968555 49566119917566308674452833)
        ·
          refine ⟨37174589938174731505839625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49566119917566308674452833 37174589938174731505839625)
          ·
            refine ⟨27880942453631048629379719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37174589938174731505839625 27880942453631048629379719)
            ·
              refine ⟨41821413680446572944069579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27880942453631048629379719 41821413680446572944069579)
              ·
                refine ⟨62732120520669859416104369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41821413680446572944069579 62732120520669859416104369)
                ·
                  refine ⟨47049090390502394562078277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62732120520669859416104369 47049090390502394562078277)
                  ·
                    refine ⟨8821704448219198980389677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47049090390502394562078277 8821704448219198980389677)
                    ·
                      refine ⟨3308139168082199617646129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821704448219198980389677 3308139168082199617646129)
                      ·
                        rfl

theorem cell23_6442578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_6442578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442578 prefixEnd_6442578 := by exact prefixLift 6442578
  have htrace : WordTrace (prefixWord ++ tailWord_6442578) baseStart_6442578 baseEnd_6442578 := by
    simpa [prefixWord, tailWord_6442578, baseEnd_6442578] using wordTrace_append hprefix tailTrace_6442578
  have hstable : (prefixWord ++ tailWord_6442578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442578).length < 2 ^ (prefixWord ++ tailWord_6442578).sum := by decide
  have hdescent : baseEnd_6442578 < baseStart_6442578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442581 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 7]
def baseStart_6442581 : Nat := 118140960795 + 6442581 * 2 ^ 59
def prefixEnd_6442581 : Nat := 4983230072969 + 3 ^ 40 * 6442581 * 2
def baseEnd_6442581 : Nat := 367571189836018122878735

theorem tailTrace_6442581 : CollatzResearch.WordTrace tailWord_6442581 prefixEnd_6442581 367571189836018122878735 := by
  unfold tailWord_6442581
  simp only [CollatzResearch.WordTrace]
  refine ⟨234980233472636817080135597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156653488981757878053423731 234980233472636817080135597)
  ·
    refine ⟨88117587552238806405050849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234980233472636817080135597 88117587552238806405050849)
    ·
      refine ⟨66088190664179104803788137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88117587552238806405050849 66088190664179104803788137)
      ·
        refine ⟨49566142998134328602841103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66088190664179104803788137 49566142998134328602841103)
        ·
          refine ⟨74349214497201492904261655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49566142998134328602841103 74349214497201492904261655)
          ·
            refine ⟨111523821745802239356392483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74349214497201492904261655 111523821745802239356392483)
            ·
              refine ⟨167285732618703359034588725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111523821745802239356392483 167285732618703359034588725)
              ·
                refine ⟨15683037433003439909492693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167285732618703359034588725 15683037433003439909492693)
                ·
                  refine ⟨367571189836018122878735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15683037433003439909492693 367571189836018122878735)
                  ·
                    rfl

theorem cell23_6442581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_6442581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442581 prefixEnd_6442581 := by exact prefixLift 6442581
  have htrace : WordTrace (prefixWord ++ tailWord_6442581) baseStart_6442581 baseEnd_6442581 := by
    simpa [prefixWord, tailWord_6442581, baseEnd_6442581] using wordTrace_append hprefix tailTrace_6442581
  have hstable : (prefixWord ++ tailWord_6442581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442581).length < 2 ^ (prefixWord ++ tailWord_6442581).sum := by decide
  have hdescent : baseEnd_6442581 < baseStart_6442581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442588 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6442588 : Nat := 118140960795 + 6442588 * 2 ^ 59
def prefixEnd_6442588 : Nat := 4983230072969 + 3 ^ 40 * 6442588 * 2
def baseEnd_6442588 : Nat := 3308144302888744578521083

theorem tailTrace_6442588 : CollatzResearch.WordTrace tailWord_6442588 prefixEnd_6442588 3308144302888744578521083 := by
  unfold tailWord_6442588
  simp only [CollatzResearch.WordTrace]
  refine ⟨117490244391805728637820209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156653659189074304850426945 117490244391805728637820209)
  ·
    refine ⟨88117683293854296478365157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117490244391805728637820209 88117683293854296478365157)
    ·
      refine ⟨16522065617597680589693467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88117683293854296478365157 16522065617597680589693467)
      ·
        refine ⟨24783098426396520884540201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16522065617597680589693467 24783098426396520884540201)
        ·
          refine ⟨18587323819797390663405151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24783098426396520884540201 18587323819797390663405151)
          ·
            refine ⟨27880985729696085995107727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18587323819797390663405151 27880985729696085995107727)
            ·
              refine ⟨41821478594544128992661591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27880985729696085995107727 41821478594544128992661591)
              ·
                refine ⟨62732217891816193488992387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41821478594544128992661591 62732217891816193488992387)
                ·
                  refine ⟨94098326837724290233488581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62732217891816193488992387 94098326837724290233488581)
                  ·
                    refine ⟨17643436282073304418779109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94098326837724290233488581 17643436282073304418779109)
                    ·
                      refine ⟨3308144302888744578521083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17643436282073304418779109 3308144302888744578521083)
                      ·
                        rfl

theorem cell23_6442588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6442588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442588 prefixEnd_6442588 := by exact prefixLift 6442588
  have htrace : WordTrace (prefixWord ++ tailWord_6442588) baseStart_6442588 baseEnd_6442588 := by
    simpa [prefixWord, tailWord_6442588, baseEnd_6442588] using wordTrace_append hprefix tailTrace_6442588
  have hstable : (prefixWord ++ tailWord_6442588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442588).length < 2 ^ (prefixWord ++ tailWord_6442588).sum := by decide
  have hdescent : baseEnd_6442588 < baseStart_6442588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442618 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2]
def baseStart_6442618 : Nat := 118140960795 + 6442618 * 2 ^ 59
def prefixEnd_6442618 : Nat := 4983230072969 + 3 ^ 40 * 6442618 * 2
def baseEnd_6442618 : Nat := 3308159707308379461145945

theorem tailTrace_6442618 : CollatzResearch.WordTrace tailWord_6442618 prefixEnd_6442618 3308159707308379461145945 := by
  unfold tailWord_6442618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58745395743375693099808127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156654388649001848266155005 58745395743375693099808127)
  ·
    refine ⟨88118093615063539649712191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58745395743375693099808127 88118093615063539649712191)
    ·
      refine ⟨132177140422595309474568287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88118093615063539649712191 132177140422595309474568287)
      ·
        refine ⟨198265710633892964211852431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132177140422595309474568287 198265710633892964211852431)
        ·
          refine ⟨297398565950839446317778647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198265710633892964211852431 297398565950839446317778647)
          ·
            refine ⟨446097848926259169476667971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297398565950839446317778647 446097848926259169476667971)
            ·
              refine ⟨669146773389388754215001957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446097848926259169476667971 669146773389388754215001957)
              ·
                refine ⟨125465020010510391415312867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669146773389388754215001957 125465020010510391415312867)
                ·
                  refine ⟨188197530015765587122969301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125465020010510391415312867 188197530015765587122969301)
                  ·
                    refine ⟨4410879609744505948194593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188197530015765587122969301 4410879609744505948194593)
                    ·
                      refine ⟨3308159707308379461145945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410879609744505948194593 3308159707308379461145945)
                      ·
                        rfl

theorem cell23_6442618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_6442618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442618 prefixEnd_6442618 := by exact prefixLift 6442618
  have htrace : WordTrace (prefixWord ++ tailWord_6442618) baseStart_6442618 baseEnd_6442618 := by
    simpa [prefixWord, tailWord_6442618, baseEnd_6442618] using wordTrace_append hprefix tailTrace_6442618
  have hstable : (prefixWord ++ tailWord_6442618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442618).length < 2 ^ (prefixWord ++ tailWord_6442618).sum := by decide
  have hdescent : baseEnd_6442618 < baseStart_6442618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442648 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6442648 : Nat := 118140960795 + 6442648 * 2 ^ 59
def prefixEnd_6442648 : Nat := 4983230072969 + 3 ^ 40 * 6442648 * 2
def baseEnd_6442648 : Nat := 3308175111728014343770807

theorem tailTrace_6442648 : CollatzResearch.WordTrace tailWord_6442648 prefixEnd_6442648 3308175111728014343770807 := by
  unfold tailWord_6442648
  simp only [CollatzResearch.WordTrace]
  refine ⟨117491338581697043761412299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156655118108929391681883065 117491338581697043761412299)
  ·
    refine ⟨176237007872545565642118449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117491338581697043761412299 176237007872545565642118449)
    ·
      refine ⟨132177755904409174231588837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176237007872545565642118449 132177755904409174231588837)
      ·
        refine ⟨24783329232076720168422907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132177755904409174231588837 24783329232076720168422907)
        ·
          refine ⟨37174993848115080252634361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24783329232076720168422907 37174993848115080252634361)
          ·
            refine ⟨27881245386086310189475771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37174993848115080252634361 27881245386086310189475771)
            ·
              refine ⟨41821868079129465284213657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27881245386086310189475771 41821868079129465284213657)
              ·
                refine ⟨31366401059347098963160243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41821868079129465284213657 31366401059347098963160243)
                ·
                  refine ⟨47049601589020648444740365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31366401059347098963160243 47049601589020648444740365)
                  ·
                    refine ⟨17643600595882743166777637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47049601589020648444740365 17643600595882743166777637)
                    ·
                      refine ⟨3308175111728014343770807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17643600595882743166777637 3308175111728014343770807)
                      ·
                        rfl

theorem cell23_6442648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6442648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442648 prefixEnd_6442648 := by exact prefixLift 6442648
  have htrace : WordTrace (prefixWord ++ tailWord_6442648) baseStart_6442648 baseEnd_6442648 := by
    simpa [prefixWord, tailWord_6442648, baseEnd_6442648] using wordTrace_append hprefix tailTrace_6442648
  have hstable : (prefixWord ++ tailWord_6442648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442648).length < 2 ^ (prefixWord ++ tailWord_6442648).sum := by decide
  have hdescent : baseEnd_6442648 < baseStart_6442648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442668 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_6442668 : Nat := 118140960795 + 6442668 * 2 ^ 59
def prefixEnd_6442668 : Nat := 4983230072969 + 3 ^ 40 * 6442668 * 2
def baseEnd_6442668 : Nat := 3308185381341104265520715

theorem tailTrace_6442668 : CollatzResearch.WordTrace tailWord_6442668 prefixEnd_6442668 3308185381341104265520715 := by
  unfold tailWord_6442668
  simp only [CollatzResearch.WordTrace]
  refine ⟨117491703311660815469276329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156655604415547753959035105 117491703311660815469276329)
  ·
    refine ⟨88118777483745611601957247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117491703311660815469276329 88118777483745611601957247)
    ·
      refine ⟨132178166225618417402935871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88118777483745611601957247 132178166225618417402935871)
      ·
        refine ⟨198267249338427626104403807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132178166225618417402935871 198267249338427626104403807)
        ·
          refine ⟨297400874007641439156605711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198267249338427626104403807 297400874007641439156605711)
          ·
            refine ⟨446101311011462158734908567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297400874007641439156605711 446101311011462158734908567)
            ·
              refine ⟨669151966517193238102362851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446101311011462158734908567 669151966517193238102362851)
              ·
                refine ⟨1003727949775789857153544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669151966517193238102362851 1003727949775789857153544277)
                ·
                  refine ⟨11762436911435037388518097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1003727949775789857153544277 11762436911435037388518097)
                  ·
                    refine ⟨8821827683576278041388573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11762436911435037388518097 8821827683576278041388573)
                    ·
                      refine ⟨3308185381341104265520715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821827683576278041388573 3308185381341104265520715)
                      ·
                        rfl

theorem cell23_6442668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_6442668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442668 prefixEnd_6442668 := by exact prefixLift 6442668
  have htrace : WordTrace (prefixWord ++ tailWord_6442668) baseStart_6442668 baseEnd_6442668 := by
    simpa [prefixWord, tailWord_6442668, baseEnd_6442668] using wordTrace_append hprefix tailTrace_6442668
  have hstable : (prefixWord ++ tailWord_6442668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442668).length < 2 ^ (prefixWord ++ tailWord_6442668).sum := by decide
  have hdescent : baseEnd_6442668 < baseStart_6442668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442671 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 10]
def baseStart_6442671 : Nat := 118140960795 + 6442671 * 2 ^ 59
def prefixEnd_6442671 : Nat := 4983230072969 + 3 ^ 40 * 6442671 * 2
def baseEnd_6442671 : Nat := 367576324642563083753689

theorem tailTrace_6442671 : CollatzResearch.WordTrace tailWord_6442671 prefixEnd_6442671 367576324642563083753689 := by
  unfold tailWord_6442671
  simp only [CollatzResearch.WordTrace]
  refine ⟨234983516042310762450911867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156655677361540508300607911 234983516042310762450911867)
  ·
    refine ⟨352475274063466143676367801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234983516042310762450911867 352475274063466143676367801)
    ·
      refine ⟨264356455547599607757275851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352475274063466143676367801 264356455547599607757275851)
      ·
        refine ⟨396534683321399411635913777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264356455547599607757275851 396534683321399411635913777)
        ·
          refine ⟨297401012491049558726935333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396534683321399411635913777 297401012491049558726935333)
          ·
            refine ⟨55762689842071792261300375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297401012491049558726935333 55762689842071792261300375)
            ·
              refine ⟨83644034763107688391950563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55762689842071792261300375 83644034763107688391950563)
              ·
                refine ⟨125466052144661532587925845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83644034763107688391950563 125466052144661532587925845)
                ·
                  refine ⟨367576324642563083753689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 125466052144661532587925845 367576324642563083753689)
                  ·
                    rfl

theorem cell23_6442671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 10].length) (baseStart_6442671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442671 prefixEnd_6442671 := by exact prefixLift 6442671
  have htrace : WordTrace (prefixWord ++ tailWord_6442671) baseStart_6442671 baseEnd_6442671 := by
    simpa [prefixWord, tailWord_6442671, baseEnd_6442671] using wordTrace_append hprefix tailTrace_6442671
  have hstable : (prefixWord ++ tailWord_6442671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442671).length < 2 ^ (prefixWord ++ tailWord_6442671).sum := by decide
  have hdescent : baseEnd_6442671 < baseStart_6442671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442685 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_6442685 : Nat := 118140960795 + 6442685 * 2 ^ 59
def prefixEnd_6442685 : Nat := 4983230072969 + 3 ^ 40 * 6442685 * 2
def baseEnd_6442685 : Nat := 3308194110512230699008137

theorem tailTrace_6442685 : CollatzResearch.WordTrace tailWord_6442685 prefixEnd_6442685 3308194110512230699008137 := by
  unfold tailWord_6442685
  simp only [CollatzResearch.WordTrace]
  refine ⟨234984026664260042841921509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156656017776173361894614339 234984026664260042841921509)
  ·
    refine ⟨44059504999548758032860283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234984026664260042841921509 44059504999548758032860283)
    ·
      refine ⟨66089257499323137049290425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44059504999548758032860283 66089257499323137049290425)
      ·
        refine ⟨49566943124492352786967819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66089257499323137049290425 49566943124492352786967819)
        ·
          refine ⟨74350414686738529180451729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49566943124492352786967819 74350414686738529180451729)
          ·
            refine ⟨55762811015053896885338797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74350414686738529180451729 55762811015053896885338797)
            ·
              refine ⟨20911054130645211332002049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55762811015053896885338797 20911054130645211332002049)
              ·
                refine ⟨15683290597983908499001537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20911054130645211332002049 15683290597983908499001537)
                ·
                  refine ⟨11762467948487931374251153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15683290597983908499001537 11762467948487931374251153)
                  ·
                    refine ⟨8821850961365948530688365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11762467948487931374251153 8821850961365948530688365)
                    ·
                      refine ⟨3308194110512230699008137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821850961365948530688365 3308194110512230699008137)
                      ·
                        rfl

theorem cell23_6442685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_6442685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442685 prefixEnd_6442685 := by exact prefixLift 6442685
  have htrace : WordTrace (prefixWord ++ tailWord_6442685) baseStart_6442685 baseEnd_6442685 := by
    simpa [prefixWord, tailWord_6442685, baseEnd_6442685] using wordTrace_append hprefix tailTrace_6442685
  have hstable : (prefixWord ++ tailWord_6442685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442685).length < 2 ^ (prefixWord ++ tailWord_6442685).sum := by decide
  have hdescent : baseEnd_6442685 < baseStart_6442685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442688 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 6]
def baseStart_6442688 : Nat := 118140960795 + 6442688 * 2 ^ 59
def prefixEnd_6442688 : Nat := 4983230072969 + 3 ^ 40 * 6442688 * 2
def baseEnd_6442688 : Nat := 367577294550466020807847

theorem tailTrace_6442688 : CollatzResearch.WordTrace tailWord_6442688 prefixEnd_6442688 367577294550466020807847 := by
  unfold tailWord_6442688
  simp only [CollatzResearch.WordTrace]
  refine ⟨117492068041624587177140359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156656090722166116236187145 117492068041624587177140359)
  ·
    refine ⟨176238102062436880765710539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117492068041624587177140359 176238102062436880765710539)
    ·
      refine ⟨264357153093655321148565809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176238102062436880765710539 264357153093655321148565809)
      ·
        refine ⟨198267864820241490861424357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264357153093655321148565809 198267864820241490861424357)
        ·
          refine ⟨37175224653795279536517067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198267864820241490861424357 37175224653795279536517067)
          ·
            refine ⟨55762836980692919304775601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37175224653795279536517067 55762836980692919304775601)
            ·
              refine ⟨41822127735519689478581701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55762836980692919304775601 41822127735519689478581701)
              ·
                refine ⟨7841648950409941777234069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41822127735519689478581701 7841648950409941777234069)
                ·
                  refine ⟨367577294550466020807847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7841648950409941777234069 367577294550466020807847)
                  ·
                    rfl

theorem cell23_6442688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_6442688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442688 prefixEnd_6442688 := by exact prefixLift 6442688
  have htrace : WordTrace (prefixWord ++ tailWord_6442688) baseStart_6442688 baseEnd_6442688 := by
    simpa [prefixWord, tailWord_6442688, baseEnd_6442688] using wordTrace_append hprefix tailTrace_6442688
  have hstable : (prefixWord ++ tailWord_6442688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442688).length < 2 ^ (prefixWord ++ tailWord_6442688).sum := by decide
  have hdescent : baseEnd_6442688 < baseStart_6442688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442705 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 6]
def baseStart_6442705 : Nat := 118140960795 + 6442705 * 2 ^ 59
def prefixEnd_6442705 : Nat := 4983230072969 + 3 ^ 40 * 6442705 * 2
def baseEnd_6442705 : Nat := 367578264458368957862005

theorem tailTrace_6442705 : CollatzResearch.WordTrace tailWord_6442705 prefixEnd_6442705 367578264458368957862005 := by
  unfold tailWord_6442705
  simp only [CollatzResearch.WordTrace]
  refine ⟨234984756124187586257649569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156656504082791724171766379 234984756124187586257649569)
  ·
    refine ⟨176238567093140689693237177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234984756124187586257649569 176238567093140689693237177)
    ·
      refine ⟨132178925319855517269927883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176238567093140689693237177 132178925319855517269927883)
      ·
        refine ⟨198268387979783275904891825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132178925319855517269927883 198268387979783275904891825)
        ·
          refine ⟨148701290984837456928668869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198268387979783275904891825 148701290984837456928668869)
          ·
            refine ⟨27881492059657023174125413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148701290984837456928668869 27881492059657023174125413)
            ·
              refine ⟨5227779761185691845148515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27881492059657023174125413 5227779761185691845148515)
              ·
                refine ⟨7841669641778537767722773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227779761185691845148515 7841669641778537767722773)
                ·
                  refine ⟨367578264458368957862005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7841669641778537767722773 367578264458368957862005)
                  ·
                    rfl

theorem cell23_6442705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 6].length) (baseStart_6442705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442705 prefixEnd_6442705 := by exact prefixLift 6442705
  have htrace : WordTrace (prefixWord ++ tailWord_6442705) baseStart_6442705 baseEnd_6442705 := by
    simpa [prefixWord, tailWord_6442705, baseEnd_6442705] using wordTrace_append hprefix tailTrace_6442705
  have hstable : (prefixWord ++ tailWord_6442705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442705).length < 2 ^ (prefixWord ++ tailWord_6442705).sum := by decide
  have hdescent : baseEnd_6442705 < baseStart_6442705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442748 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_6442748 : Nat := 118140960795 + 6442748 * 2 ^ 59
def prefixEnd_6442748 : Nat := 4983230072969 + 3 ^ 40 * 6442748 * 2
def baseEnd_6442748 : Nat := 1102742153264487984173449

theorem tailTrace_6442748 : CollatzResearch.WordTrace tailWord_6442748 prefixEnd_6442748 1102742153264487984173449 := by
  unfold tailWord_6442748
  simp only [CollatzResearch.WordTrace]
  refine ⟨117493162231515902300732449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156657549642021203067643265 117493162231515902300732449)
  ·
    refine ⟨88119871673636926725549337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117493162231515902300732449 88119871673636926725549337)
    ·
      refine ⟨66089903755227695044162003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88119871673636926725549337 66089903755227695044162003)
      ·
        refine ⟨99134855632841542566243005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66089903755227695044162003 99134855632841542566243005)
        ·
          refine ⟨37175570862315578462341127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99134855632841542566243005 37175570862315578462341127)
          ·
            refine ⟨55763356293473367693511691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37175570862315578462341127 55763356293473367693511691)
            ·
              refine ⟨83645034440210051540267537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55763356293473367693511691 83645034440210051540267537)
              ·
                refine ⟨62733775830157538655200653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83645034440210051540267537 62733775830157538655200653)
                ·
                  refine ⟨23525165936309076995700245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62733775830157538655200653 23525165936309076995700245)
                  ·
                    refine ⟨1102742153264487984173449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23525165936309076995700245 1102742153264487984173449)
                    ·
                      rfl

theorem cell23_6442748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_6442748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442748 prefixEnd_6442748 := by exact prefixLift 6442748
  have htrace : WordTrace (prefixWord ++ tailWord_6442748) baseStart_6442748 baseEnd_6442748 := by
    simpa [prefixWord, tailWord_6442748, baseEnd_6442748] using wordTrace_append hprefix tailTrace_6442748
  have hstable : (prefixWord ++ tailWord_6442748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442748).length < 2 ^ (prefixWord ++ tailWord_6442748).sum := by decide
  have hdescent : baseEnd_6442748 < baseStart_6442748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442785 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6442785 : Nat := 118140960795 + 6442785 * 2 ^ 59
def prefixEnd_6442785 : Nat := 4983230072969 + 3 ^ 40 * 6442785 * 2
def baseEnd_6442785 : Nat := 3308245458577680307757677

theorem tailTrace_6442785 : CollatzResearch.WordTrace tailWord_6442785 prefixEnd_6442785 3308245458577680307757677 := by
  unfold tailWord_6442785
  simp only [CollatzResearch.WordTrace]
  refine ⟨234987673963897759920561809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156658449309265173280374539 234987673963897759920561809)
  ·
    refine ⟨176240755472923319940421357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234987673963897759920561809 176240755472923319940421357)
    ·
      refine ⟨66090283302346244977658009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176240755472923319940421357 66090283302346244977658009)
      ·
        refine ⟨49567712476759683733243507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66090283302346244977658009 49567712476759683733243507)
        ·
          refine ⟨74351568715139525599865261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49567712476759683733243507 74351568715139525599865261)
          ·
            refine ⟨27881838268177322099949473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74351568715139525599865261 27881838268177322099949473)
            ·
              refine ⟨20911378701132991574962105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27881838268177322099949473 20911378701132991574962105)
              ·
                refine ⟨15683534025849743681221579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20911378701132991574962105 15683534025849743681221579)
                ·
                  refine ⟨23525301038774615521832369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15683534025849743681221579 23525301038774615521832369)
                  ·
                    refine ⟨17643975779080961641374277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23525301038774615521832369 17643975779080961641374277)
                    ·
                      refine ⟨3308245458577680307757677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17643975779080961641374277 3308245458577680307757677)
                      ·
                        rfl

theorem cell23_6442785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6442785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442785 prefixEnd_6442785 := by exact prefixLift 6442785
  have htrace : WordTrace (prefixWord ++ tailWord_6442785) baseStart_6442785 baseEnd_6442785 := by
    simpa [prefixWord, tailWord_6442785, baseEnd_6442785] using wordTrace_append hprefix tailTrace_6442785
  have hstable : (prefixWord ++ tailWord_6442785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442785).length < 2 ^ (prefixWord ++ tailWord_6442785).sum := by decide
  have hdescent : baseEnd_6442785 < baseStart_6442785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442789 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 1, 1, 4]
def baseStart_6442789 : Nat := 118140960795 + 6442789 * 2 ^ 59
def prefixEnd_6442789 : Nat := 4983230072969 + 3 ^ 40 * 6442789 * 2
def baseEnd_6442789 : Nat := 3308247512500298292107659

theorem tailTrace_6442789 : CollatzResearch.WordTrace tailWord_6442789 prefixEnd_6442789 3308247512500298292107659 := by
  unfold tailWord_6442789
  simp only [CollatzResearch.WordTrace]
  refine ⟨234987819855883268603707421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156658546570588845735804947 234987819855883268603707421)
  ·
    refine ⟨88120432445956225726390283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234987819855883268603707421 88120432445956225726390283)
    ·
      refine ⟨132180648668934338589585425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88120432445956225726390283 132180648668934338589585425)
      ·
        refine ⟨99135486501700753942189069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132180648668934338589585425 99135486501700753942189069)
        ·
          refine ⟨37175807438137782728320901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99135486501700753942189069 37175807438137782728320901)
          ·
            refine ⟨6970463894650834261560169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37175807438137782728320901 6970463894650834261560169)
            ·
              refine ⟨5227847920988125696170127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6970463894650834261560169 5227847920988125696170127)
              ·
                refine ⟨7841771881482188544255191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227847920988125696170127 7841771881482188544255191)
                ·
                  refine ⟨11762657822223282816382787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841771881482188544255191 11762657822223282816382787)
                  ·
                    refine ⟨17643986733334924224574181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11762657822223282816382787 17643986733334924224574181)
                    ·
                      refine ⟨3308247512500298292107659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17643986733334924224574181 3308247512500298292107659)
                      ·
                        rfl

theorem cell23_6442789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_6442789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442789 prefixEnd_6442789 := by exact prefixLift 6442789
  have htrace : WordTrace (prefixWord ++ tailWord_6442789) baseStart_6442789 baseEnd_6442789 := by
    simpa [prefixWord, tailWord_6442789, baseEnd_6442789] using wordTrace_append hprefix tailTrace_6442789
  have hstable : (prefixWord ++ tailWord_6442789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442789).length < 2 ^ (prefixWord ++ tailWord_6442789).sum := by decide
  have hdescent : baseEnd_6442789 < baseStart_6442789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442806 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6442806 : Nat := 118140960795 + 6442806 * 2 ^ 59
def prefixEnd_6442806 : Nat := 4983230072969 + 3 ^ 40 * 6442806 * 2
def baseEnd_6442806 : Nat := 3308256241671424725595081

theorem tailTrace_6442806 : CollatzResearch.WordTrace tailWord_6442806 prefixEnd_6442806 3308256241671424725595081 := by
  unfold tailWord_6442806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14686777493551355031692267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156658959931214453671384181 14686777493551355031692267)
  ·
    refine ⟨22030166240327032547538401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14686777493551355031692267 22030166240327032547538401)
    ·
      refine ⟨16522624680245274410653801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22030166240327032547538401 16522624680245274410653801)
      ·
        refine ⟨12391968510183955807990351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16522624680245274410653801 12391968510183955807990351)
        ·
          refine ⟨18587952765275933711985527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12391968510183955807990351 18587952765275933711985527)
          ·
            refine ⟨27881929147913900567978291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18587952765275933711985527 27881929147913900567978291)
            ·
              refine ⟨41822893721870850851967437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27881929147913900567978291 41822893721870850851967437)
              ·
                refine ⟨15683585145701569069487789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41822893721870850851967437 15683585145701569069487789)
                ·
                  refine ⟨5881344429638088401057921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15683585145701569069487789 5881344429638088401057921)
                  ·
                    refine ⟨4411008322228566300793441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5881344429638088401057921 4411008322228566300793441)
                    ·
                      refine ⟨3308256241671424725595081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411008322228566300793441 3308256241671424725595081)
                      ·
                        rfl

theorem cell23_6442806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6442806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442806 prefixEnd_6442806 := by exact prefixLift 6442806
  have htrace : WordTrace (prefixWord ++ tailWord_6442806) baseStart_6442806 baseEnd_6442806 := by
    simpa [prefixWord, tailWord_6442806, baseEnd_6442806] using wordTrace_append hprefix tailTrace_6442806
  have hstable : (prefixWord ++ tailWord_6442806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442806).length < 2 ^ (prefixWord ++ tailWord_6442806).sum := by decide
  have hdescent : baseEnd_6442806 < baseStart_6442806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442829 : List Nat := [1, 6, 1, 2, 1, 3, 2, 7]
def baseStart_6442829 : Nat := 118140960795 + 6442829 * 2 ^ 59
def prefixEnd_6442829 : Nat := 4983230072969 + 3 ^ 40 * 6442829 * 2
def baseEnd_6442829 : Nat := 122528446360239930948425

theorem tailTrace_6442829 : CollatzResearch.WordTrace tailWord_6442829 prefixEnd_6442829 122528446360239930948425 := by
  unfold tailWord_6442829
  simp only [CollatzResearch.WordTrace]
  refine ⟨234989278775738355435163541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156659519183825570290109027 234989278775738355435163541)
  ·
    refine ⟨11015122442612735411023291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234989278775738355435163541 11015122442612735411023291)
    ·
      refine ⟨16522683663919103116534937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11015122442612735411023291 16522683663919103116534937)
      ·
        refine ⟨12392012747939327337401203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16522683663919103116534937 12392012747939327337401203)
        ·
          refine ⟨18588019121908991006101805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12392012747939327337401203 18588019121908991006101805)
          ·
            refine ⟨6970507170715871627288177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18588019121908991006101805 6970507170715871627288177)
            ·
              refine ⟨5227880378036903720466133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6970507170715871627288177 5227880378036903720466133)
              ·
                refine ⟨122528446360239930948425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5227880378036903720466133 122528446360239930948425)
                ·
                  rfl

theorem cell23_6442829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 7].length) (baseStart_6442829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442829 prefixEnd_6442829 := by exact prefixLift 6442829
  have htrace : WordTrace (prefixWord ++ tailWord_6442829) baseStart_6442829 baseEnd_6442829 := by
    simpa [prefixWord, tailWord_6442829, baseEnd_6442829] using wordTrace_append hprefix tailTrace_6442829
  have hstable : (prefixWord ++ tailWord_6442829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442829).length < 2 ^ (prefixWord ++ tailWord_6442829).sum := by decide
  have hdescent : baseEnd_6442829 < baseStart_6442829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442865 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_6442865 : Nat := 118140960795 + 6442865 * 2 ^ 59
def prefixEnd_6442865 : Nat := 4983230072969 + 3 ^ 40 * 6442865 * 2
def baseEnd_6442865 : Nat := 3308286537030039994757309

theorem tailTrace_6442865 : CollatzResearch.WordTrace tailWord_6442865 prefixEnd_6442865 3308286537030039994757309 := by
  unfold tailWord_6442865
  simp only [CollatzResearch.WordTrace]
  refine ⟨234990591803607933583474049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156660394535738622388982699 234990591803607933583474049)
  ·
    refine ⟨176242943852705950187605537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234990591803607933583474049 176242943852705950187605537)
    ·
      refine ⟨132182207889529462640704153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176242943852705950187605537 132182207889529462640704153)
      ·
        refine ⟨99136655917147096980528115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132182207889529462640704153 99136655917147096980528115)
        ·
          refine ⟨148704983875720645470792173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99136655917147096980528115 148704983875720645470792173)
          ·
            refine ⟨55764368953395242051547065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148704983875720645470792173 55764368953395242051547065)
            ·
              refine ⟨41823276715046431538660299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55764368953395242051547065 41823276715046431538660299)
              ·
                refine ⟨62734915072569647307990449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41823276715046431538660299 62734915072569647307990449)
                ·
                  refine ⟨47051186304427235480992837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62734915072569647307990449 47051186304427235480992837)
                  ·
                    refine ⟨8822097432080106652686157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47051186304427235480992837 8822097432080106652686157)
                    ·
                      refine ⟨3308286537030039994757309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8822097432080106652686157 3308286537030039994757309)
                      ·
                        rfl

theorem cell23_6442865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_6442865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442865 prefixEnd_6442865 := by exact prefixLift 6442865
  have htrace : WordTrace (prefixWord ++ tailWord_6442865) baseStart_6442865 baseEnd_6442865 := by
    simpa [prefixWord, tailWord_6442865, baseEnd_6442865] using wordTrace_append hprefix tailTrace_6442865
  have hstable : (prefixWord ++ tailWord_6442865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442865).length < 2 ^ (prefixWord ++ tailWord_6442865).sum := by decide
  have hdescent : baseEnd_6442865 < baseStart_6442865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442913 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6442913 : Nat := 118140960795 + 6442913 * 2 ^ 59
def prefixEnd_6442913 : Nat := 4983230072969 + 3 ^ 40 * 6442913 * 2
def baseEnd_6442913 : Nat := 3308311184101455806957089

theorem tailTrace_6442913 : CollatzResearch.WordTrace tailWord_6442913 prefixEnd_6442913 3308311184101455806957089 := by
  unfold tailWord_6442913
  simp only [CollatzResearch.WordTrace]
  refine ⟨234992342507434037781221393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156661561671622691854147595 234992342507434037781221393)
  ·
    refine ⟨176244256880575528335916045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234992342507434037781221393 176244256880575528335916045)
    ·
      refine ⟨66091596330215823125968517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176244256880575528335916045 66091596330215823125968517)
      ·
        refine ⟨12392174311915466836119097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66091596330215823125968517 12392174311915466836119097)
        ·
          refine ⟨9294130733936600127089323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12392174311915466836119097 9294130733936600127089323)
          ·
            refine ⟨13941196100904900190633985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9294130733936600127089323 13941196100904900190633985)
            ·
              refine ⟨10455897075678675142975489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13941196100904900190633985 10455897075678675142975489)
              ·
                refine ⟨7841922806759006357231617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10455897075678675142975489 7841922806759006357231617)
                ·
                  refine ⟨5881442105069254767923713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7841922806759006357231617 5881442105069254767923713)
                  ·
                    refine ⟨4411081578801941075942785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5881442105069254767923713 4411081578801941075942785)
                    ·
                      refine ⟨3308311184101455806957089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411081578801941075942785 3308311184101455806957089)
                      ·
                        rfl

theorem cell23_6442913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6442913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442913 prefixEnd_6442913 := by exact prefixLift 6442913
  have htrace : WordTrace (prefixWord ++ tailWord_6442913) baseStart_6442913 baseEnd_6442913 := by
    simpa [prefixWord, tailWord_6442913, baseEnd_6442913] using wordTrace_append hprefix tailTrace_6442913
  have hstable : (prefixWord ++ tailWord_6442913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442913).length < 2 ^ (prefixWord ++ tailWord_6442913).sum := by decide
  have hdescent : baseEnd_6442913 < baseStart_6442913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442919 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 5]
def baseStart_6442919 : Nat := 118140960795 + 6442919 * 2 ^ 59
def prefixEnd_6442919 : Nat := 4983230072969 + 3 ^ 40 * 6442919 * 2
def baseEnd_6442919 : Nat := 367590473887264753720229

theorem tailTrace_6442919 : CollatzResearch.WordTrace tailWord_6442919 prefixEnd_6442919 367590473887264753720229 := by
  unfold tailWord_6442919
  simp only [CollatzResearch.WordTrace]
  refine ⟨234992561345412300805939811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156661707563608200537293207 234992561345412300805939811)
  ·
    refine ⟨352488842018118451208909717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234992561345412300805939811 352488842018118451208909717)
    ·
      refine ⟨16522914469599302400417643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 352488842018118451208909717 16522914469599302400417643)
      ·
        refine ⟨24784371704398953600626465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16522914469599302400417643 24784371704398953600626465)
        ·
          refine ⟨18588278778299215200469849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24784371704398953600626465 18588278778299215200469849)
          ·
            refine ⟨13941209083724411400352387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18588278778299215200469849 13941209083724411400352387)
            ·
              refine ⟨20911813625586617100528581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13941209083724411400352387 20911813625586617100528581)
              ·
                refine ⟨3920965054797490706349109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20911813625586617100528581 3920965054797490706349109)
                ·
                  refine ⟨367590473887264753720229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3920965054797490706349109 367590473887264753720229)
                  ·
                    rfl

theorem cell23_6442919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 5].length) (baseStart_6442919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442919 prefixEnd_6442919 := by exact prefixLift 6442919
  have htrace : WordTrace (prefixWord ++ tailWord_6442919) baseStart_6442919 baseEnd_6442919 := by
    simpa [prefixWord, tailWord_6442919, baseEnd_6442919] using wordTrace_append hprefix tailTrace_6442919
  have hstable : (prefixWord ++ tailWord_6442919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442919).length < 2 ^ (prefixWord ++ tailWord_6442919).sum := by decide
  have hdescent : baseEnd_6442919 < baseStart_6442919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442935 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_6442935 : Nat := 118140960795 + 6442935 * 2 ^ 59
def prefixEnd_6442935 : Nat := 4983230072969 + 3 ^ 40 * 6442935 * 2
def baseEnd_6442935 : Nat := 3308322480675854720881987

theorem tailTrace_6442935 : CollatzResearch.WordTrace tailWord_6442935 prefixEnd_6442935 3308322480675854720881987 := by
  unfold tailWord_6442935
  simp only [CollatzResearch.WordTrace]
  refine ⟨234993144913354335538522259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156662096608902890359014839 234993144913354335538522259)
  ·
    refine ⟨352489717370031503307783389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234993144913354335538522259 352489717370031503307783389)
    ·
      refine ⟨132183644013761813740418771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352489717370031503307783389 132183644013761813740418771)
      ·
        refine ⟨198275466020642720610628157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132183644013761813740418771 198275466020642720610628157)
        ·
          refine ⟨74353299757741020228985559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198275466020642720610628157 74353299757741020228985559)
          ·
            refine ⟨111529949636611530343478339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74353299757741020228985559 111529949636611530343478339)
            ·
              refine ⟨167294924454917295515217509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111529949636611530343478339 167294924454917295515217509)
              ·
                refine ⟨31367798335296992909103283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167294924454917295515217509 31367798335296992909103283)
                ·
                  refine ⟨47051697502945489363654925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31367798335296992909103283 47051697502945489363654925)
                  ·
                    refine ⟨17644386563604558511370597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47051697502945489363654925 17644386563604558511370597)
                    ·
                      refine ⟨3308322480675854720881987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17644386563604558511370597 3308322480675854720881987)
                      ·
                        rfl

theorem cell23_6442935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_6442935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442935 prefixEnd_6442935 := by exact prefixLift 6442935
  have htrace : WordTrace (prefixWord ++ tailWord_6442935) baseStart_6442935 baseEnd_6442935 := by
    simpa [prefixWord, tailWord_6442935, baseEnd_6442935] using wordTrace_append hprefix tailTrace_6442935
  have hstable : (prefixWord ++ tailWord_6442935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442935).length < 2 ^ (prefixWord ++ tailWord_6442935).sum := by decide
  have hdescent : baseEnd_6442935 < baseStart_6442935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442952 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_6442952 : Nat := 118140960795 + 6442952 * 2 ^ 59
def prefixEnd_6442952 : Nat := 4983230072969 + 3 ^ 40 * 6442952 * 2
def baseEnd_6442952 : Nat := 3308331209846981154369409

theorem tailTrace_6442952 : CollatzResearch.WordTrace tailWord_6442952 prefixEnd_6442952 3308331209846981154369409 := by
  unfold tailWord_6442952
  simp only [CollatzResearch.WordTrace]
  refine ⟨117496882477146373720945555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156662509969528498294594073 117496882477146373720945555)
  ·
    refine ⟨176245323715719560581418333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117496882477146373720945555 176245323715719560581418333)
    ·
      refine ⟨66091996393394835218031875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176245323715719560581418333 66091996393394835218031875)
      ·
        refine ⟨99137994590092252827047813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66091996393394835218031875 99137994590092252827047813)
        ·
          refine ⟨18588373985642297405071465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99137994590092252827047813 18588373985642297405071465)
          ·
            refine ⟨13941280489231723053803599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18588373985642297405071465 13941280489231723053803599)
            ·
              refine ⟨20911920733847584580705399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13941280489231723053803599 20911920733847584580705399)
              ·
                refine ⟨31367881100771376871058099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20911920733847584580705399 31367881100771376871058099)
                ·
                  refine ⟨47051821651157065306587149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31367881100771376871058099 47051821651157065306587149)
                  ·
                    refine ⟨17644433119183899489970181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47051821651157065306587149 17644433119183899489970181)
                    ·
                      refine ⟨3308331209846981154369409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17644433119183899489970181 3308331209846981154369409)
                      ·
                        rfl

theorem cell23_6442952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_6442952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442952 prefixEnd_6442952 := by exact prefixLift 6442952
  have htrace : WordTrace (prefixWord ++ tailWord_6442952) baseStart_6442952 baseEnd_6442952 := by
    simpa [prefixWord, tailWord_6442952, baseEnd_6442952] using wordTrace_append hprefix tailTrace_6442952
  have hstable : (prefixWord ++ tailWord_6442952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442952).length < 2 ^ (prefixWord ++ tailWord_6442952).sum := by decide
  have hdescent : baseEnd_6442952 < baseStart_6442952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442979 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 3, 4]
def baseStart_6442979 : Nat := 118140960795 + 6442979 * 2 ^ 59
def prefixEnd_6442979 : Nat := 4983230072969 + 3 ^ 40 * 6442979 * 2
def baseEnd_6442979 : Nat := 1102781691274884182910595

theorem tailTrace_6442979 : CollatzResearch.WordTrace tailWord_6442979 prefixEnd_6442979 1102781691274884182910595 := by
  unfold tailWord_6442979
  simp only [CollatzResearch.WordTrace]
  refine ⟨234994749725194931053123991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156663166483463287368749327 234994749725194931053123991)
  ·
    refine ⟨352492124587792396579685987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234994749725194931053123991 352492124587792396579685987)
    ·
      refine ⟨528738186881688594869528981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352492124587792396579685987 528738186881688594869528981)
      ·
        refine ⟨24784602510079152884509171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 528738186881688594869528981 24784602510079152884509171)
        ·
          refine ⟨37176903765118729326763757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24784602510079152884509171 37176903765118729326763757)
          ·
            refine ⟨13941338911919523497536409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37176903765118729326763757 13941338911919523497536409)
            ·
              refine ⟨10456004183939642623152307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13941338911919523497536409 10456004183939642623152307)
              ·
                refine ⟨15684006275909463934728461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10456004183939642623152307 15684006275909463934728461)
                ·
                  refine ⟨5881502353466048975523173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15684006275909463934728461 5881502353466048975523173)
                  ·
                    refine ⟨1102781691274884182910595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881502353466048975523173 1102781691274884182910595)
                    ·
                      rfl

theorem cell23_6442979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 4].length) (baseStart_6442979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442979 prefixEnd_6442979 := by exact prefixLift 6442979
  have htrace : WordTrace (prefixWord ++ tailWord_6442979) baseStart_6442979 baseEnd_6442979 := by
    simpa [prefixWord, tailWord_6442979, baseEnd_6442979] using wordTrace_append hprefix tailTrace_6442979
  have hstable : (prefixWord ++ tailWord_6442979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442979).length < 2 ^ (prefixWord ++ tailWord_6442979).sum := by decide
  have hdescent : baseEnd_6442979 < baseStart_6442979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443035 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 5, 6]
def baseStart_6443035 : Nat := 118140960795 + 6443035 * 2 ^ 59
def prefixEnd_6443035 : Nat := 4983230072969 + 3 ^ 40 * 6443035 * 2
def baseEnd_6443035 : Nat := 1102791276247101443210509

theorem tailTrace_6443035 : CollatzResearch.WordTrace tailWord_6443035 prefixEnd_6443035 1102791276247101443210509 := by
  unfold tailWord_6443035
  simp only [CollatzResearch.WordTrace]
  refine ⟨234996792212992052617162559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156664528141994701744775039 234996792212992052617162559)
  ·
    refine ⟨352495188319488078925743839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234996792212992052617162559 352495188319488078925743839)
    ·
      refine ⟨528742782479232118388615759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352495188319488078925743839 528742782479232118388615759)
      ·
        refine ⟨793114173718848177582923639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528742782479232118388615759 793114173718848177582923639)
        ·
          refine ⟨1189671260578272266374385459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793114173718848177582923639 1189671260578272266374385459)
          ·
            refine ⟨1784506890867408399561578189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189671260578272266374385459 1784506890867408399561578189)
            ·
              refine ⟨669190084075278149835591821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1784506890867408399561578189 669190084075278149835591821)
              ·
                refine ⟨250946281528229306188346933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669190084075278149835591821 250946281528229306188346933)
                ·
                  refine ⟨23526213893271497455157525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250946281528229306188346933 23526213893271497455157525)
                  ·
                    refine ⟨1102791276247101443210509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23526213893271497455157525 1102791276247101443210509)
                    ·
                      rfl

theorem cell23_6443035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_6443035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443035 prefixEnd_6443035 := by exact prefixLift 6443035
  have htrace : WordTrace (prefixWord ++ tailWord_6443035) baseStart_6443035 baseEnd_6443035 := by
    simpa [prefixWord, tailWord_6443035, baseEnd_6443035] using wordTrace_append hprefix tailTrace_6443035
  have hstable : (prefixWord ++ tailWord_6443035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443035).length < 2 ^ (prefixWord ++ tailWord_6443035).sum := by decide
  have hdescent : baseEnd_6443035 < baseStart_6443035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443036 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_6443036 : Nat := 118140960795 + 6443036 * 2 ^ 59
def prefixEnd_6443036 : Nat := 4983230072969 + 3 ^ 40 * 6443036 * 2
def baseEnd_6443036 : Nat := 3308374342221958825719023

theorem tailTrace_6443036 : CollatzResearch.WordTrace tailWord_6443036 prefixEnd_6443036 3308374342221958825719023 := by
  unfold tailWord_6443036
  simp only [CollatzResearch.WordTrace]
  refine ⟨117498414342994214893974481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156664552457325619858632641 117498414342994214893974481)
  ·
    refine ⟨88123810757245661170480861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117498414342994214893974481 88123810757245661170480861)
    ·
      refine ⟨33046429033967122938930323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88123810757245661170480861 33046429033967122938930323)
      ·
        refine ⟨49569643550950684408395485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33046429033967122938930323 49569643550950684408395485)
        ·
          refine ⟨18588616331606506653148307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49569643550950684408395485 18588616331606506653148307)
          ·
            refine ⟨27882924497409759979722461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18588616331606506653148307 27882924497409759979722461)
            ·
              refine ⟨10456096686528659992395923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27882924497409759979722461 10456096686528659992395923)
              ·
                refine ⟨15684145029792989988593885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10456096686528659992395923 15684145029792989988593885)
                ·
                  refine ⟨5881554386172371245722707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15684145029792989988593885 5881554386172371245722707)
                  ·
                    refine ⟨8822331579258556868584061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5881554386172371245722707 8822331579258556868584061)
                    ·
                      refine ⟨3308374342221958825719023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8822331579258556868584061 3308374342221958825719023)
                      ·
                        rfl

theorem cell23_6443036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_6443036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443036 prefixEnd_6443036 := by exact prefixLift 6443036
  have htrace : WordTrace (prefixWord ++ tailWord_6443036) baseStart_6443036 baseEnd_6443036 := by
    simpa [prefixWord, tailWord_6443036, baseEnd_6443036] using wordTrace_append hprefix tailTrace_6443036
  have hstable : (prefixWord ++ tailWord_6443036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443036).length < 2 ^ (prefixWord ++ tailWord_6443036).sum := by decide
  have hdescent : baseEnd_6443036 < baseStart_6443036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443052 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_6443052 : Nat := 118140960795 + 6443052 * 2 ^ 59
def prefixEnd_6443052 : Nat := 4983230072969 + 3 ^ 40 * 6443052 * 2
def baseEnd_6443052 : Nat := 1102794185970810254372983

theorem tailTrace_6443052 : CollatzResearch.WordTrace tailWord_6443052 prefixEnd_6443052 1102794185970810254372983 := by
  unfold tailWord_6443052
  simp only [CollatzResearch.WordTrace]
  refine ⟨117498706126965232260265705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156664941502620309680354273 117498706126965232260265705)
  ·
    refine ⟨88124029595223924195199279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117498706126965232260265705 88124029595223924195199279)
    ·
      refine ⟨132186044392835886292798919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88124029595223924195199279 132186044392835886292798919)
      ·
        refine ⟨198279066589253829439198379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132186044392835886292798919 198279066589253829439198379)
        ·
          refine ⟨297418599883880744158797569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198279066589253829439198379 297418599883880744158797569)
          ·
            refine ⟨223063949912910558119098177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297418599883880744158797569 223063949912910558119098177)
            ·
              refine ⟨167297962434682918589323633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223063949912910558119098177 167297962434682918589323633)
              ·
                refine ⟨125473471826012188941992725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167297962434682918589323633 125473471826012188941992725)
                ·
                  refine ⟨5881568991844321356655909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125473471826012188941992725 5881568991844321356655909)
                  ·
                    refine ⟨1102794185970810254372983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881568991844321356655909 1102794185970810254372983)
                    ·
                      rfl

theorem cell23_6443052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_6443052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443052 prefixEnd_6443052 := by exact prefixLift 6443052
  have htrace : WordTrace (prefixWord ++ tailWord_6443052) baseStart_6443052 baseEnd_6443052 := by
    simpa [prefixWord, tailWord_6443052, baseEnd_6443052] using wordTrace_append hprefix tailTrace_6443052
  have hstable : (prefixWord ++ tailWord_6443052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443052).length < 2 ^ (prefixWord ++ tailWord_6443052).sum := by decide
  have hdescent : baseEnd_6443052 < baseStart_6443052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443059 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 4]
def baseStart_6443059 : Nat := 118140960795 + 6443059 * 2 ^ 59
def prefixEnd_6443059 : Nat := 4983230072969 + 3 ^ 40 * 6443059 * 2
def baseEnd_6443059 : Nat := 3308386152277012235731417

theorem tailTrace_6443059 : CollatzResearch.WordTrace tailWord_6443059 prefixEnd_6443059 3308386152277012235731417 := by
  unfold tailWord_6443059
  simp only [CollatzResearch.WordTrace]
  refine ⟨234997667564905104716036231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156665111709936736477357487 234997667564905104716036231)
  ·
    refine ⟨352496501347357657074054347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234997667564905104716036231 352496501347357657074054347)
    ·
      refine ⟨528744752021036485611081521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352496501347357657074054347 528744752021036485611081521)
      ·
        refine ⟨396558564015777364208311141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528744752021036485611081521 396558564015777364208311141)
        ·
          refine ⟨74354730752958255789058339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 396558564015777364208311141 74354730752958255789058339)
          ·
            refine ⟨111532096129437383683587509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74354730752958255789058339 111532096129437383683587509)
            ·
              refine ⟨10456134012134754720336329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111532096129437383683587509 10456134012134754720336329)
              ·
                refine ⟨7842100509101066040252247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456134012134754720336329 7842100509101066040252247)
                ·
                  refine ⟨11763150763651599060378371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842100509101066040252247 11763150763651599060378371)
                  ·
                    refine ⟨17644726145477398590567557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11763150763651599060378371 17644726145477398590567557)
                    ·
                      refine ⟨3308386152277012235731417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17644726145477398590567557 3308386152277012235731417)
                      ·
                        rfl

theorem cell23_6443059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_6443059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443059 prefixEnd_6443059 := by exact prefixLift 6443059
  have htrace : WordTrace (prefixWord ++ tailWord_6443059) baseStart_6443059 baseEnd_6443059 := by
    simpa [prefixWord, tailWord_6443059, baseEnd_6443059] using wordTrace_append hprefix tailTrace_6443059
  have hstable : (prefixWord ++ tailWord_6443059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443059).length < 2 ^ (prefixWord ++ tailWord_6443059).sum := by decide
  have hdescent : baseEnd_6443059 < baseStart_6443059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443072 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_6443072 : Nat := 118140960795 + 6443072 * 2 ^ 59
def prefixEnd_6443072 : Nat := 4983230072969 + 3 ^ 40 * 6443072 * 2
def baseEnd_6443072 : Nat := 3308392827525520684868857

theorem tailTrace_6443072 : CollatzResearch.WordTrace tailWord_6443072 prefixEnd_6443072 3308392827525520684868857 := by
  unfold tailWord_6443072
  simp only [CollatzResearch.WordTrace]
  refine ⟨117499070856929003968129735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156665427809238671957506313 117499070856929003968129735)
  ·
    refine ⟨176248606285393505952194603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117499070856929003968129735 176248606285393505952194603)
    ·
      refine ⟨264372909428090258928291905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176248606285393505952194603 264372909428090258928291905)
      ·
        refine ⟨198279682071067694196218929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264372909428090258928291905 198279682071067694196218929)
        ·
          refine ⟨148709761553300770647164197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198279682071067694196218929 148709761553300770647164197)
          ·
            refine ⟨27883080291243894496343287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148709761553300770647164197 27883080291243894496343287)
            ·
              refine ⟨41824620436865841744514931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27883080291243894496343287 41824620436865841744514931)
              ·
                refine ⟨62736930655298762616772397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41824620436865841744514931 62736930655298762616772397)
                ·
                  refine ⟨23526348995737035981289649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62736930655298762616772397 23526348995737035981289649)
                  ·
                    refine ⟨17644761746802776985967237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23526348995737035981289649 17644761746802776985967237)
                    ·
                      refine ⟨3308392827525520684868857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17644761746802776985967237 3308392827525520684868857)
                      ·
                        rfl

theorem cell23_6443072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_6443072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443072 prefixEnd_6443072 := by exact prefixLift 6443072
  have htrace : WordTrace (prefixWord ++ tailWord_6443072) baseStart_6443072 baseEnd_6443072 := by
    simpa [prefixWord, tailWord_6443072, baseEnd_6443072] using wordTrace_append hprefix tailTrace_6443072
  have hstable : (prefixWord ++ tailWord_6443072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443072).length < 2 ^ (prefixWord ++ tailWord_6443072).sum := by decide
  have hdescent : baseEnd_6443072 < baseStart_6443072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443086 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_6443086 : Nat := 118140960795 + 6443086 * 2 ^ 59
def prefixEnd_6443086 : Nat := 4983230072969 + 3 ^ 40 * 6443086 * 2
def baseEnd_6443086 : Nat := 1102800005418227876697931

theorem tailTrace_6443086 : CollatzResearch.WordTrace tailWord_6443086 prefixEnd_6443086 1102800005418227876697931 := by
  unfold tailWord_6443086
  simp only [CollatzResearch.WordTrace]
  refine ⟨29374831541975911040908639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156665768223871525551512741 29374831541975911040908639)
  ·
    refine ⟨44062247312963866561362959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29374831541975911040908639 44062247312963866561362959)
    ·
      refine ⟨66093370969445799842044439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44062247312963866561362959 66093370969445799842044439)
      ·
        refine ⟨99140056454168699763066659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66093370969445799842044439 99140056454168699763066659)
        ·
          refine ⟨148710084681253049644599989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99140056454168699763066659 148710084681253049644599989)
          ·
            refine ⟨13941570438867473404181249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148710084681253049644599989 13941570438867473404181249)
            ·
              refine ⟨10456177829150605053135937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13941570438867473404181249 10456177829150605053135937)
              ·
                refine ⟨7842133371862953789851953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456177829150605053135937 7842133371862953789851953)
                ·
                  refine ⟨5881600028897215342388965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7842133371862953789851953 5881600028897215342388965)
                  ·
                    refine ⟨1102800005418227876697931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881600028897215342388965 1102800005418227876697931)
                    ·
                      rfl

theorem cell23_6443086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_6443086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443086 prefixEnd_6443086 := by exact prefixLift 6443086
  have htrace : WordTrace (prefixWord ++ tailWord_6443086) baseStart_6443086 baseEnd_6443086 := by
    simpa [prefixWord, tailWord_6443086, baseEnd_6443086] using wordTrace_append hprefix tailTrace_6443086
  have hstable : (prefixWord ++ tailWord_6443086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443086).length < 2 ^ (prefixWord ++ tailWord_6443086).sum := by decide
  have hdescent : baseEnd_6443086 < baseStart_6443086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443109 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_6443109 : Nat := 118140960795 + 6443109 * 2 ^ 59
def prefixEnd_6443109 : Nat := 4983230072969 + 3 ^ 40 * 6443109 * 2
def baseEnd_6443109 : Nat := 3308411826309737040106187

theorem tailTrace_6443109 : CollatzResearch.WordTrace tailWord_6443109 prefixEnd_6443109 3308411826309737040106187 := by
  unfold tailWord_6443109
  simp only [CollatzResearch.WordTrace]
  refine ⟨234999491214723963255356381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156666327476482642170237587 234999491214723963255356381)
  ·
    refine ⟨88124809205521486220758643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234999491214723963255356381 88124809205521486220758643)
    ·
      refine ⟨132187213808282229331137965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88124809205521486220758643 132187213808282229331137965)
      ·
        refine ⟨49570205178105835999176737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132187213808282229331137965 49570205178105835999176737)
        ·
          refine ⟨37177653883579376999382553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49570205178105835999176737 37177653883579376999382553)
          ·
            refine ⟨27883240412684532749536915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37177653883579376999382553 27883240412684532749536915)
            ·
              refine ⟨41824860619026799124305373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27883240412684532749536915 41824860619026799124305373)
              ·
                refine ⟨15684322732135049671614515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41824860619026799124305373 15684322732135049671614515)
                ·
                  refine ⟨23526484098202574507421773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15684322732135049671614515 23526484098202574507421773)
                  ·
                    refine ⟨8822431536825965440283165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23526484098202574507421773 8822431536825965440283165)
                    ·
                      refine ⟨3308411826309737040106187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8822431536825965440283165 3308411826309737040106187)
                      ·
                        rfl

theorem cell23_6443109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_6443109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443109 prefixEnd_6443109 := by exact prefixLift 6443109
  have htrace : WordTrace (prefixWord ++ tailWord_6443109) baseStart_6443109 baseEnd_6443109 := by
    simpa [prefixWord, tailWord_6443109, baseEnd_6443109] using wordTrace_append hprefix tailTrace_6443109
  have hstable : (prefixWord ++ tailWord_6443109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443109).length < 2 ^ (prefixWord ++ tailWord_6443109).sum := by decide
  have hdescent : baseEnd_6443109 < baseStart_6443109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443126 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6443126 : Nat := 118140960795 + 6443126 * 2 ^ 59
def prefixEnd_6443126 : Nat := 4983230072969 + 3 ^ 40 * 6443126 * 2
def baseEnd_6443126 : Nat := 3308420555480863473593609

theorem tailTrace_6443126 : CollatzResearch.WordTrace tailWord_6443126 prefixEnd_6443126 3308420555480863473593609 := by
  unfold tailWord_6443126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14687506953478898447420327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156666740837108250105816821 14687506953478898447420327)
  ·
    refine ⟨22031260430218347671130491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14687506953478898447420327 22031260430218347671130491)
    ·
      refine ⟨33046890645327521506695737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22031260430218347671130491 33046890645327521506695737)
      ·
        refine ⟨24785167983995641130021803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33046890645327521506695737 24785167983995641130021803)
        ·
          refine ⟨37177751975993461695032705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24785167983995641130021803 37177751975993461695032705)
          ·
            refine ⟨27883313981995096271274529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37177751975993461695032705 27883313981995096271274529)
            ·
              refine ⟨20912485486496322203455897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27883313981995096271274529 20912485486496322203455897)
              ·
                refine ⟨15684364114872241652591923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20912485486496322203455897 15684364114872241652591923)
                ·
                  refine ⟨23526546172308362478887885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15684364114872241652591923 23526546172308362478887885)
                  ·
                    refine ⟨8822454814615635929582957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23526546172308362478887885 8822454814615635929582957)
                    ·
                      refine ⟨3308420555480863473593609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8822454814615635929582957 3308420555480863473593609)
                      ·
                        rfl

theorem cell23_6443126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6443126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443126 prefixEnd_6443126 := by exact prefixLift 6443126
  have htrace : WordTrace (prefixWord ++ tailWord_6443126) baseStart_6443126 baseEnd_6443126 := by
    simpa [prefixWord, tailWord_6443126, baseEnd_6443126] using wordTrace_append hprefix tailTrace_6443126
  have hstable : (prefixWord ++ tailWord_6443126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443126).length < 2 ^ (prefixWord ++ tailWord_6443126).sum := by decide
  have hdescent : baseEnd_6443126 < baseStart_6443126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443160 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6443160 : Nat := 118140960795 + 6443160 * 2 ^ 59
def prefixEnd_6443160 : Nat := 4983230072969 + 3 ^ 40 * 6443160 * 2
def baseEnd_6443160 : Nat := 3308438013823116340568453

theorem tailTrace_6443160 : CollatzResearch.WordTrace tailWord_6443160 prefixEnd_6443160 3308438013823116340568453 := by
  unfold tailWord_6443160
  simp only [CollatzResearch.WordTrace]
  refine ⟨117500675668769599482731467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156667567558359465976975289 117500675668769599482731467)
  ·
    refine ⟨176251013503154399224097201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117500675668769599482731467 176251013503154399224097201)
    ·
      refine ⟨132188260127365799418072901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176251013503154399224097201 132188260127365799418072901)
      ·
        refine ⟨24785298773881087390888669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132188260127365799418072901 24785298773881087390888669)
        ·
          refine ⟨9294487040205407771583251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24785298773881087390888669 9294487040205407771583251)
          ·
            refine ⟨13941730560308111657374877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9294487040205407771583251 13941730560308111657374877)
            ·
              refine ⟨5228148960115541871515579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13941730560308111657374877 5228148960115541871515579)
              ·
                refine ⟨7842223440173312807273369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228148960115541871515579 7842223440173312807273369)
                ·
                  refine ⟨5881667580129984605455027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7842223440173312807273369 5881667580129984605455027)
                  ·
                    refine ⟨8822501370194976908182541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5881667580129984605455027 8822501370194976908182541)
                    ·
                      refine ⟨3308438013823116340568453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8822501370194976908182541 3308438013823116340568453)
                      ·
                        rfl

theorem cell23_6443160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6443160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443160 prefixEnd_6443160 := by exact prefixLift 6443160
  have htrace : WordTrace (prefixWord ++ tailWord_6443160) baseStart_6443160 baseEnd_6443160 := by
    simpa [prefixWord, tailWord_6443160, baseEnd_6443160] using wordTrace_append hprefix tailTrace_6443160
  have hstable : (prefixWord ++ tailWord_6443160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443160).length < 2 ^ (prefixWord ++ tailWord_6443160).sum := by decide
  have hdescent : baseEnd_6443160 < baseStart_6443160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443170 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_6443170 : Nat := 118140960795 + 6443170 * 2 ^ 59
def prefixEnd_6443170 : Nat := 4983230072969 + 3 ^ 40 * 6443170 * 2
def baseEnd_6443170 : Nat := 3308443148629661301443407

theorem tailTrace_6443170 : CollatzResearch.WordTrace tailWord_6443170 prefixEnd_6443170 3308443148629661301443407 := by
  unfold tailWord_6443170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58750429016875742668331741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156667810711668647115551309 58750429016875742668331741)
  ·
    refine ⟨22031410881328403500624403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58750429016875742668331741 22031410881328403500624403)
    ·
      refine ⟨33047116321992605250936605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22031410881328403500624403 33047116321992605250936605)
      ·
        refine ⟨12392668620747226969101227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33047116321992605250936605 12392668620747226969101227)
        ·
          refine ⟨18589002931120840453651841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12392668620747226969101227 18589002931120840453651841)
          ·
            refine ⟨13941752198340630340238881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18589002931120840453651841 13941752198340630340238881)
            ·
              refine ⟨10456314148755472755179161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13941752198340630340238881 10456314148755472755179161)
              ·
                refine ⟨7842235611566604566384371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456314148755472755179161 7842235611566604566384371)
                ·
                  refine ⟨11763353417349906849576557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842235611566604566384371 11763353417349906849576557)
                  ·
                    refine ⟨4411257531506215068591209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11763353417349906849576557 4411257531506215068591209)
                    ·
                      refine ⟨3308443148629661301443407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411257531506215068591209 3308443148629661301443407)
                      ·
                        rfl

theorem cell23_6443170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_6443170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443170 prefixEnd_6443170 := by exact prefixLift 6443170
  have htrace : WordTrace (prefixWord ++ tailWord_6443170) baseStart_6443170 baseEnd_6443170 := by
    simpa [prefixWord, tailWord_6443170, baseEnd_6443170] using wordTrace_append hprefix tailTrace_6443170
  have hstable : (prefixWord ++ tailWord_6443170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443170).length < 2 ^ (prefixWord ++ tailWord_6443170).sum := by decide
  have hdescent : baseEnd_6443170 < baseStart_6443170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443290 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4]
def baseStart_6443290 : Nat := 118140960795 + 6443290 * 2 ^ 59
def prefixEnd_6443290 : Nat := 4983230072969 + 3 ^ 40 * 6443290 * 2
def baseEnd_6443290 : Nat := 3308504766308200831942855

theorem tailTrace_6443290 : CollatzResearch.WordTrace tailWord_6443290 prefixEnd_6443290 3308504766308200831942855 := by
  unfold tailWord_6443290
  simp only [CollatzResearch.WordTrace]
  refine ⟨58751523206767057791923831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156670728551378820778463549 58751523206767057791923831)
  ·
    refine ⟨88127284810150586687885747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58751523206767057791923831 88127284810150586687885747)
    ·
      refine ⟨132190927215225880031828621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88127284810150586687885747 132190927215225880031828621)
      ·
        refine ⟨49571597705709705011935733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132190927215225880031828621 49571597705709705011935733)
        ·
          refine ⟨4647337284910284844868975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49571597705709705011935733 4647337284910284844868975)
          ·
            refine ⟨6971005927365427267303463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647337284910284844868975 6971005927365427267303463)
            ·
              refine ⟨10456508891048140900955195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971005927365427267303463 10456508891048140900955195)
              ·
                refine ⟨15684763336572211351432793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10456508891048140900955195 15684763336572211351432793)
                ·
                  refine ⟨11763572502429158513574595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15684763336572211351432793 11763572502429158513574595)
                  ·
                    refine ⟨17645358753643737770361893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11763572502429158513574595 17645358753643737770361893)
                    ·
                      refine ⟨3308504766308200831942855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17645358753643737770361893 3308504766308200831942855)
                      ·
                        rfl

theorem cell23_6443290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_6443290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443290 prefixEnd_6443290 := by exact prefixLift 6443290
  have htrace : WordTrace (prefixWord ++ tailWord_6443290) baseStart_6443290 baseEnd_6443290 := by
    simpa [prefixWord, tailWord_6443290, baseEnd_6443290] using wordTrace_append hprefix tailTrace_6443290
  have hstable : (prefixWord ++ tailWord_6443290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443290).length < 2 ^ (prefixWord ++ tailWord_6443290).sum := by decide
  have hdescent : baseEnd_6443290 < baseStart_6443290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443293 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6443293 : Nat := 118140960795 + 6443293 * 2 ^ 59
def prefixEnd_6443293 : Nat := 4983230072969 + 3 ^ 40 * 6443293 * 2
def baseEnd_6443293 : Nat := 3308506306750164320205341

theorem tailTrace_6443293 : CollatzResearch.WordTrace tailWord_6443293 prefixEnd_6443293 3308506306750164320205341 := by
  unfold tailWord_6443293
  simp only [CollatzResearch.WordTrace]
  refine ⟨235006202246057362680054533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156670801497371575120036355 235006202246057362680054533)
  ·
    refine ⟨44063662921135755502510225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235006202246057362680054533 44063662921135755502510225)
    ·
      refine ⟨33047747190851816626882669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44063662921135755502510225 33047747190851816626882669)
      ·
        refine ⟨12392905196569431235081001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33047747190851816626882669 12392905196569431235081001)
        ·
          refine ⟨9294678897427073426310751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12392905196569431235081001 9294678897427073426310751)
          ·
            refine ⟨13942018346140610139466127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9294678897427073426310751 13942018346140610139466127)
            ·
              refine ⟨20913027519210915209199191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13942018346140610139466127 20913027519210915209199191)
              ·
                refine ⟨31369541278816372813798787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20913027519210915209199191 31369541278816372813798787)
                ·
                  refine ⟨47054311918224559220698181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31369541278816372813798787 47054311918224559220698181)
                  ·
                    refine ⟨8822683484667104853880909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47054311918224559220698181 8822683484667104853880909)
                    ·
                      refine ⟨3308506306750164320205341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8822683484667104853880909 3308506306750164320205341)
                      ·
                        rfl

theorem cell23_6443293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6443293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443293 prefixEnd_6443293 := by exact prefixLift 6443293
  have htrace : WordTrace (prefixWord ++ tailWord_6443293) baseStart_6443293 baseEnd_6443293 := by
    simpa [prefixWord, tailWord_6443293, baseEnd_6443293] using wordTrace_append hprefix tailTrace_6443293
  have hstable : (prefixWord ++ tailWord_6443293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443293).length < 2 ^ (prefixWord ++ tailWord_6443293).sum := by decide
  have hdescent : baseEnd_6443293 < baseStart_6443293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443300 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_6443300 : Nat := 118140960795 + 6443300 * 2 ^ 59
def prefixEnd_6443300 : Nat := 4983230072969 + 3 ^ 40 * 6443300 * 2
def baseEnd_6443300 : Nat := 1102836633704915264272603

theorem tailTrace_6443300 : CollatzResearch.WordTrace tailWord_6443300 prefixEnd_6443300 1102836633704915264272603 := by
  unfold tailWord_6443300
  simp only [CollatzResearch.WordTrace]
  refine ⟨117503228778516001437779677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156670971704688001917039569 117503228778516001437779677)
  ·
    refine ⟨44063710791943500539167379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117503228778516001437779677 44063710791943500539167379)
    ·
      refine ⟨66095566187915250808751069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44063710791943500539167379 66095566187915250808751069)
      ·
        refine ⟨24785837320468219053281651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66095566187915250808751069 24785837320468219053281651)
        ·
          refine ⟨37178755980702328579922477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24785837320468219053281651 37178755980702328579922477)
          ·
            refine ⟨13942033492763373217470929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37178755980702328579922477 13942033492763373217470929)
            ·
              refine ⟨10456525119572529913103197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13942033492763373217470929 10456525119572529913103197)
              ·
                refine ⟨3921196919839698717413699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10456525119572529913103197 3921196919839698717413699)
                ·
                  refine ⟨5881795379759548076120549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921196919839698717413699 5881795379759548076120549)
                  ·
                    refine ⟨1102836633704915264272603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881795379759548076120549 1102836633704915264272603)
                    ·
                      rfl

theorem cell23_6443300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_6443300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443300 prefixEnd_6443300 := by exact prefixLift 6443300
  have htrace : WordTrace (prefixWord ++ tailWord_6443300) baseStart_6443300 baseEnd_6443300 := by
    simpa [prefixWord, tailWord_6443300, baseEnd_6443300] using wordTrace_append hprefix tailTrace_6443300
  have hstable : (prefixWord ++ tailWord_6443300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443300).length < 2 ^ (prefixWord ++ tailWord_6443300).sum := by decide
  have hdescent : baseEnd_6443300 < baseStart_6443300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443313 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 6]
def baseStart_6443313 : Nat := 118140960795 + 6443313 * 2 ^ 59
def prefixEnd_6443313 : Nat := 4983230072969 + 3 ^ 40 * 6443313 * 2
def baseEnd_6443313 : Nat := 367612952929250471328361

theorem tailTrace_6443313 : CollatzResearch.WordTrace tailWord_6443313 prefixEnd_6443313 367612952929250471328361 := by
  unfold tailWord_6443313
  simp only [CollatzResearch.WordTrace]
  refine ⟨235006931705984906095782593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156671287803989937397188395 235006931705984906095782593)
  ·
    refine ⟨176255198779488679571836945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235006931705984906095782593 176255198779488679571836945)
    ·
      refine ⟨132191399084616509678877709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176255198779488679571836945 132191399084616509678877709)
      ·
        refine ⟨49571774656731191129579141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132191399084616509678877709 49571774656731191129579141)
        ·
          refine ⟨9294707748137098336796089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49571774656731191129579141 9294707748137098336796089)
          ·
            refine ⟨6971030811102823752597067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9294707748137098336796089 6971030811102823752597067)
            ·
              refine ⟨10456546216654235628895601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971030811102823752597067 10456546216654235628895601)
              ·
                refine ⟨7842409662490676721671701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456546216654235628895601 7842409662490676721671701)
                ·
                  refine ⟨367612952929250471328361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7842409662490676721671701 367612952929250471328361)
                  ·
                    rfl

theorem cell23_6443313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 6].length) (baseStart_6443313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443313 prefixEnd_6443313 := by exact prefixLift 6443313
  have htrace : WordTrace (prefixWord ++ tailWord_6443313) baseStart_6443313 baseEnd_6443313 := by
    simpa [prefixWord, tailWord_6443313, baseEnd_6443313] using wordTrace_append hprefix tailTrace_6443313
  have hstable : (prefixWord ++ tailWord_6443313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443313).length < 2 ^ (prefixWord ++ tailWord_6443313).sum := by decide
  have hdescent : baseEnd_6443313 < baseStart_6443313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443316 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6443316 : Nat := 118140960795 + 6443316 * 2 ^ 59
def prefixEnd_6443316 : Nat := 4983230072969 + 3 ^ 40 * 6443316 * 2
def baseEnd_6443316 : Nat := 3308518116805217730217735

theorem tailTrace_6443316 : CollatzResearch.WordTrace tailWord_6443316 prefixEnd_6443316 3308518116805217730217735 := by
  unfold tailWord_6443316
  simp only [CollatzResearch.WordTrace]
  refine ⟨117503520562487018804070901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156671360749982691738761201 117503520562487018804070901)
  ·
    refine ⟨11015955052733158012881647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117503520562487018804070901 11015955052733158012881647)
    ·
      refine ⟨16523932579099737019322471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11015955052733158012881647 16523932579099737019322471)
      ·
        refine ⟨24785898868649605528983707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16523932579099737019322471 24785898868649605528983707)
        ·
          refine ⟨37178848302974408293475561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24785898868649605528983707 37178848302974408293475561)
          ·
            refine ⟨27884136227230806220106671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37178848302974408293475561 27884136227230806220106671)
            ·
              refine ⟨41826204340846209330160007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27884136227230806220106671 41826204340846209330160007)
              ·
                refine ⟨62739306511269313995240011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41826204340846209330160007 62739306511269313995240011)
                ·
                  refine ⟨94108959766903970992860017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62739306511269313995240011 94108959766903970992860017)
                  ·
                    refine ⟨70581719825177978244645013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94108959766903970992860017 70581719825177978244645013)
                    ·
                      refine ⟨3308518116805217730217735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70581719825177978244645013 3308518116805217730217735)
                      ·
                        rfl

theorem cell23_6443316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6443316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443316 prefixEnd_6443316 := by exact prefixLift 6443316
  have htrace : WordTrace (prefixWord ++ tailWord_6443316) baseStart_6443316 baseEnd_6443316 := by
    simpa [prefixWord, tailWord_6443316, baseEnd_6443316] using wordTrace_append hprefix tailTrace_6443316
  have hstable : (prefixWord ++ tailWord_6443316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443316).length < 2 ^ (prefixWord ++ tailWord_6443316).sum := by decide
  have hdescent : baseEnd_6443316 < baseStart_6443316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443339 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 1, 6]
def baseStart_6443339 : Nat := 118140960795 + 6443339 * 2 ^ 59
def prefixEnd_6443339 : Nat := 4983230072969 + 3 ^ 40 * 6443339 * 2
def baseEnd_6443339 : Nat := 1102843308953423713410043

theorem tailTrace_6443339 : CollatzResearch.WordTrace tailWord_6443339 prefixEnd_6443339 1102843308953423713410043 := by
  unfold tailWord_6443339
  simp only [CollatzResearch.WordTrace]
  refine ⟨235007880003890712536229071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156671920002593808357486047 235007880003890712536229071)
  ·
    refine ⟨352511820005836068804343607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235007880003890712536229071 352511820005836068804343607)
    ·
      refine ⟨528767730008754103206515411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352511820005836068804343607 528767730008754103206515411)
      ·
        refine ⟨793151595013131154809773117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528767730008754103206515411 793151595013131154809773117)
        ·
          refine ⟨297431848129924183053664919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 793151595013131154809773117 297431848129924183053664919)
          ·
            refine ⟨446147772194886274580497379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297431848129924183053664919 446147772194886274580497379)
            ·
              refine ⟨669221658292329411870746069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446147772194886274580497379 669221658292329411870746069)
              ·
                refine ⟨15684882616226470590720611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 669221658292329411870746069 15684882616226470590720611)
                ·
                  refine ⟨23527323924339705886080917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15684882616226470590720611 23527323924339705886080917)
                  ·
                    refine ⟨1102843308953423713410043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23527323924339705886080917 1102843308953423713410043)
                    ·
                      rfl

theorem cell23_6443339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 6].length) (baseStart_6443339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443339 prefixEnd_6443339 := by exact prefixLift 6443339
  have htrace : WordTrace (prefixWord ++ tailWord_6443339) baseStart_6443339 baseEnd_6443339 := by
    simpa [prefixWord, tailWord_6443339, baseEnd_6443339] using wordTrace_append hprefix tailTrace_6443339
  have hstable : (prefixWord ++ tailWord_6443339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443339).length < 2 ^ (prefixWord ++ tailWord_6443339).sum := by decide
  have hdescent : baseEnd_6443339 < baseStart_6443339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443346 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6443346 : Nat := 118140960795 + 6443346 * 2 ^ 59
def prefixEnd_6443346 : Nat := 4983230072969 + 3 ^ 40 * 6443346 * 2
def baseEnd_6443346 : Nat := 3308533521224852612842597

theorem tailTrace_6443346 : CollatzResearch.WordTrace tailWord_6443346 prefixEnd_6443346 3308533521224852612842597 := by
  unfold tailWord_6443346
  simp only [CollatzResearch.WordTrace]
  refine ⟨58752033828716338182933473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156672090209910235154489261 58752033828716338182933473)
  ·
    refine ⟨44064025371537253637200105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58752033828716338182933473 44064025371537253637200105)
    ·
      refine ⟨33048019028652940227900079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44064025371537253637200105 33048019028652940227900079)
      ·
        refine ⟨49572028542979410341850119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33048019028652940227900079 49572028542979410341850119)
        ·
          refine ⟨74358042814469115512775179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49572028542979410341850119 74358042814469115512775179)
          ·
            refine ⟨111537064221703673269162769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74358042814469115512775179 111537064221703673269162769)
            ·
              refine ⟨83652798166277754951872077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111537064221703673269162769 83652798166277754951872077)
              ·
                refine ⟨31369799312354158106952029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83652798166277754951872077 31369799312354158106952029)
                ·
                  refine ⟨11763674742132809290107011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31369799312354158106952029 11763674742132809290107011)
                  ·
                    refine ⟨17645512113199213935160517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11763674742132809290107011 17645512113199213935160517)
                    ·
                      refine ⟨3308533521224852612842597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17645512113199213935160517 3308533521224852612842597)
                      ·
                        rfl

theorem cell23_6443346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6443346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443346 prefixEnd_6443346 := by exact prefixLift 6443346
  have htrace : WordTrace (prefixWord ++ tailWord_6443346) baseStart_6443346 baseEnd_6443346 := by
    simpa [prefixWord, tailWord_6443346, baseEnd_6443346] using wordTrace_append hprefix tailTrace_6443346
  have hstable : (prefixWord ++ tailWord_6443346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443346).length < 2 ^ (prefixWord ++ tailWord_6443346).sum := by decide
  have hdescent : baseEnd_6443346 < baseStart_6443346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443373 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_6443373 : Nat := 118140960795 + 6443373 * 2 ^ 59
def prefixEnd_6443373 : Nat := 4983230072969 + 3 ^ 40 * 6443373 * 2
def baseEnd_6443373 : Nat := 1102849128400841335734991

theorem tailTrace_6443373 : CollatzResearch.WordTrace tailWord_6443373 prefixEnd_6443373 1102849128400841335734991 := by
  unfold tailWord_6443373
  simp only [CollatzResearch.WordTrace]
  refine ⟨235009120085767536342966773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156672746723845024228644515 235009120085767536342966773)
  ·
    refine ⟨22032105008040706532153135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235009120085767536342966773 22032105008040706532153135)
    ·
      refine ⟨33048157512061059798229703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22032105008040706532153135 33048157512061059798229703)
      ·
        refine ⟨49572236268091589697344555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33048157512061059798229703 49572236268091589697344555)
        ·
          refine ⟨74358354402137384546016833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49572236268091589697344555 74358354402137384546016833)
          ·
            refine ⟨55768765801603038409512625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74358354402137384546016833 55768765801603038409512625)
            ·
              refine ⟨41826574351202278807134469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55768765801603038409512625 41826574351202278807134469)
              ·
                refine ⟨7842482690850427276337713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41826574351202278807134469 7842482690850427276337713)
                ·
                  refine ⟨5881862018137820457253285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7842482690850427276337713 5881862018137820457253285)
                  ·
                    refine ⟨1102849128400841335734991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881862018137820457253285 1102849128400841335734991)
                    ·
                      rfl

theorem cell23_6443373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_6443373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443373 prefixEnd_6443373 := by exact prefixLift 6443373
  have htrace : WordTrace (prefixWord ++ tailWord_6443373) baseStart_6443373 baseEnd_6443373 := by
    simpa [prefixWord, tailWord_6443373, baseEnd_6443373] using wordTrace_append hprefix tailTrace_6443373
  have hstable : (prefixWord ++ tailWord_6443373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443373).length < 2 ^ (prefixWord ++ tailWord_6443373).sum := by decide
  have hdescent : baseEnd_6443373 < baseStart_6443373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443394 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6443394 : Nat := 118140960795 + 6443394 * 2 ^ 59
def prefixEnd_6443394 : Nat := 4983230072969 + 3 ^ 40 * 6443394 * 2
def baseEnd_6443394 : Nat := 1102852722765422808347459

theorem tailTrace_6443394 : CollatzResearch.WordTrace tailWord_6443394 prefixEnd_6443394 1102852722765422808347459 := by
  unfold tailWord_6443394
  simp only [CollatzResearch.WordTrace]
  refine ⟨58752471504672864232370309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156673257345794304619654157 58752471504672864232370309)
  ·
    refine ⟨11016088407126162043569433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58752471504672864232370309 11016088407126162043569433)
    ·
      refine ⟨8262066305344621532677075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11016088407126162043569433 8262066305344621532677075)
      ·
        refine ⟨12393099458016932299015613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262066305344621532677075 12393099458016932299015613)
        ·
          refine ⟨4647412296756349612130855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12393099458016932299015613 4647412296756349612130855)
          ·
            refine ⟨6971118445134524418196283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647412296756349612130855 6971118445134524418196283)
            ·
              refine ⟨10456677667701786627294425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971118445134524418196283 10456677667701786627294425)
              ·
                refine ⟨7842508250776339970470819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456677667701786627294425 7842508250776339970470819)
                ·
                  refine ⟨11763762376164509955706229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842508250776339970470819 11763762376164509955706229)
                  ·
                    refine ⟨1102852722765422808347459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11763762376164509955706229 1102852722765422808347459)
                    ·
                      rfl

theorem cell23_6443394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6443394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443394 prefixEnd_6443394 := by exact prefixLift 6443394
  have htrace : WordTrace (prefixWord ++ tailWord_6443394) baseStart_6443394 baseEnd_6443394 := by
    simpa [prefixWord, tailWord_6443394, baseEnd_6443394] using wordTrace_append hprefix tailTrace_6443394
  have hstable : (prefixWord ++ tailWord_6443394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443394).length < 2 ^ (prefixWord ++ tailWord_6443394).sum := by decide
  have hdescent : baseEnd_6443394 < baseStart_6443394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443431 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_6443431 : Nat := 118140960795 + 6443431 * 2 ^ 59
def prefixEnd_6443431 : Nat := 4983230072969 + 3 ^ 40 * 6443431 * 2
def baseEnd_6443431 : Nat := 3308577167080484780279707

theorem tailTrace_6443431 : CollatzResearch.WordTrace tailWord_6443431 prefixEnd_6443431 3308577167080484780279707 := by
  unfold tailWord_6443431
  simp only [CollatzResearch.WordTrace]
  refine ⟨235011235519557412248578147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156674157013038274832385431 235011235519557412248578147)
  ·
    refine ⟨352516853279336118372867221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235011235519557412248578147 352516853279336118372867221)
    ·
      refine ⟨16524227497468880548728151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 352516853279336118372867221 16524227497468880548728151)
      ·
        refine ⟨24786341246203320823092227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16524227497468880548728151 24786341246203320823092227)
        ·
          refine ⟨37179511869304981234638341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24786341246203320823092227 37179511869304981234638341)
          ·
            refine ⟨6971158475494683981494689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37179511869304981234638341 6971158475494683981494689)
            ·
              refine ⟨5228368856621012986121017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6971158475494683981494689 5228368856621012986121017)
              ·
                refine ⟨3921276642465759739590763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228368856621012986121017 3921276642465759739590763)
                ·
                  refine ⟨5881914963698639609386145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921276642465759739590763 5881914963698639609386145)
                  ·
                    refine ⟨4411436222773979707039609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5881914963698639609386145 4411436222773979707039609)
                    ·
                      refine ⟨3308577167080484780279707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411436222773979707039609 3308577167080484780279707)
                      ·
                        rfl

theorem cell23_6443431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_6443431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443431 prefixEnd_6443431 := by exact prefixLift 6443431
  have htrace : WordTrace (prefixWord ++ tailWord_6443431) baseStart_6443431 baseEnd_6443431 := by
    simpa [prefixWord, tailWord_6443431, baseEnd_6443431] using wordTrace_append hprefix tailTrace_6443431
  have hstable : (prefixWord ++ tailWord_6443431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443431).length < 2 ^ (prefixWord ++ tailWord_6443431).sum := by decide
  have hdescent : baseEnd_6443431 < baseStart_6443431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443456 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_6443456 : Nat := 118140960795 + 6443456 * 2 ^ 59
def prefixEnd_6443456 : Nat := 4983230072969 + 3 ^ 40 * 6443456 * 2
def baseEnd_6443456 : Nat := 3308590004096847182467091

theorem tailTrace_6443456 : CollatzResearch.WordTrace tailWord_6443456 prefixEnd_6443456 3308590004096847182467091 := by
  unfold tailWord_6443456
  simp only [CollatzResearch.WordTrace]
  refine ⟨117506073672233420759119111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156674764896311227678825481 117506073672233420759119111)
  ·
    refine ⟨176259110508350131138678667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117506073672233420759119111 176259110508350131138678667)
    ·
      refine ⟨264388665762525196708018001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176259110508350131138678667 264388665762525196708018001)
      ·
        refine ⟨198291499321893897531013501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264388665762525196708018001 198291499321893897531013501)
        ·
          refine ⟨74359312245710211574130063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198291499321893897531013501 74359312245710211574130063)
          ·
            refine ⟨111538968368565317361195095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74359312245710211574130063 111538968368565317361195095)
            ·
              refine ⟨167308452552847976041792643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111538968368565317361195095 167308452552847976041792643)
              ·
                refine ⟨250962678829271964062688965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167308452552847976041792643 250962678829271964062688965)
                ·
                  refine ⟨47055502280488493261754181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250962678829271964062688965 47055502280488493261754181)
                  ·
                    refine ⟨8822906677591592486578909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47055502280488493261754181 8822906677591592486578909)
                    ·
                      refine ⟨3308590004096847182467091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8822906677591592486578909 3308590004096847182467091)
                      ·
                        rfl

theorem cell23_6443456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_6443456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443456 prefixEnd_6443456 := by exact prefixLift 6443456
  have htrace : WordTrace (prefixWord ++ tailWord_6443456) baseStart_6443456 baseEnd_6443456 := by
    simpa [prefixWord, tailWord_6443456, baseEnd_6443456] using wordTrace_append hprefix tailTrace_6443456
  have hstable : (prefixWord ++ tailWord_6443456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443456).length < 2 ^ (prefixWord ++ tailWord_6443456).sum := by decide
  have hdescent : baseEnd_6443456 < baseStart_6443456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443466 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_6443466 : Nat := 118140960795 + 6443466 * 2 ^ 59
def prefixEnd_6443466 : Nat := 4983230072969 + 3 ^ 40 * 6443466 * 2
def baseEnd_6443466 : Nat := 3308595138903392143342045

theorem tailTrace_6443466 : CollatzResearch.WordTrace tailWord_6443466 prefixEnd_6443466 3308595138903392143342045 := by
  unfold tailWord_6443466
  simp only [CollatzResearch.WordTrace]
  refine ⟨58753128018607653306525563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156675008049620408817401501 58753128018607653306525563)
  ·
    refine ⟨88129692027911479959788345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58753128018607653306525563 88129692027911479959788345)
    ·
      refine ⟨66097269020933609969841259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88129692027911479959788345 66097269020933609969841259)
      ·
        refine ⟨99145903531400414954761889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66097269020933609969841259 99145903531400414954761889)
        ·
          refine ⟨74359427648550311216071417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99145903531400414954761889 74359427648550311216071417)
          ·
            refine ⟨55769570736412733412053563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74359427648550311216071417 55769570736412733412053563)
            ·
              refine ⟨83654356104619100118080345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55769570736412733412053563 83654356104619100118080345)
              ·
                refine ⟨62740767078464325088560259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83654356104619100118080345 62740767078464325088560259)
                ·
                  refine ⟨94111150617696487632840389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62740767078464325088560259 94111150617696487632840389)
                  ·
                    refine ⟨17645840740818091431157573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94111150617696487632840389 17645840740818091431157573)
                    ·
                      refine ⟨3308595138903392143342045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17645840740818091431157573 3308595138903392143342045)
                      ·
                        rfl

theorem cell23_6443466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_6443466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443466 prefixEnd_6443466 := by exact prefixLift 6443466
  have htrace : WordTrace (prefixWord ++ tailWord_6443466) baseStart_6443466 baseEnd_6443466 := by
    simpa [prefixWord, tailWord_6443466, baseEnd_6443466] using wordTrace_append hprefix tailTrace_6443466
  have hstable : (prefixWord ++ tailWord_6443466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443466).length < 2 ^ (prefixWord ++ tailWord_6443466).sum := by decide
  have hdescent : baseEnd_6443466 < baseStart_6443466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443470 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_6443470 : Nat := 118140960795 + 6443470 * 2 ^ 59
def prefixEnd_6443470 : Nat := 4983230072969 + 3 ^ 40 * 6443470 * 2
def baseEnd_6443470 : Nat := 3308597192826010127692027

theorem tailTrace_6443470 : CollatzResearch.WordTrace tailWord_6443470 prefixEnd_6443470 3308597192826010127692027 := by
  unfold tailWord_6443470
  simp only [CollatzResearch.WordTrace]
  refine ⟨29376582245802015238655983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156675105310944081272831909 29376582245802015238655983)
  ·
    refine ⟨44064873368703022857983975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29376582245802015238655983 44064873368703022857983975)
    ·
      refine ⟨66097310053054534286975963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44064873368703022857983975 66097310053054534286975963)
      ·
        refine ⟨99145965079581801430463945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66097310053054534286975963 99145965079581801430463945)
        ·
          refine ⟨74359473809686351072847959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99145965079581801430463945 74359473809686351072847959)
          ·
            refine ⟨111539210714529526609271939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74359473809686351072847959 111539210714529526609271939)
            ·
              refine ⟨167308816071794289913907909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111539210714529526609271939 167308816071794289913907909)
              ·
                refine ⟨31370403013461429358857733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167308816071794289913907909 31370403013461429358857733)
                ·
                  refine ⟨5881950565024018004785825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31370403013461429358857733 5881950565024018004785825)
                  ·
                    refine ⟨4411462923768013503589369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5881950565024018004785825 4411462923768013503589369)
                    ·
                      refine ⟨3308597192826010127692027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411462923768013503589369 3308597192826010127692027)
                      ·
                        rfl

theorem cell23_6443470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_6443470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443470 prefixEnd_6443470 := by exact prefixLift 6443470
  have htrace : WordTrace (prefixWord ++ tailWord_6443470) baseStart_6443470 baseEnd_6443470 := by
    simpa [prefixWord, tailWord_6443470, baseEnd_6443470] using wordTrace_append hprefix tailTrace_6443470
  have hstable : (prefixWord ++ tailWord_6443470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443470).length < 2 ^ (prefixWord ++ tailWord_6443470).sum := by decide
  have hdescent : baseEnd_6443470 < baseStart_6443470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443474 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6443474 : Nat := 118140960795 + 6443474 * 2 ^ 59
def prefixEnd_6443474 : Nat := 4983230072969 + 3 ^ 40 * 6443474 * 2
def baseEnd_6443474 : Nat := 3308599246748628112042009

theorem tailTrace_6443474 : CollatzResearch.WordTrace tailWord_6443474 prefixEnd_6443474 3308599246748628112042009 := by
  unfold tailWord_6443474
  simp only [CollatzResearch.WordTrace]
  refine ⟨58753200964600407648098369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156675202572267753728262317 58753200964600407648098369)
  ·
    refine ⟨44064900723450305736073777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58753200964600407648098369 44064900723450305736073777)
    ·
      refine ⟨33048675542587729302055333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44064900723450305736073777 33048675542587729302055333)
      ·
        refine ⟨6196626664235199244135375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33048675542587729302055333 6196626664235199244135375)
        ·
          refine ⟨9294939996352798866203063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6196626664235199244135375 9294939996352798866203063)
          ·
            refine ⟨13942409994529198299304595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9294939996352798866203063 13942409994529198299304595)
            ·
              refine ⟨20913614991793797448956893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13942409994529198299304595 20913614991793797448956893)
              ·
                refine ⟨7842605621922674043358835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20913614991793797448956893 7842605621922674043358835)
                ·
                  refine ⟨11763908432884011065038253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842605621922674043358835 11763908432884011065038253)
                  ·
                    refine ⟨4411465662331504149389345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11763908432884011065038253 4411465662331504149389345)
                    ·
                      refine ⟨3308599246748628112042009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411465662331504149389345 3308599246748628112042009)
                      ·
                        rfl

theorem cell23_6443474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6443474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443474 prefixEnd_6443474 := by exact prefixLift 6443474
  have htrace : WordTrace (prefixWord ++ tailWord_6443474) baseStart_6443474 baseEnd_6443474 := by
    simpa [prefixWord, tailWord_6443474, baseEnd_6443474] using wordTrace_append hprefix tailTrace_6443474
  have hstable : (prefixWord ++ tailWord_6443474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443474).length < 2 ^ (prefixWord ++ tailWord_6443474).sum := by decide
  have hdescent : baseEnd_6443474 < baseStart_6443474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443487 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 2, 2, 2]
def baseStart_6443487 : Nat := 118140960795 + 6443487 * 2 ^ 59
def prefixEnd_6443487 : Nat := 4983230072969 + 3 ^ 40 * 6443487 * 2
def baseEnd_6443487 : Nat := 3308605921997136561179449

theorem tailTrace_6443487 : CollatzResearch.WordTrace tailWord_6443487 prefixEnd_6443487 3308605921997136561179449 := by
  unfold tailWord_6443487
  simp only [CollatzResearch.WordTrace]
  refine ⟨235013278007354533812616715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156675518671569689208411143 235013278007354533812616715)
  ·
    refine ⟨352519917011031800718925073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235013278007354533812616715 352519917011031800718925073)
    ·
      refine ⟨264389937758273850539193805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352519917011031800718925073 264389937758273850539193805)
      ·
        refine ⟨99146226659352693952197677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264389937758273850539193805 99146226659352693952197677)
        ·
          refine ⟨37179834997257260232074129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99146226659352693952197677 37179834997257260232074129)
          ·
            refine ⟨27884876247942945174055597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37179834997257260232074129 27884876247942945174055597)
            ·
              refine ⟨10456828592978604440270849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27884876247942945174055597 10456828592978604440270849)
              ·
                refine ⟨7842621444733953330203137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456828592978604440270849 7842621444733953330203137)
                ·
                  refine ⟨5881966083550464997652353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7842621444733953330203137 5881966083550464997652353)
                  ·
                    refine ⟨4411474562662848748239265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5881966083550464997652353 4411474562662848748239265)
                    ·
                      refine ⟨3308605921997136561179449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411474562662848748239265 3308605921997136561179449)
                      ·
                        rfl

theorem cell23_6443487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_6443487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443487 prefixEnd_6443487 := by exact prefixLift 6443487
  have htrace : WordTrace (prefixWord ++ tailWord_6443487) baseStart_6443487 baseEnd_6443487 := by
    simpa [prefixWord, tailWord_6443487, baseEnd_6443487] using wordTrace_append hprefix tailTrace_6443487
  have hstable : (prefixWord ++ tailWord_6443487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443487).length < 2 ^ (prefixWord ++ tailWord_6443487).sum := by decide
  have hdescent : baseEnd_6443487 < baseStart_6443487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443513 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 2, 5, 2]
def baseStart_6443513 : Nat := 118140960795 + 6443513 * 2 ^ 59
def prefixEnd_6443513 : Nat := 4983230072969 + 3 ^ 40 * 6443513 * 2
def baseEnd_6443513 : Nat := 3308619272494153459454329

theorem tailTrace_6443513 : CollatzResearch.WordTrace tailWord_6443513 prefixEnd_6443513 3308619272494153459454329 := by
  unfold tailWord_6443513
  simp only [CollatzResearch.WordTrace]
  refine ⟨235014226305260340253063193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156676150870173560168708795 235014226305260340253063193)
  ·
    refine ⟨176260669728945255189797395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235014226305260340253063193 176260669728945255189797395)
    ·
      refine ⟨264391004593417882784696093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176260669728945255189797395 264391004593417882784696093)
      ·
        refine ⟨99146626722531706044261035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264391004593417882784696093 99146626722531706044261035)
        ·
          refine ⟨148719940083797559066391553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99146626722531706044261035 148719940083797559066391553)
          ·
            refine ⟨111539955062848169299793665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148719940083797559066391553 111539955062848169299793665)
            ·
              refine ⟨83654966297136126974845249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111539955062848169299793665 83654966297136126974845249)
              ·
                refine ⟨62741224722852095231133937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83654966297136126974845249 62741224722852095231133937)
                ·
                  refine ⟨47055918542139071423350453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62741224722852095231133937 47055918542139071423350453)
                  ·
                    refine ⟨4411492363325537945939105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47055918542139071423350453 4411492363325537945939105)
                    ·
                      refine ⟨3308619272494153459454329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411492363325537945939105 3308619272494153459454329)
                      ·
                        rfl

theorem cell23_6443513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_6443513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443513 prefixEnd_6443513 := by exact prefixLift 6443513
  have htrace : WordTrace (prefixWord ++ tailWord_6443513) baseStart_6443513 baseEnd_6443513 := by
    simpa [prefixWord, tailWord_6443513, baseEnd_6443513] using wordTrace_append hprefix tailTrace_6443513
  have hstable : (prefixWord ++ tailWord_6443513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443513).length < 2 ^ (prefixWord ++ tailWord_6443513).sum := by decide
  have hdescent : baseEnd_6443513 < baseStart_6443513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443516 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_6443516 : Nat := 118140960795 + 6443516 * 2 ^ 59
def prefixEnd_6443516 : Nat := 4983230072969 + 3 ^ 40 * 6443516 * 2
def baseEnd_6443516 : Nat := 3308620812936116947716815

theorem tailTrace_6443516 : CollatzResearch.WordTrace tailWord_6443516 prefixEnd_6443516 3308620812936116947716815 := by
  unfold tailWord_6443516
  simp only [CollatzResearch.WordTrace]
  refine ⟨117507167862124735882711201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156676223816166314510281601 117507167862124735882711201)
  ·
    refine ⟨88130375896593551912033401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117507167862124735882711201 88130375896593551912033401)
    ·
      refine ⟨66097781922445163934025051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88130375896593551912033401 66097781922445163934025051)
      ·
        refine ⟨99146672883667745901037577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66097781922445163934025051 99146672883667745901037577)
        ·
          refine ⟨74360004662750809425778183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99146672883667745901037577 74360004662750809425778183)
          ·
            refine ⟨111540006994126214138667275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74360004662750809425778183 111540006994126214138667275)
            ·
              refine ⟨167310010491189321208000913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111540006994126214138667275 167310010491189321208000913)
              ·
                refine ⟨125482507868391990906000685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167310010491189321208000913 125482507868391990906000685)
                ·
                  refine ⟨47055940450646996589750257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125482507868391990906000685 47055940450646996589750257)
                  ·
                    refine ⟨35291955337985247442312693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47055940450646996589750257 35291955337985247442312693)
                    ·
                      refine ⟨3308620812936116947716815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35291955337985247442312693 3308620812936116947716815)
                      ·
                        rfl

theorem cell23_6443516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_6443516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443516 prefixEnd_6443516 := by exact prefixLift 6443516
  have htrace : WordTrace (prefixWord ++ tailWord_6443516) baseStart_6443516 baseEnd_6443516 := by
    simpa [prefixWord, tailWord_6443516, baseEnd_6443516] using wordTrace_append hprefix tailTrace_6443516
  have hstable : (prefixWord ++ tailWord_6443516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443516).length < 2 ^ (prefixWord ++ tailWord_6443516).sum := by decide
  have hdescent : baseEnd_6443516 < baseStart_6443516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443527 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 5]
def baseStart_6443527 : Nat := 118140960795 + 6443527 * 2 ^ 59
def prefixEnd_6443527 : Nat := 4983230072969 + 3 ^ 40 * 6443527 * 2
def baseEnd_6443527 : Nat := 367625162358146267186585

theorem tailTrace_6443527 : CollatzResearch.WordTrace tailWord_6443527 prefixEnd_6443527 367625162358146267186585 := by
  unfold tailWord_6443527
  simp only [CollatzResearch.WordTrace]
  refine ⟨235014736927209620644072835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156676491284806413762715223 235014736927209620644072835)
  ·
    refine ⟨352522105390814430966109253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235014736927209620644072835 352522105390814430966109253)
    ·
      refine ⟨66097894760777705806145485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352522105390814430966109253 66097894760777705806145485)
      ·
        refine ⟨24786710535291639677304557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66097894760777705806145485 24786710535291639677304557)
        ·
          refine ⟨9295016450734364878989209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24786710535291639677304557 9295016450734364878989209)
          ·
            refine ⟨6971262338050773659241907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9295016450734364878989209 6971262338050773659241907)
            ·
              refine ⟨10456893507076160488862861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971262338050773659241907 10456893507076160488862861)
              ·
                refine ⟨3921335065153560183323573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10456893507076160488862861 3921335065153560183323573)
                ·
                  refine ⟨367625162358146267186585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3921335065153560183323573 367625162358146267186585)
                  ·
                    rfl

theorem cell23_6443527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 5].length) (baseStart_6443527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443527 prefixEnd_6443527 := by exact prefixLift 6443527
  have htrace : WordTrace (prefixWord ++ tailWord_6443527) baseStart_6443527 baseEnd_6443527 := by
    simpa [prefixWord, tailWord_6443527, baseEnd_6443527] using wordTrace_append hprefix tailTrace_6443527
  have hstable : (prefixWord ++ tailWord_6443527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443527).length < 2 ^ (prefixWord ++ tailWord_6443527).sum := by decide
  have hdescent : baseEnd_6443527 < baseStart_6443527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443540 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_6443540 : Nat := 118140960795 + 6443540 * 2 ^ 59
def prefixEnd_6443540 : Nat := 4983230072969 + 3 ^ 40 * 6443540 * 2
def baseEnd_6443540 : Nat := 1102877712157274951272235

theorem tailTrace_6443540 : CollatzResearch.WordTrace tailWord_6443540 prefixEnd_6443540 1102877712157274951272235 := by
  unfold tailWord_6443540
  simp only [CollatzResearch.WordTrace]
  refine ⟨117507605538081261932148037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156676807384108349242864049 117507605538081261932148037)
  ·
    refine ⟨22032676038390236612277757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117507605538081261932148037 22032676038390236612277757)
    ·
      refine ⟨8262253514396338729604159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22032676038390236612277757 8262253514396338729604159)
      ·
        refine ⟨12393380271594508094406239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262253514396338729604159 12393380271594508094406239)
        ·
          refine ⟨18590070407391762141609359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12393380271594508094406239 18590070407391762141609359)
          ·
            refine ⟨27885105611087643212414039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18590070407391762141609359 27885105611087643212414039)
            ·
              refine ⟨41827658416631464818621059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27885105611087643212414039 41827658416631464818621059)
              ·
                refine ⟨62741487624947197227931589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41827658416631464818621059 62741487624947197227931589)
                ·
                  refine ⟨11764028929677599480237173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62741487624947197227931589 11764028929677599480237173)
                  ·
                    refine ⟨1102877712157274951272235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11764028929677599480237173 1102877712157274951272235)
                    ·
                      rfl

theorem cell23_6443540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_6443540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443540 prefixEnd_6443540 := by exact prefixLift 6443540
  have htrace : WordTrace (prefixWord ++ tailWord_6443540) baseStart_6443540 baseEnd_6443540 := by
    simpa [prefixWord, tailWord_6443540, baseEnd_6443540] using wordTrace_append hprefix tailTrace_6443540
  have hstable : (prefixWord ++ tailWord_6443540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443540).length < 2 ^ (prefixWord ++ tailWord_6443540).sum := by decide
  have hdescent : baseEnd_6443540 < baseStart_6443540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443580 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_6443580 : Nat := 118140960795 + 6443580 * 2 ^ 59
def prefixEnd_6443580 : Nat := 4983230072969 + 3 ^ 40 * 6443580 * 2
def baseEnd_6443580 : Nat := 3308653675698004697316521

theorem tailTrace_6443580 : CollatzResearch.WordTrace tailWord_6443580 prefixEnd_6443580 3308653675698004697316521 := by
  unfold tailWord_6443580
  simp only [CollatzResearch.WordTrace]
  refine ⟨117508334998008805347876097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156677779997345073797168129 117508334998008805347876097)
  ·
    refine ⟨88131251248506604010907073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117508334998008805347876097 88131251248506604010907073)
    ·
      refine ⟨66098438436379953008180305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88131251248506604010907073 66098438436379953008180305)
      ·
        refine ⟨49573828827284964756135229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66098438436379953008180305 49573828827284964756135229)
        ·
          refine ⟨18590185810231861783550711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49573828827284964756135229 18590185810231861783550711)
          ·
            refine ⟨27885278715347792675326067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18590185810231861783550711 27885278715347792675326067)
            ·
              refine ⟨41827918073021689012989101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27885278715347792675326067 41827918073021689012989101)
              ·
                refine ⟨15685469277383133379870913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41827918073021689012989101 15685469277383133379870913)
                ·
                  refine ⟨11764101958037350034903185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15685469277383133379870913 11764101958037350034903185)
                  ·
                    refine ⟨8823076468528012526177389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11764101958037350034903185 8823076468528012526177389)
                    ·
                      refine ⟨3308653675698004697316521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8823076468528012526177389 3308653675698004697316521)
                      ·
                        rfl

theorem cell23_6443580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_6443580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443580 prefixEnd_6443580 := by exact prefixLift 6443580
  have htrace : WordTrace (prefixWord ++ tailWord_6443580) baseStart_6443580 baseEnd_6443580 := by
    simpa [prefixWord, tailWord_6443580, baseEnd_6443580] using wordTrace_append hprefix tailTrace_6443580
  have hstable : (prefixWord ++ tailWord_6443580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443580).length < 2 ^ (prefixWord ++ tailWord_6443580).sum := by decide
  have hdescent : baseEnd_6443580 < baseStart_6443580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443597 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6443597 : Nat := 118140960795 + 6443597 * 2 ^ 59
def prefixEnd_6443597 : Nat := 4983230072969 + 3 ^ 40 * 6443597 * 2
def baseEnd_6443597 : Nat := 3308662404869131130803943

theorem tailTrace_6443597 : CollatzResearch.WordTrace tailWord_6443597 prefixEnd_6443597 3308662404869131130803943 := by
  unfold tailWord_6443597
  simp only [CollatzResearch.WordTrace]
  refine ⟨235017290036956022599121045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156678193357970681732747363 235017290036956022599121045)
  ·
    refine ⟨11016435470482313559333799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235017290036956022599121045 11016435470482313559333799)
    ·
      refine ⟨16524653205723470339000699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11016435470482313559333799 16524653205723470339000699)
      ·
        refine ⟨24786979808585205508501049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16524653205723470339000699 24786979808585205508501049)
        ·
          refine ⟨18590234856438904131375787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24786979808585205508501049 18590234856438904131375787)
          ·
            refine ⟨27885352284658356197063681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18590234856438904131375787 27885352284658356197063681)
            ·
              refine ⟨20914014213493767147797761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27885352284658356197063681 20914014213493767147797761)
              ·
                refine ⟨15685510660120325360848321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20914014213493767147797761 15685510660120325360848321)
                ·
                  refine ⟨11764132995090244020636241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15685510660120325360848321 11764132995090244020636241)
                  ·
                    refine ⟨8823099746317683015477181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11764132995090244020636241 8823099746317683015477181)
                    ·
                      refine ⟨3308662404869131130803943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8823099746317683015477181 3308662404869131130803943)
                      ·
                        rfl

theorem cell23_6443597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6443597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443597 prefixEnd_6443597 := by exact prefixLift 6443597
  have htrace : WordTrace (prefixWord ++ tailWord_6443597) baseStart_6443597 baseEnd_6443597 := by
    simpa [prefixWord, tailWord_6443597, baseEnd_6443597] using wordTrace_append hprefix tailTrace_6443597
  have hstable : (prefixWord ++ tailWord_6443597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443597).length < 2 ^ (prefixWord ++ tailWord_6443597).sum := by decide
  have hdescent : baseEnd_6443597 < baseStart_6443597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443604 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_6443604 : Nat := 118140960795 + 6443604 * 2 ^ 59
def prefixEnd_6443604 : Nat := 4983230072969 + 3 ^ 40 * 6443604 * 2
def baseEnd_6443604 : Nat := 1102888666411237534472137

theorem tailTrace_6443604 : CollatzResearch.WordTrace tailWord_6443604 prefixEnd_6443604 1102888666411237534472137 := by
  unfold tailWord_6443604
  simp only [CollatzResearch.WordTrace]
  refine ⟨117508772673965331397312933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156678363565287108529750577 117508772673965331397312933)
  ·
    refine ⟨22032894876368499636996175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117508772673965331397312933 22032894876368499636996175)
    ·
      refine ⟨33049342314552749455494263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22032894876368499636996175 33049342314552749455494263)
      ·
        refine ⟨49574013471829124183241395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33049342314552749455494263 49574013471829124183241395)
        ·
          refine ⟨74361020207743686274862093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49574013471829124183241395 74361020207743686274862093)
          ·
            refine ⟨27885382577903882353073285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74361020207743686274862093 27885382577903882353073285)
            ·
              refine ⟨5228509233356977941201241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27885382577903882353073285 5228509233356977941201241)
              ·
                refine ⟨3921381925017733455900931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228509233356977941201241 3921381925017733455900931)
                ·
                  refine ⟨5882072887526600183851397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921381925017733455900931 5882072887526600183851397)
                  ·
                    refine ⟨1102888666411237534472137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882072887526600183851397 1102888666411237534472137)
                    ·
                      rfl

theorem cell23_6443604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_6443604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443604 prefixEnd_6443604 := by exact prefixLift 6443604
  have htrace : WordTrace (prefixWord ++ tailWord_6443604) baseStart_6443604 baseEnd_6443604 := by
    simpa [prefixWord, tailWord_6443604, baseEnd_6443604] using wordTrace_append hprefix tailTrace_6443604
  have hstable : (prefixWord ++ tailWord_6443604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443604).length < 2 ^ (prefixWord ++ tailWord_6443604).sum := by decide
  have hdescent : baseEnd_6443604 < baseStart_6443604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443620 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_6443620 : Nat := 118140960795 + 6443620 * 2 ^ 59
def prefixEnd_6443620 : Nat := 4983230072969 + 3 ^ 40 * 6443620 * 2
def baseEnd_6443620 : Nat := 3308674214924184540816337

theorem tailTrace_6443620 : CollatzResearch.WordTrace tailWord_6443620 prefixEnd_6443620 3308674214924184540816337 := by
  unfold tailWord_6443620
  simp only [CollatzResearch.WordTrace]
  refine ⟨117509064457936348763604157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156678752610581798351472209 117509064457936348763604157)
  ·
    refine ⟨44065899171726130786351559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117509064457936348763604157 44065899171726130786351559)
    ·
      refine ⟨66098848757589196179527339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44065899171726130786351559 66098848757589196179527339)
      ·
        refine ⟨99148273136383794269291009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66098848757589196179527339 99148273136383794269291009)
        ·
          refine ⟨74361204852287845701968257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99148273136383794269291009 74361204852287845701968257)
          ·
            refine ⟨55770903639215884276476193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74361204852287845701968257 55770903639215884276476193)
            ·
              refine ⟨41828177729411913207357145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55770903639215884276476193 41828177729411913207357145)
              ·
                refine ⟨31371133297058934905517859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41828177729411913207357145 31371133297058934905517859)
                ·
                  refine ⟨47056699945588402358276789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31371133297058934905517859 47056699945588402358276789)
                  ·
                    refine ⟨4411565619898912721088449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47056699945588402358276789 4411565619898912721088449)
                    ·
                      refine ⟨3308674214924184540816337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411565619898912721088449 3308674214924184540816337)
                      ·
                        rfl

theorem cell23_6443620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_6443620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443620 prefixEnd_6443620 := by exact prefixLift 6443620
  have htrace : WordTrace (prefixWord ++ tailWord_6443620) baseStart_6443620 baseEnd_6443620 := by
    simpa [prefixWord, tailWord_6443620, baseEnd_6443620] using wordTrace_append hprefix tailTrace_6443620
  have hstable : (prefixWord ++ tailWord_6443620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443620).length < 2 ^ (prefixWord ++ tailWord_6443620).sum := by decide
  have hdescent : baseEnd_6443620 < baseStart_6443620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443630 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_6443630 : Nat := 118140960795 + 6443630 * 2 ^ 59
def prefixEnd_6443630 : Nat := 4983230072969 + 3 ^ 40 * 6443630 * 2
def baseEnd_6443630 : Nat := 1102893116576909833897097

theorem tailTrace_6443630 : CollatzResearch.WordTrace tailWord_6443630 prefixEnd_6443630 1102893116576909833897097 := by
  unfold tailWord_6443630
  simp only [CollatzResearch.WordTrace]
  refine ⟨29377311705729558654384043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156678995763890979490048229 29377311705729558654384043)
  ·
    refine ⟨44065967558594337981576065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29377311705729558654384043 44065967558594337981576065)
    ·
      refine ⟨33049475668945753486182049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44065967558594337981576065 33049475668945753486182049)
      ·
        refine ⟨24787106751709315114636537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33049475668945753486182049 24787106751709315114636537)
        ·
          refine ⟨18590330063781986335977403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24787106751709315114636537 18590330063781986335977403)
          ·
            refine ⟨27885495095672979503966105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18590330063781986335977403 27885495095672979503966105)
            ·
              refine ⟨20914121321754734627974579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27885495095672979503966105 20914121321754734627974579)
              ·
                refine ⟨31371181982632101941961869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20914121321754734627974579 31371181982632101941961869)
                ·
                  refine ⟨11764193243487038228235701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31371181982632101941961869 11764193243487038228235701)
                  ·
                    refine ⟨1102893116576909833897097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11764193243487038228235701 1102893116576909833897097)
                    ·
                      rfl

theorem cell23_6443630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_6443630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443630 prefixEnd_6443630 := by exact prefixLift 6443630
  have htrace : WordTrace (prefixWord ++ tailWord_6443630) baseStart_6443630 baseEnd_6443630 := by
    simpa [prefixWord, tailWord_6443630, baseEnd_6443630] using wordTrace_append hprefix tailTrace_6443630
  have hstable : (prefixWord ++ tailWord_6443630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443630).length < 2 ^ (prefixWord ++ tailWord_6443630).sum := by decide
  have hdescent : baseEnd_6443630 < baseStart_6443630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443660 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_6443660 : Nat := 118140960795 + 6443660 * 2 ^ 59
def prefixEnd_6443660 : Nat := 4983230072969 + 3 ^ 40 * 6443660 * 2
def baseEnd_6443660 : Nat := 1102898251383454794772051

theorem tailTrace_6443660 : CollatzResearch.WordTrace tailWord_6443660 prefixEnd_6443660 1102898251383454794772051 := by
  unfold tailWord_6443660
  simp only [CollatzResearch.WordTrace]
  refine ⟨117509793917863892179332217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156679725223818522905776289 117509793917863892179332217)
  ·
    refine ⟨88132345438397919134499163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117509793917863892179332217 88132345438397919134499163)
    ·
      refine ⟨132198518157596878701748745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88132345438397919134499163 132198518157596878701748745)
      ·
        refine ⟨99148888618197659026311559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132198518157596878701748745 99148888618197659026311559)
        ·
          refine ⟨148723332927296488539467339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99148888618197659026311559 148723332927296488539467339)
          ·
            refine ⟨223084999390944732809201009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148723332927296488539467339 223084999390944732809201009)
            ·
              refine ⟨167313749543208549606900757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223084999390944732809201009 167313749543208549606900757)
              ·
                refine ⟨7842832009837900762823473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167313749543208549606900757 7842832009837900762823473)
                ·
                  refine ⟨5882124007378425572117605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7842832009837900762823473 5882124007378425572117605)
                  ·
                    refine ⟨1102898251383454794772051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882124007378425572117605 1102898251383454794772051)
                    ·
                      rfl

theorem cell23_6443660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_6443660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443660 prefixEnd_6443660 := by exact prefixLift 6443660
  have htrace : WordTrace (prefixWord ++ tailWord_6443660) baseStart_6443660 baseEnd_6443660 := by
    simpa [prefixWord, tailWord_6443660, baseEnd_6443660] using wordTrace_append hprefix tailTrace_6443660
  have hstable : (prefixWord ++ tailWord_6443660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443660).length < 2 ^ (prefixWord ++ tailWord_6443660).sum := by decide
  have hdescent : baseEnd_6443660 < baseStart_6443660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443680 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_6443680 : Nat := 118140960795 + 6443680 * 2 ^ 59
def prefixEnd_6443680 : Nat := 4983230072969 + 3 ^ 40 * 6443680 * 2
def baseEnd_6443680 : Nat := 3308705023763454306066061

theorem tailTrace_6443680 : CollatzResearch.WordTrace tailWord_6443680 prefixEnd_6443680 3308705023763454306066061 := by
  unfold tailWord_6443680
  simp only [CollatzResearch.WordTrace]
  refine ⟨117510158647827663887196247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156680211530436885182928329 117510158647827663887196247)
  ·
    refine ⟨176265237971741495830794371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117510158647827663887196247 176265237971741495830794371)
    ·
      refine ⟨264397856957612243746191557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176265237971741495830794371 264397856957612243746191557)
      ·
        refine ⟨49574598179552295702410917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264397856957612243746191557 49574598179552295702410917)
        ·
          refine ⟨9295237158666055444202047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49574598179552295702410917 9295237158666055444202047)
          ·
            refine ⟨13942855737999083166303071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295237158666055444202047 13942855737999083166303071)
            ·
              refine ⟨20914283606998624749454607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13942855737999083166303071 20914283606998624749454607)
              ·
                refine ⟨31371425410497937124181911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20914283606998624749454607 31371425410497937124181911)
                ·
                  refine ⟨47057138115746905686272867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31371425410497937124181911 47057138115746905686272867)
                  ·
                    refine ⟨70585707173620358529409301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47057138115746905686272867 70585707173620358529409301)
                    ·
                      refine ⟨3308705023763454306066061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70585707173620358529409301 3308705023763454306066061)
                      ·
                        rfl

theorem cell23_6443680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_6443680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443680 prefixEnd_6443680 := by exact prefixLift 6443680
  have htrace : WordTrace (prefixWord ++ tailWord_6443680) baseStart_6443680 baseEnd_6443680 := by
    simpa [prefixWord, tailWord_6443680, baseEnd_6443680] using wordTrace_append hprefix tailTrace_6443680
  have hstable : (prefixWord ++ tailWord_6443680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443680).length < 2 ^ (prefixWord ++ tailWord_6443680).sum := by decide
  have hdescent : baseEnd_6443680 < baseStart_6443680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443780 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 7]
def baseStart_6443780 : Nat := 118140960795 + 6443780 * 2 ^ 59
def prefixEnd_6443780 : Nat := 4983230072969 + 3 ^ 40 * 6443780 * 2
def baseEnd_6443780 : Nat := 367639596869878212757289

theorem tailTrace_6443780 : CollatzResearch.WordTrace tailWord_6443780 prefixEnd_6443780 367639596869878212757289 := by
  unfold tailWord_6443780
  simp only [CollatzResearch.WordTrace]
  refine ⟨117511982297646522426516397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156682643063528696568688529 117511982297646522426516397)
  ·
    refine ⟨44066993361617445909943649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117511982297646522426516397 44066993361617445909943649)
    ·
      refine ⟨33050245021213084432457737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44066993361617445909943649 33050245021213084432457737)
      ·
        refine ⟨24787683765909813324343303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33050245021213084432457737 24787683765909813324343303)
        ·
          refine ⟨37181525648864719986514955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24787683765909813324343303 37181525648864719986514955)
          ·
            refine ⟨55772288473297079979772433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37181525648864719986514955 55772288473297079979772433)
            ·
              refine ⟨41829216354972809984829325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55772288473297079979772433 41829216354972809984829325)
              ·
                refine ⟨15685956133114803744310997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41829216354972809984829325 15685956133114803744310997)
                ·
                  refine ⟨367639596869878212757289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15685956133114803744310997 367639596869878212757289)
                  ·
                    rfl

theorem cell23_6443780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_6443780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443780 prefixEnd_6443780 := by exact prefixLift 6443780
  have htrace : WordTrace (prefixWord ++ tailWord_6443780) baseStart_6443780 baseEnd_6443780 := by
    simpa [prefixWord, tailWord_6443780, baseEnd_6443780] using wordTrace_append hprefix tailTrace_6443780
  have hstable : (prefixWord ++ tailWord_6443780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443780).length < 2 ^ (prefixWord ++ tailWord_6443780).sum := by decide
  have hdescent : baseEnd_6443780 < baseStart_6443780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443890 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6443890 : Nat := 118140960795 + 6443890 * 2 ^ 59
def prefixEnd_6443890 : Nat := 4983230072969 + 3 ^ 40 * 6443890 * 2
def baseEnd_6443890 : Nat := 3308812854700898484440095

theorem tailTrace_6443890 : CollatzResearch.WordTrace tailWord_6443890 prefixEnd_6443890 3308812854700898484440095 := by
  unfold tailWord_6443890
  simp only [CollatzResearch.WordTrace]
  refine ⟨58756994156223633409884281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156685317749929689093024749 58756994156223633409884281)
  ·
    refine ⟨44067745617167725057413211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58756994156223633409884281 44067745617167725057413211)
    ·
      refine ⟨66101618425751587586119817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44067745617167725057413211 66101618425751587586119817)
      ·
        refine ⟨49576213819313690689589863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66101618425751587586119817 49576213819313690689589863)
        ·
          refine ⟨74364320728970536034384795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49576213819313690689589863 74364320728970536034384795)
          ·
            refine ⟨111546481093455804051577193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74364320728970536034384795 111546481093455804051577193)
            ·
              refine ⟨83659860820091853038682895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111546481093455804051577193 83659860820091853038682895)
              ·
                refine ⟨125489791230137779558024343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83659860820091853038682895 125489791230137779558024343)
                ·
                  refine ⟨188234686845206669337036515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125489791230137779558024343 188234686845206669337036515)
                  ·
                    refine ⟨282352030267810004005554773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188234686845206669337036515 282352030267810004005554773)
                    ·
                      refine ⟨3308812854700898484440095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 282352030267810004005554773 3308812854700898484440095)
                      ·
                        rfl

theorem cell23_6443890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6443890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443890 prefixEnd_6443890 := by exact prefixLift 6443890
  have htrace : WordTrace (prefixWord ++ tailWord_6443890) baseStart_6443890 baseEnd_6443890 := by
    simpa [prefixWord, tailWord_6443890, baseEnd_6443890] using wordTrace_append hprefix tailTrace_6443890
  have hstable : (prefixWord ++ tailWord_6443890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443890).length < 2 ^ (prefixWord ++ tailWord_6443890).sum := by decide
  have hdescent : baseEnd_6443890 < baseStart_6443890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443957 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6443957 : Nat := 118140960795 + 6443957 * 2 ^ 59
def prefixEnd_6443957 : Nat := 4983230072969 + 3 ^ 40 * 6443957 * 2
def baseEnd_6443957 : Nat := 3308847257904749722302287

theorem tailTrace_6443957 : CollatzResearch.WordTrace tailWord_6443957 prefixEnd_6443957 3308847257904749722302287 := by
  unfold tailWord_6443957
  simp only [CollatzResearch.WordTrace]
  refine ⟨235030420315651804082226125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156686946877101202721484083 235030420315651804082226125)
  ·
    refine ⟨88136407618369426530834797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235030420315651804082226125 88136407618369426530834797)
    ·
      refine ⟨33051152856888534949063049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88136407618369426530834797 33051152856888534949063049)
      ·
        refine ⟨24788364642666401211797287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33051152856888534949063049 24788364642666401211797287)
        ·
          refine ⟨37182546963999601817695931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788364642666401211797287 37182546963999601817695931)
          ·
            refine ⟨55773820445999402726543897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37182546963999601817695931 55773820445999402726543897)
            ·
              refine ⟨41830365334499552044907923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55773820445999402726543897 41830365334499552044907923)
              ·
                refine ⟨62745548001749328067361885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41830365334499552044907923 62745548001749328067361885)
                ·
                  refine ⟨23529580500655998025260707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62745548001749328067361885 23529580500655998025260707)
                  ·
                    refine ⟨35294370750983997037891061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23529580500655998025260707 35294370750983997037891061)
                    ·
                      refine ⟨3308847257904749722302287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35294370750983997037891061 3308847257904749722302287)
                      ·
                        rfl

theorem cell23_6443957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6443957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443957 prefixEnd_6443957 := by exact prefixLift 6443957
  have htrace : WordTrace (prefixWord ++ tailWord_6443957) baseStart_6443957 baseEnd_6443957 := by
    simpa [prefixWord, tailWord_6443957, baseEnd_6443957] using wordTrace_append hprefix tailTrace_6443957
  have hstable : (prefixWord ++ tailWord_6443957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443957).length < 2 ^ (prefixWord ++ tailWord_6443957).sum := by decide
  have hdescent : baseEnd_6443957 < baseStart_6443957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6443988 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_6443988 : Nat := 118140960795 + 6443988 * 2 ^ 59
def prefixEnd_6443988 : Nat := 4983230072969 + 3 ^ 40 * 6443988 * 2
def baseEnd_6443988 : Nat := 3308863175805039101014645

theorem tailTrace_6443988 : CollatzResearch.WordTrace tailWord_6443988 prefixEnd_6443988 3308863175805039101014645 := by
  unfold tailWord_6443988
  simp only [CollatzResearch.WordTrace]
  refine ⟨117515775489269748188302309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156687700652359664251069745 117515775489269748188302309)
  ·
    refine ⟨22034207904238077785306683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117515775489269748188302309 22034207904238077785306683)
    ·
      refine ⟨33051311856357116677960025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22034207904238077785306683 33051311856357116677960025)
      ·
        refine ⟨24788483892267837508470019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33051311856357116677960025 24788483892267837508470019)
        ·
          refine ⟨37182725838401756262705029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788483892267837508470019 37182725838401756262705029)
          ·
            refine ⟨6971761094700329299257193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37182725838401756262705029 6971761094700329299257193)
            ·
              refine ⟨5228820821025246974442895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6971761094700329299257193 5228820821025246974442895)
              ·
                refine ⟨7843231231537870461664343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228820821025246974442895 7843231231537870461664343)
                ·
                  refine ⟨11764846847306805692496515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7843231231537870461664343 11764846847306805692496515)
                  ·
                    refine ⟨17647270270960208538744773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11764846847306805692496515 17647270270960208538744773)
                    ·
                      refine ⟨3308863175805039101014645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17647270270960208538744773 3308863175805039101014645)
                      ·
                        rfl

theorem cell23_6443988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_6443988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6443988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6443988 prefixEnd_6443988 := by exact prefixLift 6443988
  have htrace : WordTrace (prefixWord ++ tailWord_6443988) baseStart_6443988 baseEnd_6443988 := by
    simpa [prefixWord, tailWord_6443988, baseEnd_6443988] using wordTrace_append hprefix tailTrace_6443988
  have hstable : (prefixWord ++ tailWord_6443988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6443988).length < 2 ^ (prefixWord ++ tailWord_6443988).sum := by decide
  have hdescent : baseEnd_6443988 < baseStart_6443988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6443988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444005 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6444005 : Nat := 118140960795 + 6444005 * 2 ^ 59
def prefixEnd_6444005 : Nat := 4983230072969 + 3 ^ 40 * 6444005 * 2
def baseEnd_6444005 : Nat := 3308871904976165534502067

theorem tailTrace_6444005 : CollatzResearch.WordTrace tailWord_6444005 prefixEnd_6444005 3308871904976165534502067 := by
  unfold tailWord_6444005
  simp only [CollatzResearch.WordTrace]
  refine ⟨235032171019477908279973469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156688114012985272186648979 235032171019477908279973469)
  ·
    refine ⟨88137064132304215604990051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235032171019477908279973469 88137064132304215604990051)
    ·
      refine ⟨132205596198456323407485077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88137064132304215604990051 132205596198456323407485077)
      ·
        refine ⟨6197137321802640159725863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132205596198456323407485077 6197137321802640159725863)
        ·
          refine ⟨9295705982703960239588795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197137321802640159725863 9295705982703960239588795)
          ·
            refine ⟨13943558974055940359383193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295705982703960239588795 13943558974055940359383193)
            ·
              refine ⟨10457669230541955269537395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13943558974055940359383193 10457669230541955269537395)
              ·
                refine ⟨15686503845812932904306093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10457669230541955269537395 15686503845812932904306093)
                ·
                  refine ⟨5882438942179849839114785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15686503845812932904306093 5882438942179849839114785)
                  ·
                    refine ⟨4411829206634887379336089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5882438942179849839114785 4411829206634887379336089)
                    ·
                      refine ⟨3308871904976165534502067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411829206634887379336089 3308871904976165534502067)
                      ·
                        rfl

theorem cell23_6444005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6444005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444005 prefixEnd_6444005 := by exact prefixLift 6444005
  have htrace : WordTrace (prefixWord ++ tailWord_6444005) baseStart_6444005 baseEnd_6444005 := by
    simpa [prefixWord, tailWord_6444005, baseEnd_6444005] using wordTrace_append hprefix tailTrace_6444005
  have hstable : (prefixWord ++ tailWord_6444005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444005).length < 2 ^ (prefixWord ++ tailWord_6444005).sum := by decide
  have hdescent : baseEnd_6444005 < baseStart_6444005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444018 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6444018 : Nat := 118140960795 + 6444018 * 2 ^ 59
def prefixEnd_6444018 : Nat := 4983230072969 + 3 ^ 40 * 6444018 * 2
def baseEnd_6444018 : Nat := 3308878580224673983639507

theorem tailTrace_6444018 : CollatzResearch.WordTrace tailWord_6444018 prefixEnd_6444018 3308878580224673983639507 := by
  unfold tailWord_6444018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58758161292107702875049177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156688430112287207666797805 58758161292107702875049177)
  ·
    refine ⟨44068620969080777156286883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58758161292107702875049177 44068620969080777156286883)
    ·
      refine ⟨66102931453621165734430325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44068620969080777156286883 66102931453621165734430325)
      ·
        refine ⟨6197149823776984287602843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66102931453621165734430325 6197149823776984287602843)
        ·
          refine ⟨9295724735665476431404265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197149823776984287602843 9295724735665476431404265)
          ·
            refine ⟨6971793551749107323553199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9295724735665476431404265 6971793551749107323553199)
            ·
              refine ⟨10457690327623660985329799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971793551749107323553199 10457690327623660985329799)
              ·
                refine ⟨15686535491435491477994699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10457690327623660985329799 15686535491435491477994699)
                ·
                  refine ⟨23529803237153237216992049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15686535491435491477994699 23529803237153237216992049)
                  ·
                    refine ⟨17647352427864927912744037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23529803237153237216992049 17647352427864927912744037)
                    ·
                      refine ⟨3308878580224673983639507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17647352427864927912744037 3308878580224673983639507)
                      ·
                        rfl

theorem cell23_6444018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6444018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444018 prefixEnd_6444018 := by exact prefixLift 6444018
  have htrace : WordTrace (prefixWord ++ tailWord_6444018) baseStart_6444018 baseEnd_6444018 := by
    simpa [prefixWord, tailWord_6444018, baseEnd_6444018] using wordTrace_append hprefix tailTrace_6444018
  have hstable : (prefixWord ++ tailWord_6444018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444018).length < 2 ^ (prefixWord ++ tailWord_6444018).sum := by decide
  have hdescent : baseEnd_6444018 < baseStart_6444018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444047 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_6444047 : Nat := 118140960795 + 6444047 * 2 ^ 59
def prefixEnd_6444047 : Nat := 4983230072969 + 3 ^ 40 * 6444047 * 2
def baseEnd_6444047 : Nat := 3308893471163654370176873

theorem tailTrace_6444047 : CollatzResearch.WordTrace tailWord_6444047 prefixEnd_6444047 3308893471163654370176873 := by
  unfold tailWord_6444047
  simp only [CollatzResearch.WordTrace]
  refine ⟨235033702885325749453002395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156689135256883832968668263 235033702885325749453002395)
  ·
    refine ⟨352550554327988624179503593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235033702885325749453002395 352550554327988624179503593)
    ·
      refine ⟨264412915745991468134627695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352550554327988624179503593 264412915745991468134627695)
      ·
        refine ⟨396619373618987202201941543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264412915745991468134627695 396619373618987202201941543)
        ·
          refine ⟨594929060428480803302912315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396619373618987202201941543 594929060428480803302912315)
          ·
            refine ⟨892393590642721204954368473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594929060428480803302912315 892393590642721204954368473)
            ·
              refine ⟨669295192982040903715776355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892393590642721204954368473 669295192982040903715776355)
              ·
                refine ⟨1003942789473061355573664533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669295192982040903715776355 1003942789473061355573664533)
                ·
                  refine ⟨47059818256549751042515525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1003942789473061355573664533 47059818256549751042515525)
                  ·
                    refine ⟨8823715923103078320471661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47059818256549751042515525 8823715923103078320471661)
                    ·
                      refine ⟨3308893471163654370176873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8823715923103078320471661 3308893471163654370176873)
                      ·
                        rfl

theorem cell23_6444047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_6444047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444047 prefixEnd_6444047 := by exact prefixLift 6444047
  have htrace : WordTrace (prefixWord ++ tailWord_6444047) baseStart_6444047 baseEnd_6444047 := by
    simpa [prefixWord, tailWord_6444047, baseEnd_6444047] using wordTrace_append hprefix tailTrace_6444047
  have hstable : (prefixWord ++ tailWord_6444047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444047).length < 2 ^ (prefixWord ++ tailWord_6444047).sum := by decide
  have hdescent : baseEnd_6444047 < baseStart_6444047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444057 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_6444057 : Nat := 118140960795 + 6444057 * 2 ^ 59
def prefixEnd_6444057 : Nat := 4983230072969 + 3 ^ 40 * 6444057 * 2
def baseEnd_6444057 : Nat := 3308898605970199331051827

theorem tailTrace_6444057 : CollatzResearch.WordTrace tailWord_6444057 prefixEnd_6444057 3308898605970199331051827 := by
  unfold tailWord_6444057
  simp only [CollatzResearch.WordTrace]
  refine ⟨235034067615289521160866425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156689378410193014107244283 235034067615289521160866425)
  ·
    refine ⟨176275550711467140870649819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235034067615289521160866425 176275550711467140870649819)
    ·
      refine ⟨264413326067200711305974729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176275550711467140870649819 264413326067200711305974729)
      ·
        refine ⟨198309994550400533479481047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264413326067200711305974729 198309994550400533479481047)
        ·
          refine ⟨297464991825600800219221571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198309994550400533479481047 297464991825600800219221571)
          ·
            refine ⟨446197487738401200328832357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297464991825600800219221571 446197487738401200328832357)
            ·
              refine ⟨83662028950950225061656067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 446197487738401200328832357 83662028950950225061656067)
              ·
                refine ⟨125493043426425337592484101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83662028950950225061656067 125493043426425337592484101)
                ·
                  refine ⟨23529945642454750798590769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125493043426425337592484101 23529945642454750798590769)
                  ·
                    refine ⟨17647459231841063098943077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23529945642454750798590769 17647459231841063098943077)
                    ·
                      refine ⟨3308898605970199331051827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17647459231841063098943077 3308898605970199331051827)
                      ·
                        rfl

theorem cell23_6444057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_6444057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444057 prefixEnd_6444057 := by exact prefixLift 6444057
  have htrace : WordTrace (prefixWord ++ tailWord_6444057) baseStart_6444057 baseEnd_6444057 := by
    simpa [prefixWord, tailWord_6444057, baseEnd_6444057] using wordTrace_append hprefix tailTrace_6444057
  have hstable : (prefixWord ++ tailWord_6444057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444057).length < 2 ^ (prefixWord ++ tailWord_6444057).sum := by decide
  have hdescent : baseEnd_6444057 < baseStart_6444057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444124 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6444124 : Nat := 118140960795 + 6444124 * 2 ^ 59
def prefixEnd_6444124 : Nat := 4983230072969 + 3 ^ 40 * 6444124 * 2
def baseEnd_6444124 : Nat := 3308933009174050568914019

theorem tailTrace_6444124 : CollatzResearch.WordTrace tailWord_6444124 prefixEnd_6444124 3308933009174050568914019 := by
  unfold tailWord_6444124
  simp only [CollatzResearch.WordTrace]
  refine ⟨117518255653023395801777713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156691007537364527735703617 117518255653023395801777713)
  ·
    refine ⟨88138691739767546851333285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117518255653023395801777713 88138691739767546851333285)
    ·
      refine ⟨16526004701206415034624991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88138691739767546851333285 16526004701206415034624991)
      ·
        refine ⟨24789007051809622551937487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16526004701206415034624991 24789007051809622551937487)
        ·
          refine ⟨37183510577714433827906231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24789007051809622551937487 37183510577714433827906231)
          ·
            refine ⟨55775265866571650741859347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37183510577714433827906231 55775265866571650741859347)
            ·
              refine ⟨83662898799857476112789021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55775265866571650741859347 83662898799857476112789021)
              ·
                refine ⟨31373587049946553542295883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83662898799857476112789021 31373587049946553542295883)
                ·
                  refine ⟨47060380574919830313443825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31373587049946553542295883 47060380574919830313443825)
                  ·
                    refine ⟨35295285431189872735082869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47060380574919830313443825 35295285431189872735082869)
                    ·
                      refine ⟨3308933009174050568914019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35295285431189872735082869 3308933009174050568914019)
                      ·
                        rfl

theorem cell23_6444124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6444124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444124 prefixEnd_6444124 := by exact prefixLift 6444124
  have htrace : WordTrace (prefixWord ++ tailWord_6444124) baseStart_6444124 baseEnd_6444124 := by
    simpa [prefixWord, tailWord_6444124, baseEnd_6444124] using wordTrace_append hprefix tailTrace_6444124
  have hstable : (prefixWord ++ tailWord_6444124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444124).length < 2 ^ (prefixWord ++ tailWord_6444124).sum := by decide
  have hdescent : baseEnd_6444124 < baseStart_6444124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444147 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_6444147 : Nat := 118140960795 + 6444147 * 2 ^ 59
def prefixEnd_6444147 : Nat := 4983230072969 + 3 ^ 40 * 6444147 * 2
def baseEnd_6444147 : Nat := 3308944819229103978926413

theorem tailTrace_6444147 : CollatzResearch.WordTrace tailWord_6444147 prefixEnd_6444147 3308944819229103978926413 := by
  unfold tailWord_6444147
  simp only [CollatzResearch.WordTrace]
  refine ⟨235037350184963466531642695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156691566789975644354428463 235037350184963466531642695)
  ·
    refine ⟨352556025277445199797464043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235037350184963466531642695 352556025277445199797464043)
    ·
      refine ⟨528834037916167799696196065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352556025277445199797464043 528834037916167799696196065)
      ·
        refine ⟨396625528437125849772147049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528834037916167799696196065 396625528437125849772147049)
        ·
          refine ⟨297469146327844387329110287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396625528437125849772147049 297469146327844387329110287)
          ·
            refine ⟨446203719491766580993665431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297469146327844387329110287 446203719491766580993665431)
            ·
              refine ⟨669305579237649871490498147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446203719491766580993665431 669305579237649871490498147)
              ·
                refine ⟨1003958368856474807235747221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669305579237649871490498147 1003958368856474807235747221)
                ·
                  refine ⟨47060548540147256589175651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1003958368856474807235747221 47060548540147256589175651)
                  ·
                    refine ⟨70590822810220884883763477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47060548540147256589175651 70590822810220884883763477)
                    ·
                      refine ⟨3308944819229103978926413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70590822810220884883763477 3308944819229103978926413)
                      ·
                        rfl

theorem cell23_6444147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_6444147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444147 prefixEnd_6444147 := by exact prefixLift 6444147
  have htrace : WordTrace (prefixWord ++ tailWord_6444147) baseStart_6444147 baseEnd_6444147 := by
    simpa [prefixWord, tailWord_6444147, baseEnd_6444147] using wordTrace_append hprefix tailTrace_6444147
  have hstable : (prefixWord ++ tailWord_6444147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444147).length < 2 ^ (prefixWord ++ tailWord_6444147).sum := by decide
  have hdescent : baseEnd_6444147 < baseStart_6444147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444164 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_6444164 : Nat := 118140960795 + 6444164 * 2 ^ 59
def prefixEnd_6444164 : Nat := 4983230072969 + 3 ^ 40 * 6444164 * 2
def baseEnd_6444164 : Nat := 3308953548400230412413835

theorem tailTrace_6444164 : CollatzResearch.WordTrace tailWord_6444164 prefixEnd_6444164 3308953548400230412413835 := by
  unfold tailWord_6444164
  simp only [CollatzResearch.WordTrace]
  refine ⟨117518985112950939217505773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156691980150601252290007697 117518985112950939217505773)
  ·
    refine ⟨44069619417356602206564665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117518985112950939217505773 44069619417356602206564665)
    ·
      refine ⟨33052214563017451654923499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44069619417356602206564665 33052214563017451654923499)
      ·
        refine ⟨49578321844526177482385249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33052214563017451654923499 49578321844526177482385249)
        ·
          refine ⟨37183741383394633111788937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49578321844526177482385249 37183741383394633111788937)
          ·
            refine ⟨27887806037545974833841703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37183741383394633111788937 27887806037545974833841703)
            ·
              refine ⟨41831709056318962250762555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27887806037545974833841703 41831709056318962250762555)
              ·
                refine ⟨62747563584478443376143833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41831709056318962250762555 62747563584478443376143833)
                ·
                  refine ⟨47060672688358832532107875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62747563584478443376143833 47060672688358832532107875)
                  ·
                    refine ⟨70591009032538248798161813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47060672688358832532107875 70591009032538248798161813)
                    ·
                      refine ⟨3308953548400230412413835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70591009032538248798161813 3308953548400230412413835)
                      ·
                        rfl

theorem cell23_6444164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_6444164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444164 prefixEnd_6444164 := by exact prefixLift 6444164
  have htrace : WordTrace (prefixWord ++ tailWord_6444164) baseStart_6444164 baseEnd_6444164 := by
    simpa [prefixWord, tailWord_6444164, baseEnd_6444164] using wordTrace_append hprefix tailTrace_6444164
  have hstable : (prefixWord ++ tailWord_6444164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444164).length < 2 ^ (prefixWord ++ tailWord_6444164).sum := by decide
  have hdescent : baseEnd_6444164 < baseStart_6444164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444178 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_6444178 : Nat := 118140960795 + 6444178 * 2 ^ 59
def prefixEnd_6444178 : Nat := 4983230072969 + 3 ^ 40 * 6444178 * 2
def baseEnd_6444178 : Nat := 1102986912376464452546257

theorem tailTrace_6444178 : CollatzResearch.WordTrace tailWord_6444178 prefixEnd_6444178 1102986912376464452546257 := by
  unfold tailWord_6444178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58759620211962789706505297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156692320565234105884014125 58759620211962789706505297)
  ·
    refine ⟨44069715158972092279878973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58759620211962789706505297 44069715158972092279878973)
    ·
      refine ⟨16526143184614534604954615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44069715158972092279878973 16526143184614534604954615)
      ·
        refine ⟨24789214776921801907431923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16526143184614534604954615 24789214776921801907431923)
        ·
          refine ⟨37183822165382702861147885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24789214776921801907431923 37183822165382702861147885)
          ·
            refine ⟨13943933312018513572930457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37183822165382702861147885 13943933312018513572930457)
            ·
              refine ⟨10457949984013885179697843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13943933312018513572930457 10457949984013885179697843)
              ·
                refine ⟨15686924976020827769546765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10457949984013885179697843 15686924976020827769546765)
                ·
                  refine ⟨5882596866007810413580037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15686924976020827769546765 5882596866007810413580037)
                  ·
                    refine ⟨1102986912376464452546257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882596866007810413580037 1102986912376464452546257)
                    ·
                      rfl

theorem cell23_6444178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_6444178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444178 prefixEnd_6444178 := by exact prefixLift 6444178
  have htrace : WordTrace (prefixWord ++ tailWord_6444178) baseStart_6444178 baseEnd_6444178 := by
    simpa [prefixWord, tailWord_6444178, baseEnd_6444178] using wordTrace_append hprefix tailTrace_6444178
  have hstable : (prefixWord ++ tailWord_6444178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444178).length < 2 ^ (prefixWord ++ tailWord_6444178).sum := by decide
  have hdescent : baseEnd_6444178 < baseStart_6444178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444187 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 11]
def baseStart_6444187 : Nat := 118140960795 + 6444187 * 2 ^ 59
def prefixEnd_6444187 : Nat := 4983230072969 + 3 ^ 40 * 6444187 * 2
def baseEnd_6444187 : Nat := 1102988452818427940808743

theorem tailTrace_6444187 : CollatzResearch.WordTrace tailWord_6444187 prefixEnd_6444187 1102988452818427940808743 := by
  unfold tailWord_6444187
  simp only [CollatzResearch.WordTrace]
  refine ⟨235038809104818553363098815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156692539403212368908732543 235038809104818553363098815)
  ·
    refine ⟨352558213657227830044648223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235038809104818553363098815 352558213657227830044648223)
    ·
      refine ⟨528837320485841745066972335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352558213657227830044648223 528837320485841745066972335)
      ·
        refine ⟨793255980728762617600458503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528837320485841745066972335 793255980728762617600458503)
        ·
          refine ⟨1189883971093143926400687755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793255980728762617600458503 1189883971093143926400687755)
          ·
            refine ⟨1784825956639715889601031633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189883971093143926400687755 1784825956639715889601031633)
            ·
              refine ⟨1338619467479786917200773725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784825956639715889601031633 1338619467479786917200773725)
              ·
                refine ⟨501982300304920093950290147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338619467479786917200773725 501982300304920093950290147)
                ·
                  refine ⟨752973450457380140925435221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501982300304920093950290147 752973450457380140925435221)
                  ·
                    refine ⟨1102988452818427940808743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 752973450457380140925435221 1102988452818427940808743)
                    ·
                      rfl

theorem cell23_6444187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_6444187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444187 prefixEnd_6444187 := by exact prefixLift 6444187
  have htrace : WordTrace (prefixWord ++ tailWord_6444187) baseStart_6444187 baseEnd_6444187 := by
    simpa [prefixWord, tailWord_6444187, baseEnd_6444187] using wordTrace_append hprefix tailTrace_6444187
  have hstable : (prefixWord ++ tailWord_6444187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444187).length < 2 ^ (prefixWord ++ tailWord_6444187).sum := by decide
  have hdescent : baseEnd_6444187 < baseStart_6444187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444211 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 1, 5, 2]
def baseStart_6444211 : Nat := 118140960795 + 6444211 * 2 ^ 59
def prefixEnd_6444211 : Nat := 4983230072969 + 3 ^ 40 * 6444211 * 2
def baseEnd_6444211 : Nat := 3308977681990991728526119

theorem tailTrace_6444211 : CollatzResearch.WordTrace tailWord_6444211 prefixEnd_6444211 3308977681990991728526119 := by
  unfold tailWord_6444211
  simp only [CollatzResearch.WordTrace]
  refine ⟨235039684456731605461972487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156693122971154403641314991 235039684456731605461972487)
  ·
    refine ⟨352559526685097408192958731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235039684456731605461972487 352559526685097408192958731)
    ·
      refine ⟨528839290027646112289438097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352559526685097408192958731 528839290027646112289438097)
      ·
        refine ⟨396629467520734584217078573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528839290027646112289438097 396629467520734584217078573)
        ·
          refine ⟨148736050320275469081404465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396629467520734584217078573 148736050320275469081404465)
          ·
            refine ⟨111552037740206601811053349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148736050320275469081404465 111552037740206601811053349)
            ·
              refine ⟨20916007076288737839572503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111552037740206601811053349 20916007076288737839572503)
              ·
                refine ⟨31374010614433106759358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20916007076288737839572503 31374010614433106759358755)
                ·
                  refine ⟨47061015921649660139038133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31374010614433106759358755 47061015921649660139038133)
                  ·
                    refine ⟨4411970242654655638034825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47061015921649660139038133 4411970242654655638034825)
                    ·
                      refine ⟨3308977681990991728526119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4411970242654655638034825 3308977681990991728526119)
                      ·
                        rfl

theorem cell23_6444211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5, 2].length) (baseStart_6444211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444211 prefixEnd_6444211 := by exact prefixLift 6444211
  have htrace : WordTrace (prefixWord ++ tailWord_6444211) baseStart_6444211 baseEnd_6444211 := by
    simpa [prefixWord, tailWord_6444211, baseEnd_6444211] using wordTrace_append hprefix tailTrace_6444211
  have hstable : (prefixWord ++ tailWord_6444211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444211).length < 2 ^ (prefixWord ++ tailWord_6444211).sum := by decide
  have hdescent : baseEnd_6444211 < baseStart_6444211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444221 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_6444221 : Nat := 118140960795 + 6444221 * 2 ^ 59
def prefixEnd_6444221 : Nat := 4983230072969 + 3 ^ 40 * 6444221 * 2
def baseEnd_6444221 : Nat := 1102994272265845563133691

theorem tailTrace_6444221 : CollatzResearch.WordTrace tailWord_6444221 prefixEnd_6444221 1102994272265845563133691 := by
  unfold tailWord_6444221
  simp only [CollatzResearch.WordTrace]
  refine ⟨235040049186695377169836517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156693366124463584779891011 235040049186695377169836517)
  ·
    refine ⟨44070009222505383219344347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235040049186695377169836517 44070009222505383219344347)
    ·
      refine ⟨66105013833758074829016521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44070009222505383219344347 66105013833758074829016521)
      ·
        refine ⟨49578760375318556121762391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66105013833758074829016521 49578760375318556121762391)
        ·
          refine ⟨74368140562977834182643587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49578760375318556121762391 74368140562977834182643587)
          ·
            refine ⟨111552210844466751273965381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74368140562977834182643587 111552210844466751273965381)
            ·
              refine ⟨20916039533337515863868509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111552210844466751273965381 20916039533337515863868509)
              ·
                refine ⟨7843514825001568448950691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20916039533337515863868509 7843514825001568448950691)
                ·
                  refine ⟨11765272237502352673426037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7843514825001568448950691 11765272237502352673426037)
                  ·
                    refine ⟨1102994272265845563133691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11765272237502352673426037 1102994272265845563133691)
                    ·
                      rfl

theorem cell23_6444221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_6444221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444221 prefixEnd_6444221 := by exact prefixLift 6444221
  have htrace : WordTrace (prefixWord ++ tailWord_6444221) baseStart_6444221 baseEnd_6444221 := by
    simpa [prefixWord, tailWord_6444221, baseEnd_6444221] using wordTrace_append hprefix tailTrace_6444221
  have hstable : (prefixWord ++ tailWord_6444221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444221).length < 2 ^ (prefixWord ++ tailWord_6444221).sum := by decide
  have hdescent : baseEnd_6444221 < baseStart_6444221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444264 : List Nat := [2, 1, 4, 1, 2, 1, 1, 11]
def baseStart_6444264 : Nat := 118140960795 + 6444264 * 2 ^ 59
def prefixEnd_6444264 : Nat := 4983230072969 + 3 ^ 40 * 6444264 * 2
def baseEnd_6444264 : Nat := 122555736906136297080125

theorem tailTrace_6444264 : CollatzResearch.WordTrace tailWord_6444264 prefixEnd_6444264 122555736906136297080125 := by
  unfold tailWord_6444264
  simp only [CollatzResearch.WordTrace]
  refine ⟨117520808762769797756825923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156694411683693063675767897 117520808762769797756825923)
  ·
    refine ⟨176281213144154696635238885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117520808762769797756825923 176281213144154696635238885)
    ·
      refine ⟨33052727464529005619107291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176281213144154696635238885 33052727464529005619107291)
      ·
        refine ⟨49579091196793508428660937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33052727464529005619107291 49579091196793508428660937)
        ·
          refine ⟨37184318397595131321495703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49579091196793508428660937 37184318397595131321495703)
          ·
            refine ⟨55776477596392696982243555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37184318397595131321495703 55776477596392696982243555)
            ·
              refine ⟨83664716394589045473365333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55776477596392696982243555 83664716394589045473365333)
              ·
                refine ⟨122555736906136297080125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 83664716394589045473365333 122555736906136297080125)
                ·
                  rfl

theorem cell23_6444264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 11].length) (baseStart_6444264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444264 prefixEnd_6444264 := by exact prefixLift 6444264
  have htrace : WordTrace (prefixWord ++ tailWord_6444264) baseStart_6444264 baseEnd_6444264 := by
    simpa [prefixWord, tailWord_6444264, baseEnd_6444264] using wordTrace_append hprefix tailTrace_6444264
  have hstable : (prefixWord ++ tailWord_6444264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444264).length < 2 ^ (prefixWord ++ tailWord_6444264).sum := by decide
  have hdescent : baseEnd_6444264 < baseStart_6444264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444341 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_6444341 : Nat := 118140960795 + 6444341 * 2 ^ 59
def prefixEnd_6444341 : Nat := 4983230072969 + 3 ^ 40 * 6444341 * 2
def baseEnd_6444341 : Nat := 1103014811492025406633507

theorem tailTrace_6444341 : CollatzResearch.WordTrace tailWord_6444341 prefixEnd_6444341 1103014811492025406633507 := by
  unfold tailWord_6444341
  simp only [CollatzResearch.WordTrace]
  refine ⟨235044425946260637664204877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156696283964173758442803251 235044425946260637664204877)
  ·
    refine ⟨88141659729847739124076829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235044425946260637664204877 88141659729847739124076829)
    ·
      refine ⟨33053122398692902171528811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88141659729847739124076829 33053122398692902171528811)
      ·
        refine ⟨49579683598039353257293217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33053122398692902171528811 49579683598039353257293217)
        ·
          refine ⟨37184762698529514942969913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49579683598039353257293217 37184762698529514942969913)
          ·
            refine ⟨27888572023897136207227435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37184762698529514942969913 27888572023897136207227435)
            ·
              refine ⟨41832858035845704310841153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27888572023897136207227435 41832858035845704310841153)
              ·
                refine ⟨31374643526884278233130865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41832858035845704310841153 31374643526884278233130865)
                ·
                  refine ⟨23530982645163208674848149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31374643526884278233130865 23530982645163208674848149)
                  ·
                    refine ⟨1103014811492025406633507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23530982645163208674848149 1103014811492025406633507)
                    ·
                      rfl

theorem cell23_6444341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_6444341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444341 prefixEnd_6444341 := by exact prefixLift 6444341
  have htrace : WordTrace (prefixWord ++ tailWord_6444341) baseStart_6444341 baseEnd_6444341 := by
    simpa [prefixWord, tailWord_6444341, baseEnd_6444341] using wordTrace_append hprefix tailTrace_6444341
  have hstable : (prefixWord ++ tailWord_6444341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444341).length < 2 ^ (prefixWord ++ tailWord_6444341).sum := by decide
  have hdescent : baseEnd_6444341 < baseStart_6444341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444361 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_6444361 : Nat := 118140960795 + 6444361 * 2 ^ 59
def prefixEnd_6444361 : Nat := 4983230072969 + 3 ^ 40 * 6444361 * 2
def baseEnd_6444361 : Nat := 3309054704089166141650429

theorem tailTrace_6444361 : CollatzResearch.WordTrace tailWord_6444361 prefixEnd_6444361 3309054704089166141650429 := by
  unfold tailWord_6444361
  simp only [CollatzResearch.WordTrace]
  refine ⟨235045155406188181079932937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156696770270792120719955291 235045155406188181079932937)
  ·
    refine ⟨176283866554641135809949703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235045155406188181079932937 176283866554641135809949703)
    ·
      refine ⟨264425799831961703714924555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176283866554641135809949703 264425799831961703714924555)
      ·
        refine ⟨396638699747942555572386833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264425799831961703714924555 396638699747942555572386833)
        ·
          refine ⟨297479024810956916679290125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396638699747942555572386833 297479024810956916679290125)
          ·
            refine ⟨111554634304108843754733797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297479024810956916679290125 111554634304108843754733797)
            ·
              refine ⟨20916493932020408204012587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111554634304108843754733797 20916493932020408204012587)
              ·
                refine ⟨31374740898030612306018881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20916493932020408204012587 31374740898030612306018881)
                ·
                  refine ⟨23531055673522959229514161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31374740898030612306018881 23531055673522959229514161)
                  ·
                    refine ⟨17648291755142219422135621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23531055673522959229514161 17648291755142219422135621)
                    ·
                      refine ⟨3309054704089166141650429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17648291755142219422135621 3309054704089166141650429)
                      ·
                        rfl

theorem cell23_6444361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_6444361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444361 prefixEnd_6444361 := by exact prefixLift 6444361
  have htrace : WordTrace (prefixWord ++ tailWord_6444361) baseStart_6444361 baseEnd_6444361 := by
    simpa [prefixWord, tailWord_6444361, baseEnd_6444361] using wordTrace_append hprefix tailTrace_6444361
  have hstable : (prefixWord ++ tailWord_6444361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444361).length < 2 ^ (prefixWord ++ tailWord_6444361).sum := by decide
  have hdescent : baseEnd_6444361 < baseStart_6444361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444401 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_6444401 : Nat := 118140960795 + 6444401 * 2 ^ 59
def prefixEnd_6444401 : Nat := 4983230072969 + 3 ^ 40 * 6444401 * 2
def baseEnd_6444401 : Nat := 1103025081105115328383415

theorem tailTrace_6444401 : CollatzResearch.WordTrace tailWord_6444401 prefixEnd_6444401 1103025081105115328383415 := by
  unfold tailWord_6444401
  simp only [CollatzResearch.WordTrace]
  refine ⟨235046614326043267911389057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156697742884028845274259371 235046614326043267911389057)
  ·
    refine ⟨176284960744532450933541793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235046614326043267911389057 176284960744532450933541793)
    ·
      refine ⟨132213720558399338200156345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176284960744532450933541793 132213720558399338200156345)
      ·
        refine ⟨99160290418799503650117259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132213720558399338200156345 99160290418799503650117259)
        ·
          refine ⟨148740435628199255475175889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99160290418799503650117259 148740435628199255475175889)
          ·
            refine ⟨111555326721149441606381917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148740435628199255475175889 111555326721149441606381917)
            ·
              refine ⟨41833247520431040602393219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111555326721149441606381917 41833247520431040602393219)
              ·
                refine ⟨62749871280646560903589829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41833247520431040602393219 62749871280646560903589829)
                ·
                  refine ⟨11765600865121230169423093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62749871280646560903589829 11765600865121230169423093)
                  ·
                    refine ⟨1103025081105115328383415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11765600865121230169423093 1103025081105115328383415)
                    ·
                      rfl

theorem cell23_6444401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_6444401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444401 prefixEnd_6444401 := by exact prefixLift 6444401
  have htrace : WordTrace (prefixWord ++ tailWord_6444401) baseStart_6444401 baseEnd_6444401 := by
    simpa [prefixWord, tailWord_6444401, baseEnd_6444401] using wordTrace_append hprefix tailTrace_6444401
  have hstable : (prefixWord ++ tailWord_6444401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444401).length < 2 ^ (prefixWord ++ tailWord_6444401).sum := by decide
  have hdescent : baseEnd_6444401 < baseStart_6444401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444405 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 7]
def baseStart_6444405 : Nat := 118140960795 + 6444405 * 2 ^ 59
def prefixEnd_6444405 : Nat := 4983230072969 + 3 ^ 40 * 6444405 * 2
def baseEnd_6444405 : Nat := 367675255248662663277803

theorem tailTrace_6444405 : CollatzResearch.WordTrace tailWord_6444405 prefixEnd_6444405 367675255248662663277803 := by
  unfold tailWord_6444405
  simp only [CollatzResearch.WordTrace]
  refine ⟨235046760218028776594534669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156697840145352517729689779 235046760218028776594534669)
  ·
    refine ⟨88142535081760791222950501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235046760218028776594534669 88142535081760791222950501)
    ·
      refine ⟨16526725327830148354303219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88142535081760791222950501 16526725327830148354303219)
      ·
        refine ⟨24790087991745222531454829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16526725327830148354303219 24790087991745222531454829)
        ·
          refine ⟨9296282996904458449295561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24790087991745222531454829 9296282996904458449295561)
          ·
            refine ⟨6972212247678343836971671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9296282996904458449295561 6972212247678343836971671)
            ·
              refine ⟨10458318371517515755457507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972212247678343836971671 10458318371517515755457507)
              ·
                refine ⟨15687477557276273633186261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10458318371517515755457507 15687477557276273633186261)
                ·
                  refine ⟨367675255248662663277803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15687477557276273633186261 367675255248662663277803)
                  ·
                    rfl

theorem cell23_6444405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_6444405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444405 prefixEnd_6444405 := by exact prefixLift 6444405
  have htrace : WordTrace (prefixWord ++ tailWord_6444405) baseStart_6444405 baseEnd_6444405 := by
    simpa [prefixWord, tailWord_6444405, baseEnd_6444405] using wordTrace_append hprefix tailTrace_6444405
  have hstable : (prefixWord ++ tailWord_6444405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444405).length < 2 ^ (prefixWord ++ tailWord_6444405).sum := by decide
  have hdescent : baseEnd_6444405 < baseStart_6444405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444411 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5]
def baseStart_6444411 : Nat := 118140960795 + 6444411 * 2 ^ 59
def prefixEnd_6444411 : Nat := 4983230072969 + 3 ^ 40 * 6444411 * 2
def baseEnd_6444411 : Nat := 3309080378121890946025199

theorem tailTrace_6444411 : CollatzResearch.WordTrace tailWord_6444411 prefixEnd_6444411 3309080378121890946025199 := by
  unfold tailWord_6444411
  simp only [CollatzResearch.WordTrace]
  refine ⟨235046979056007039619253087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156697986037338026412835391 235046979056007039619253087)
  ·
    refine ⟨352570468584010559428879631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235046979056007039619253087 352570468584010559428879631)
    ·
      refine ⟨528855702876015839143319447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352570468584010559428879631 528855702876015839143319447)
      ·
        refine ⟨793283554314023758714979171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528855702876015839143319447 793283554314023758714979171)
        ·
          refine ⟨1189925331471035638072468757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793283554314023758714979171 1189925331471035638072468757)
          ·
            refine ⟨55777749912704795534646973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1189925331471035638072468757 55777749912704795534646973)
            ·
              refine ⟨20916656217264298325492615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55777749912704795534646973 20916656217264298325492615)
              ·
                refine ⟨31374984325896447488238923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20916656217264298325492615 31374984325896447488238923)
                ·
                  refine ⟨47062476488844671232358385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31374984325896447488238923 47062476488844671232358385)
                  ·
                    refine ⟨35296857366633503424268789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47062476488844671232358385 35296857366633503424268789)
                    ·
                      refine ⟨3309080378121890946025199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35296857366633503424268789 3309080378121890946025199)
                      ·
                        rfl

theorem cell23_6444411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_6444411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444411 prefixEnd_6444411 := by exact prefixLift 6444411
  have htrace : WordTrace (prefixWord ++ tailWord_6444411) baseStart_6444411 baseEnd_6444411 := by
    simpa [prefixWord, tailWord_6444411, baseEnd_6444411] using wordTrace_append hprefix tailTrace_6444411
  have hstable : (prefixWord ++ tailWord_6444411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444411).length < 2 ^ (prefixWord ++ tailWord_6444411).sum := by decide
  have hdescent : baseEnd_6444411 < baseStart_6444411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444421 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_6444421 : Nat := 118140960795 + 6444421 * 2 ^ 59
def prefixEnd_6444421 : Nat := 4983230072969 + 3 ^ 40 * 6444421 * 2
def baseEnd_6444421 : Nat := 3309085512928435906900153

theorem tailTrace_6444421 : CollatzResearch.WordTrace tailWord_6444421 prefixEnd_6444421 3309085512928435906900153 := by
  unfold tailWord_6444421
  simp only [CollatzResearch.WordTrace]
  refine ⟨235047343785970811327117117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156698229190647207551411411 235047343785970811327117117)
  ·
    refine ⟨88142753919739054247668919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235047343785970811327117117 88142753919739054247668919)
    ·
      refine ⟨132214130879608581371503379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88142753919739054247668919 132214130879608581371503379)
      ·
        refine ⟨198321196319412872057255069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132214130879608581371503379 198321196319412872057255069)
        ·
          refine ⟨74370448619779827021470651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198321196319412872057255069 74370448619779827021470651)
          ·
            refine ⟨111555672929669740532205977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74370448619779827021470651 111555672929669740532205977)
            ·
              refine ⟨83666754697252305399154483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111555672929669740532205977 83666754697252305399154483)
              ·
                refine ⟨125500132045878458098731725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83666754697252305399154483 125500132045878458098731725)
                ·
                  refine ⟨47062549517204421787024397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125500132045878458098731725 47062549517204421787024397)
                  ·
                    refine ⟨17648456068951658170134149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47062549517204421787024397 17648456068951658170134149)
                    ·
                      refine ⟨3309085512928435906900153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17648456068951658170134149 3309085512928435906900153)
                      ·
                        rfl

theorem cell23_6444421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_6444421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444421 prefixEnd_6444421 := by exact prefixLift 6444421
  have htrace : WordTrace (prefixWord ++ tailWord_6444421) baseStart_6444421 baseEnd_6444421 := by
    simpa [prefixWord, tailWord_6444421, baseEnd_6444421] using wordTrace_append hprefix tailTrace_6444421
  have hstable : (prefixWord ++ tailWord_6444421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444421).length < 2 ^ (prefixWord ++ tailWord_6444421).sum := by decide
  have hdescent : baseEnd_6444421 < baseStart_6444421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444451 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_6444451 : Nat := 118140960795 + 6444451 * 2 ^ 59
def prefixEnd_6444451 : Nat := 4983230072969 + 3 ^ 40 * 6444451 * 2
def baseEnd_6444451 : Nat := 3309100917348070789525015

theorem tailTrace_6444451 : CollatzResearch.WordTrace tailWord_6444451 prefixEnd_6444451 3309100917348070789525015 := by
  unfold tailWord_6444451
  simp only [CollatzResearch.WordTrace]
  refine ⟨235048437975862126450709207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156698958650574750967139471 235048437975862126450709207)
  ·
    refine ⟨352572656963793189676063811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235048437975862126450709207 352572656963793189676063811)
    ·
      refine ⟨528858985445689784514095717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352572656963793189676063811 528858985445689784514095717)
      ·
        refine ⟨99161059771066834596392947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528858985445689784514095717 99161059771066834596392947)
        ·
          refine ⟨148741589656600251894589421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99161059771066834596392947 148741589656600251894589421)
          ·
            refine ⟨55778096121225094460471033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148741589656600251894589421 55778096121225094460471033)
            ·
              refine ⟨41833572090918820845353275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55778096121225094460471033 41833572090918820845353275)
              ·
                refine ⟨62750358136378231268029913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41833572090918820845353275 62750358136378231268029913)
                ·
                  refine ⟨47062768602283673451022435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62750358136378231268029913 47062768602283673451022435)
                  ·
                    refine ⟨70594152903425510176533653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47062768602283673451022435 70594152903425510176533653)
                    ·
                      refine ⟨3309100917348070789525015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70594152903425510176533653 3309100917348070789525015)
                      ·
                        rfl

theorem cell23_6444451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_6444451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444451 prefixEnd_6444451 := by exact prefixLift 6444451
  have htrace : WordTrace (prefixWord ++ tailWord_6444451) baseStart_6444451 baseEnd_6444451 := by
    simpa [prefixWord, tailWord_6444451, baseEnd_6444451] using wordTrace_append hprefix tailTrace_6444451
  have hstable : (prefixWord ++ tailWord_6444451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444451).length < 2 ^ (prefixWord ++ tailWord_6444451).sum := by decide
  have hdescent : baseEnd_6444451 < baseStart_6444451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444455 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_6444455 : Nat := 118140960795 + 6444455 * 2 ^ 59
def prefixEnd_6444455 : Nat := 4983230072969 + 3 ^ 40 * 6444455 * 2
def baseEnd_6444455 : Nat := 3309102971270688773874997

theorem tailTrace_6444455 : CollatzResearch.WordTrace tailWord_6444455 prefixEnd_6444455 3309102971270688773874997 := by
  unfold tailWord_6444455
  simp only [CollatzResearch.WordTrace]
  refine ⟨235048583867847635133854819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156699055911898423422569879 235048583867847635133854819)
  ·
    refine ⟨352572875801771452700782229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235048583867847635133854819 352572875801771452700782229)
    ·
      refine ⟨16526853553208036845349167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 352572875801771452700782229 16526853553208036845349167)
      ·
        refine ⟨24790280329812055268023751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16526853553208036845349167 24790280329812055268023751)
        ·
          refine ⟨37185420494718082902035627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24790280329812055268023751 37185420494718082902035627)
          ·
            refine ⟨55778130742077124353053441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37185420494718082902035627 55778130742077124353053441)
            ·
              refine ⟨41833598056557843264790081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55778130742077124353053441 41833598056557843264790081)
              ·
                refine ⟨31375198542418382448592561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41833598056557843264790081 31375198542418382448592561)
                ·
                  refine ⟨23531398906813786836444421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31375198542418382448592561 23531398906813786836444421)
                  ·
                    refine ⟨4412137295027585031833329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23531398906813786836444421 4412137295027585031833329)
                    ·
                      refine ⟨3309102971270688773874997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412137295027585031833329 3309102971270688773874997)
                      ·
                        rfl

theorem cell23_6444455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_6444455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444455 prefixEnd_6444455 := by exact prefixLift 6444455
  have htrace : WordTrace (prefixWord ++ tailWord_6444455) baseStart_6444455 baseEnd_6444455 := by
    simpa [prefixWord, tailWord_6444455, baseEnd_6444455] using wordTrace_append hprefix tailTrace_6444455
  have hstable : (prefixWord ++ tailWord_6444455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444455).length < 2 ^ (prefixWord ++ tailWord_6444455).sum := by decide
  have hdescent : baseEnd_6444455 < baseStart_6444455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444456 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 5]
def baseStart_6444456 : Nat := 118140960795 + 6444456 * 2 ^ 59
def prefixEnd_6444456 : Nat := 4983230072969 + 3 ^ 40 * 6444456 * 2
def baseEnd_6444456 : Nat := 367678164972371474440277

theorem tailTrace_6444456 : CollatzResearch.WordTrace tailWord_6444456 prefixEnd_6444456 367678164972371474440277 := by
  unfold tailWord_6444456
  simp only [CollatzResearch.WordTrace]
  refine ⟨117524310170422006152320611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156699080227229341536427481 117524310170422006152320611)
  ·
    refine ⟨176286465255633009228480917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117524310170422006152320611 176286465255633009228480917)
    ·
      refine ⟨8263428058857797307585043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176286465255633009228480917 8263428058857797307585043)
      ·
        refine ⟨12395142088286695961377565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263428058857797307585043 12395142088286695961377565)
        ·
          refine ⟨4648178283107510985516587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12395142088286695961377565 4648178283107510985516587)
          ·
            refine ⟨6972267424661266478274881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648178283107510985516587 6972267424661266478274881)
            ·
              refine ⟨5229200568495949858706161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6972267424661266478274881 5229200568495949858706161)
              ·
                refine ⟨3921900426371962394029621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229200568495949858706161 3921900426371962394029621)
                ·
                  refine ⟨367678164972371474440277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3921900426371962394029621 367678164972371474440277)
                  ·
                    rfl

theorem cell23_6444456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 5].length) (baseStart_6444456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444456 prefixEnd_6444456 := by exact prefixLift 6444456
  have htrace : WordTrace (prefixWord ++ tailWord_6444456) baseStart_6444456 baseEnd_6444456 := by
    simpa [prefixWord, tailWord_6444456, baseEnd_6444456] using wordTrace_append hprefix tailTrace_6444456
  have hstable : (prefixWord ++ tailWord_6444456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444456).length < 2 ^ (prefixWord ++ tailWord_6444456).sum := by decide
  have hdescent : baseEnd_6444456 < baseStart_6444456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444492 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6444492 : Nat := 118140960795 + 6444492 * 2 ^ 59
def prefixEnd_6444492 : Nat := 4983230072969 + 3 ^ 40 * 6444492 * 2
def baseEnd_6444492 : Nat := 3309121970054905129112327

theorem tailTrace_6444492 : CollatzResearch.WordTrace tailWord_6444492 prefixEnd_6444492 3309121970054905129112327 := by
  unfold tailWord_6444492
  simp only [CollatzResearch.WordTrace]
  refine ⟨117524966684356795226475865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156699955579142393635301153 117524966684356795226475865)
  ·
    refine ⟨88143725013267596419856899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117524966684356795226475865 88143725013267596419856899)
    ·
      refine ⟨132215587519901394629785349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88143725013267596419856899 132215587519901394629785349)
      ·
        refine ⟨24790422659981511493084753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132215587519901394629785349 24790422659981511493084753)
        ·
          refine ⟨18592816994986133619813565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24790422659981511493084753 18592816994986133619813565)
          ·
            refine ⟨6972306373119800107430087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18592816994986133619813565 6972306373119800107430087)
            ·
              refine ⟨10458459559679700161145131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972306373119800107430087 10458459559679700161145131)
              ·
                refine ⟨15687689339519550241717697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10458459559679700161145131 15687689339519550241717697)
                ·
                  refine ⟨11765767004639662681288273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15687689339519550241717697 11765767004639662681288273)
                  ·
                    refine ⟨8824325253479747010966205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11765767004639662681288273 8824325253479747010966205)
                    ·
                      refine ⟨3309121970054905129112327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8824325253479747010966205 3309121970054905129112327)
                      ·
                        rfl

theorem cell23_6444492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6444492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444492 prefixEnd_6444492 := by exact prefixLift 6444492
  have htrace : WordTrace (prefixWord ++ tailWord_6444492) baseStart_6444492 baseEnd_6444492 := by
    simpa [prefixWord, tailWord_6444492, baseEnd_6444492] using wordTrace_append hprefix tailTrace_6444492
  have hstable : (prefixWord ++ tailWord_6444492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444492).length < 2 ^ (prefixWord ++ tailWord_6444492).sum := by decide
  have hdescent : baseEnd_6444492 < baseStart_6444492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444550 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6444550 : Nat := 118140960795 + 6444550 * 2 ^ 59
def prefixEnd_6444550 : Nat := 4983230072969 + 3 ^ 40 * 6444550 * 2
def baseEnd_6444550 : Nat := 1103050583977621967395687

theorem tailTrace_6444550 : CollatzResearch.WordTrace tailWord_6444550 prefixEnd_6444550 1103050583977621967395687 := by
  unfold tailWord_6444550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7345376525078233323705097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156701365868335644239042069 7345376525078233323705097)
  ·
    refine ⟨5509032393808674992778823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7345376525078233323705097 5509032393808674992778823)
    ·
      refine ⟨8263548590713012489168235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509032393808674992778823 8263548590713012489168235)
      ·
        refine ⟨12395322886069518733752353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263548590713012489168235 12395322886069518733752353)
        ·
          refine ⟨9296492164552139050314265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12395322886069518733752353 9296492164552139050314265)
          ·
            refine ⟨6972369123414104287735699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9296492164552139050314265 6972369123414104287735699)
            ·
              refine ⟨10458553685121156431603549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972369123414104287735699 10458553685121156431603549)
              ·
                refine ⟨3921957631920433661851331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10458553685121156431603549 3921957631920433661851331)
                ·
                  refine ⟨5882936447880650492776997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921957631920433661851331 5882936447880650492776997)
                  ·
                    refine ⟨1103050583977621967395687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5882936447880650492776997 1103050583977621967395687)
                    ·
                      rfl

theorem cell23_6444550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6444550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444550 prefixEnd_6444550 := by exact prefixLift 6444550
  have htrace : WordTrace (prefixWord ++ tailWord_6444550) baseStart_6444550 baseEnd_6444550 := by
    simpa [prefixWord, tailWord_6444550, baseEnd_6444550] using wordTrace_append hprefix tailTrace_6444550
  have hstable : (prefixWord ++ tailWord_6444550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444550).length < 2 ^ (prefixWord ++ tailWord_6444550).sum := by decide
  have hdescent : baseEnd_6444550 < baseStart_6444550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444556 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 1, 1, 3]
def baseStart_6444556 : Nat := 118140960795 + 6444556 * 2 ^ 59
def prefixEnd_6444556 : Nat := 4983230072969 + 3 ^ 40 * 6444556 * 2
def baseEnd_6444556 : Nat := 3309154832816792878712033

theorem tailTrace_6444556 : CollatzResearch.WordTrace tailWord_6444556 prefixEnd_6444556 3309154832816792878712033 := by
  unfold tailWord_6444556
  simp only [CollatzResearch.WordTrace]
  refine ⟨117526133820240864691640761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156701511760321152922187681 117526133820240864691640761)
  ·
    refine ⟨88144600365180648518730571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117526133820240864691640761 88144600365180648518730571)
    ·
      refine ⟨132216900547770972778095857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88144600365180648518730571 132216900547770972778095857)
      ·
        refine ⟨99162675410828229583571893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132216900547770972778095857 99162675410828229583571893)
        ·
          refine ⟨9296500819765146523459865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99162675410828229583571893 9296500819765146523459865)
          ·
            refine ⟨6972375614823859892594899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9296500819765146523459865 6972375614823859892594899)
            ·
              refine ⟨10458563422235789838892349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972375614823859892594899 10458563422235789838892349)
              ·
                refine ⟨3921961283338421189584631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10458563422235789838892349 3921961283338421189584631)
                ·
                  refine ⟨5882941925007631784376947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921961283338421189584631 5882941925007631784376947)
                  ·
                    refine ⟨8824412887511447676565421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5882941925007631784376947 8824412887511447676565421)
                    ·
                      refine ⟨3309154832816792878712033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8824412887511447676565421 3309154832816792878712033)
                      ·
                        rfl

theorem cell23_6444556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_6444556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444556 prefixEnd_6444556 := by exact prefixLift 6444556
  have htrace : WordTrace (prefixWord ++ tailWord_6444556) baseStart_6444556 baseEnd_6444556 := by
    simpa [prefixWord, tailWord_6444556, baseEnd_6444556] using wordTrace_append hprefix tailTrace_6444556
  have hstable : (prefixWord ++ tailWord_6444556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444556).length < 2 ^ (prefixWord ++ tailWord_6444556).sum := by decide
  have hdescent : baseEnd_6444556 < baseStart_6444556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444565 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_6444565 : Nat := 118140960795 + 6444565 * 2 ^ 59
def prefixEnd_6444565 : Nat := 4983230072969 + 3 ^ 40 * 6444565 * 2
def baseEnd_6444565 : Nat := 3309159454142683343499491

theorem tailTrace_6444565 : CollatzResearch.WordTrace tailWord_6444565 prefixEnd_6444565 3309159454142683343499491 := by
  unfold tailWord_6444565
  simp only [CollatzResearch.WordTrace]
  refine ⟨235052595897449123920359149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156701730598299415946906099 235052595897449123920359149)
  ·
    refine ⟨88144723461543421470134681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235052595897449123920359149 88144723461543421470134681)
    ·
      refine ⟨66108542596157566102601011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88144723461543421470134681 66108542596157566102601011)
      ·
        refine ⟨99162813894236349153901517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66108542596157566102601011 99162813894236349153901517)
        ·
          refine ⟨37186055210338630932713069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99162813894236349153901517 37186055210338630932713069)
          ·
            refine ⟨13944770703876986599767401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37186055210338630932713069 13944770703876986599767401)
            ·
              refine ⟨10458578027907739949825551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13944770703876986599767401 10458578027907739949825551)
              ·
                refine ⟨15687867041861609924738327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10458578027907739949825551 15687867041861609924738327)
                ·
                  refine ⟨23531800562792414887107491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15687867041861609924738327 23531800562792414887107491)
                  ·
                    refine ⟨35297700844188622330661237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23531800562792414887107491 35297700844188622330661237)
                    ·
                      refine ⟨3309159454142683343499491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35297700844188622330661237 3309159454142683343499491)
                      ·
                        rfl

theorem cell23_6444565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_6444565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444565 prefixEnd_6444565 := by exact prefixLift 6444565
  have htrace : WordTrace (prefixWord ++ tailWord_6444565) baseStart_6444565 baseEnd_6444565 := by
    simpa [prefixWord, tailWord_6444565, baseEnd_6444565] using wordTrace_append hprefix tailTrace_6444565
  have hstable : (prefixWord ++ tailWord_6444565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444565).length < 2 ^ (prefixWord ++ tailWord_6444565).sum := by decide
  have hdescent : baseEnd_6444565 < baseStart_6444565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444645 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_6444645 : Nat := 118140960795 + 6444645 * 2 ^ 59
def prefixEnd_6444645 : Nat := 4983230072969 + 3 ^ 40 * 6444645 * 2
def baseEnd_6444645 : Nat := 1103066844198347676833041

theorem tailTrace_6444645 : CollatzResearch.WordTrace tailWord_6444645 prefixEnd_6444645 1103066844198347676833041 := by
  unfold tailWord_6444645
  simp only [CollatzResearch.WordTrace]
  refine ⟨235055513737159297583271389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156703675824772865055514259 235055513737159297583271389)
  ·
    refine ⟨88145817651434736593726771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235055513737159297583271389 88145817651434736593726771)
    ·
      refine ⟨132218726477152104890590157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88145817651434736593726771 132218726477152104890590157)
      ·
        refine ⟨49582022428932039333971309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132218726477152104890590157 49582022428932039333971309)
        ·
          refine ⟨18593258410849514750239241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49582022428932039333971309 18593258410849514750239241)
          ·
            refine ⟨13944943808137136062679431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18593258410849514750239241 13944943808137136062679431)
            ·
              refine ⟨20917415712205704094019147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13944943808137136062679431 20917415712205704094019147)
              ·
                refine ⟨31376123568308556141028721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20917415712205704094019147 31376123568308556141028721)
                ·
                  refine ⟨23532092676231417105771541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31376123568308556141028721 23532092676231417105771541)
                  ·
                    refine ⟨1103066844198347676833041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23532092676231417105771541 1103066844198347676833041)
                    ·
                      rfl

theorem cell23_6444645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_6444645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444645 prefixEnd_6444645 := by exact prefixLift 6444645
  have htrace : WordTrace (prefixWord ++ tailWord_6444645) baseStart_6444645 baseEnd_6444645 := by
    simpa [prefixWord, tailWord_6444645, baseEnd_6444645] using wordTrace_append hprefix tailTrace_6444645
  have hstable : (prefixWord ++ tailWord_6444645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444645).length < 2 ^ (prefixWord ++ tailWord_6444645).sum := by decide
  have hdescent : baseEnd_6444645 < baseStart_6444645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444652 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 6, 2, 2]
def baseStart_6444652 : Nat := 118140960795 + 6444652 * 2 ^ 59
def prefixEnd_6444652 : Nat := 4983230072969 + 3 ^ 40 * 6444652 * 2
def baseEnd_6444652 : Nat := 3309204126959624503111591

theorem tailTrace_6444652 : CollatzResearch.WordTrace tailWord_6444652 prefixEnd_6444652 3309204126959624503111591 := by
  unfold tailWord_6444652
  simp only [CollatzResearch.WordTrace]
  refine ⟨117527884524066968889388105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156703846032089291852517473 117527884524066968889388105)
  ·
    refine ⟨88145913393050226667041079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117527884524066968889388105 88145913393050226667041079)
    ·
      refine ⟨132218870089575340000561619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88145913393050226667041079 132218870089575340000561619)
      ·
        refine ⟨198328305134363010000842429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132218870089575340000561619 198328305134363010000842429)
        ·
          refine ⟨74373114425386128750315911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198328305134363010000842429 74373114425386128750315911)
          ·
            refine ⟨111559671638079193125473867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74373114425386128750315911 111559671638079193125473867)
            ·
              refine ⟨167339507457118789688210801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111559671638079193125473867 167339507457118789688210801)
              ·
                refine ⟨125504630592839092266158101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167339507457118789688210801 125504630592839092266158101)
                ·
                  refine ⟨5883029559039332449976161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125504630592839092266158101 5883029559039332449976161)
                  ·
                    refine ⟨4412272169279499337482121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883029559039332449976161 4412272169279499337482121)
                    ·
                      refine ⟨3309204126959624503111591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412272169279499337482121 3309204126959624503111591)
                      ·
                        rfl

theorem cell23_6444652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_6444652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444652 prefixEnd_6444652 := by exact prefixLift 6444652
  have htrace : WordTrace (prefixWord ++ tailWord_6444652) baseStart_6444652 baseEnd_6444652 := by
    simpa [prefixWord, tailWord_6444652, baseEnd_6444652] using wordTrace_append hprefix tailTrace_6444652
  have hstable : (prefixWord ++ tailWord_6444652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444652).length < 2 ^ (prefixWord ++ tailWord_6444652).sum := by decide
  have hdescent : baseEnd_6444652 < baseStart_6444652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444668 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_6444668 : Nat := 118140960795 + 6444668 * 2 ^ 59
def prefixEnd_6444668 : Nat := 4983230072969 + 3 ^ 40 * 6444668 * 2
def baseEnd_6444668 : Nat := 3309212342650096440511517

theorem tailTrace_6444668 : CollatzResearch.WordTrace tailWord_6444668 prefixEnd_6444668 3309212342650096440511517 := by
  unfold tailWord_6444668
  simp only [CollatzResearch.WordTrace]
  refine ⟨117528176308037986255679329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156704235077383981674239105 117528176308037986255679329)
  ·
    refine ⟨88146132231028489691759497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117528176308037986255679329 88146132231028489691759497)
    ·
      refine ⟨66109599173271367268819623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88146132231028489691759497 66109599173271367268819623)
      ·
        refine ⟨99164398759907050903229435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66109599173271367268819623 99164398759907050903229435)
        ·
          refine ⟨148746598139860576354844153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99164398759907050903229435 148746598139860576354844153)
          ·
            refine ⟨111559948604895432266133115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148746598139860576354844153 111559948604895432266133115)
            ·
              refine ⟨167339922907343148399199673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111559948604895432266133115 167339922907343148399199673)
              ·
                refine ⟨125504942180507361299399755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167339922907343148399199673 125504942180507361299399755)
                ·
                  refine ⟨188257413270761041949099633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125504942180507361299399755 188257413270761041949099633)
                  ·
                    refine ⟨141193059953070781461824725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188257413270761041949099633 141193059953070781461824725)
                    ·
                      refine ⟨3309212342650096440511517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141193059953070781461824725 3309212342650096440511517)
                      ·
                        rfl

theorem cell23_6444668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_6444668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444668 prefixEnd_6444668 := by exact prefixLift 6444668
  have htrace : WordTrace (prefixWord ++ tailWord_6444668) baseStart_6444668 baseEnd_6444668 := by
    simpa [prefixWord, tailWord_6444668, baseEnd_6444668] using wordTrace_append hprefix tailTrace_6444668
  have hstable : (prefixWord ++ tailWord_6444668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444668).length < 2 ^ (prefixWord ++ tailWord_6444668).sum := by decide
  have hdescent : baseEnd_6444668 < baseStart_6444668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444686 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6444686 : Nat := 118140960795 + 6444686 * 2 ^ 59
def prefixEnd_6444686 : Nat := 4983230072969 + 3 ^ 40 * 6444686 * 2
def baseEnd_6444686 : Nat := 3309221585301877370086435

theorem tailTrace_6444686 : CollatzResearch.WordTrace tailWord_6444686 prefixEnd_6444686 3309221585301877370086435 := by
  unfold tailWord_6444686
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382126141251345198189239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156704672753340507723675941 29382126141251345198189239)
  ·
    refine ⟨44073189211877017797283859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29382126141251345198189239 44073189211877017797283859)
    ·
      refine ⟨66109783817815526695925789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44073189211877017797283859 66109783817815526695925789)
      ·
        refine ⟨24791168931680822510972171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66109783817815526695925789 24791168931680822510972171)
        ·
          refine ⟨37186753397521233766458257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24791168931680822510972171 37186753397521233766458257)
          ·
            refine ⟨27890065048140925324843693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37186753397521233766458257 27890065048140925324843693)
            ·
              refine ⟨10458774393052846996816385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27890065048140925324843693 10458774393052846996816385)
              ·
                refine ⟨7844080794789635247612289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10458774393052846996816385 7844080794789635247612289)
                ·
                  refine ⟨5883060596092226435709217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7844080794789635247612289 5883060596092226435709217)
                  ·
                    refine ⟨4412295447069169826781913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883060596092226435709217 4412295447069169826781913)
                    ·
                      refine ⟨3309221585301877370086435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412295447069169826781913 3309221585301877370086435)
                      ·
                        rfl

theorem cell23_6444686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6444686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444686 prefixEnd_6444686 := by exact prefixLift 6444686
  have htrace : WordTrace (prefixWord ++ tailWord_6444686) baseStart_6444686 baseEnd_6444686 := by
    simpa [prefixWord, tailWord_6444686, baseEnd_6444686] using wordTrace_append hprefix tailTrace_6444686
  have hstable : (prefixWord ++ tailWord_6444686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444686).length < 2 ^ (prefixWord ++ tailWord_6444686).sum := by decide
  have hdescent : baseEnd_6444686 < baseStart_6444686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444703 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6444703 : Nat := 118140960795 + 6444703 * 2 ^ 59
def prefixEnd_6444703 : Nat := 4983230072969 + 3 ^ 40 * 6444703 * 2
def baseEnd_6444703 : Nat := 3309230314473003803573857

theorem tailTrace_6444703 : CollatzResearch.WordTrace tailWord_6444703 prefixEnd_6444703 3309230314473003803573857 := by
  unfold tailWord_6444703
  simp only [CollatzResearch.WordTrace]
  refine ⟨235057629170949173488882763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156705086113966115659255175 235057629170949173488882763)
  ·
    refine ⟨352586443756423760233324145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235057629170949173488882763 352586443756423760233324145)
    ·
      refine ⟨264439832817317820174993109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352586443756423760233324145 264439832817317820174993109)
      ·
        refine ⟨6197808581655886410351401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 264439832817317820174993109 6197808581655886410351401)
        ·
          refine ⟨4648356436241914807763551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6197808581655886410351401 4648356436241914807763551)
          ·
            refine ⟨6972534654362872211645327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648356436241914807763551 6972534654362872211645327)
            ·
              refine ⟨10458801981544308317467991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972534654362872211645327 10458801981544308317467991)
              ·
                refine ⟨15688202972316462476201987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10458801981544308317467991 15688202972316462476201987)
                ·
                  refine ⟨23532304458474693714302981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15688202972316462476201987 23532304458474693714302981)
                  ·
                    refine ⟨4412307085964005071431809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23532304458474693714302981 4412307085964005071431809)
                    ·
                      refine ⟨3309230314473003803573857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412307085964005071431809 3309230314473003803573857)
                      ·
                        rfl

theorem cell23_6444703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6444703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444703 prefixEnd_6444703 := by exact prefixLift 6444703
  have htrace : WordTrace (prefixWord ++ tailWord_6444703) baseStart_6444703 baseEnd_6444703 := by
    simpa [prefixWord, tailWord_6444703, baseEnd_6444703] using wordTrace_append hprefix tailTrace_6444703
  have hstable : (prefixWord ++ tailWord_6444703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444703).length < 2 ^ (prefixWord ++ tailWord_6444703).sum := by decide
  have hdescent : baseEnd_6444703 < baseStart_6444703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444705 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_6444705 : Nat := 118140960795 + 6444705 * 2 ^ 59
def prefixEnd_6444705 : Nat := 4983230072969 + 3 ^ 40 * 6444705 * 2
def baseEnd_6444705 : Nat := 1103077113811437598582949

theorem tailTrace_6444705 : CollatzResearch.WordTrace tailWord_6444705 prefixEnd_6444705 1103077113811437598582949 := by
  unfold tailWord_6444705
  simp only [CollatzResearch.WordTrace]
  refine ⟨235057702116941927830455569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156705134744627951886970379 235057702116941927830455569)
  ·
    refine ⟨176293276587706445872841677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235057702116941927830455569 176293276587706445872841677)
    ·
      refine ⟨66109978720389917202315629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176293276587706445872841677 66109978720389917202315629)
      ·
        refine ⟨24791242020146218950868361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66109978720389917202315629 24791242020146218950868361)
        ·
          refine ⟨18593431515109664213151271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24791242020146218950868361 18593431515109664213151271)
          ·
            refine ⟨27890147272664496319726907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18593431515109664213151271 27890147272664496319726907)
            ·
              refine ⟨41835220908996744479590361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27890147272664496319726907 41835220908996744479590361)
              ·
                refine ⟨31376415681747558359692771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41835220908996744479590361 31376415681747558359692771)
                ·
                  refine ⟨47064623522621337539539157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31376415681747558359692771 47064623522621337539539157)
                  ·
                    refine ⟨1103077113811437598582949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47064623522621337539539157 1103077113811437598582949)
                    ·
                      rfl

theorem cell23_6444705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_6444705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444705 prefixEnd_6444705 := by exact prefixLift 6444705
  have htrace : WordTrace (prefixWord ++ tailWord_6444705) baseStart_6444705 baseEnd_6444705 := by
    simpa [prefixWord, tailWord_6444705, baseEnd_6444705] using wordTrace_append hprefix tailTrace_6444705
  have hstable : (prefixWord ++ tailWord_6444705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444705).length < 2 ^ (prefixWord ++ tailWord_6444705).sum := by decide
  have hdescent : baseEnd_6444705 < baseStart_6444705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444726 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_6444726 : Nat := 118140960795 + 6444726 * 2 ^ 59
def prefixEnd_6444726 : Nat := 4983230072969 + 3 ^ 40 * 6444726 * 2
def baseEnd_6444726 : Nat := 367693569392006357065139

theorem tailTrace_6444726 : CollatzResearch.WordTrace tailWord_6444726 prefixEnd_6444726 367693569392006357065139 := by
  unfold tailWord_6444726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691154253116615526060627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156705645366577232277980021 14691154253116615526060627)
  ·
    refine ⟨22036731379674923289090941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14691154253116615526060627 22036731379674923289090941)
    ·
      refine ⟨8263774267378096233409103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22036731379674923289090941 8263774267378096233409103)
      ·
        refine ⟨12395661401067144350113655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263774267378096233409103 12395661401067144350113655)
        ·
          refine ⟨18593492101600716525170483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12395661401067144350113655 18593492101600716525170483)
          ·
            refine ⟨27890238152401074787755725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18593492101600716525170483 27890238152401074787755725)
            ·
              refine ⟨10458839307150403045408397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27890238152401074787755725 10458839307150403045408397)
              ·
                refine ⟨3922064740181401142028149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10458839307150403045408397 3922064740181401142028149)
                ·
                  refine ⟨367693569392006357065139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922064740181401142028149 367693569392006357065139)
                  ·
                    rfl

theorem cell23_6444726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_6444726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444726 prefixEnd_6444726 := by exact prefixLift 6444726
  have htrace : WordTrace (prefixWord ++ tailWord_6444726) baseStart_6444726 baseEnd_6444726 := by
    simpa [prefixWord, tailWord_6444726, baseEnd_6444726] using wordTrace_append hprefix tailTrace_6444726
  have hstable : (prefixWord ++ tailWord_6444726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444726).length < 2 ^ (prefixWord ++ tailWord_6444726).sum := by decide
  have hdescent : baseEnd_6444726 < baseStart_6444726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444749 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6444749 : Nat := 118140960795 + 6444749 * 2 ^ 59
def prefixEnd_6444749 : Nat := 4983230072969 + 3 ^ 40 * 6444749 * 2
def baseEnd_6444749 : Nat := 3309253934583110623598645

theorem tailTrace_6444749 : CollatzResearch.WordTrace tailWord_6444749 prefixEnd_6444749 3309253934583110623598645 := by
  unfold tailWord_6444749
  simp only [CollatzResearch.WordTrace]
  refine ⟨235059306928782523345057301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156706204619188348896704867 235059306928782523345057301)
  ·
    refine ⟨11018405012286680781799561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235059306928782523345057301 11018405012286680781799561)
    ·
      refine ⟨8263803759215010586349671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11018405012286680781799561 8263803759215010586349671)
      ·
        refine ⟨12395705638822515879524507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263803759215010586349671 12395705638822515879524507)
        ·
          refine ⟨18593558458233773819286761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12395705638822515879524507 18593558458233773819286761)
          ·
            refine ⟨13945168843675330364465071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18593558458233773819286761 13945168843675330364465071)
            ·
              refine ⟨20917753265512995546697607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945168843675330364465071 20917753265512995546697607)
              ·
                refine ⟨31376629898269493320046411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20917753265512995546697607 31376629898269493320046411)
                ·
                  refine ⟨47064944847404239980069617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31376629898269493320046411 47064944847404239980069617)
                  ·
                    refine ⟨35298708635553179985052213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47064944847404239980069617 35298708635553179985052213)
                    ·
                      refine ⟨3309253934583110623598645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35298708635553179985052213 3309253934583110623598645)
                      ·
                        rfl

theorem cell23_6444749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6444749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444749 prefixEnd_6444749 := by exact prefixLift 6444749
  have htrace : WordTrace (prefixWord ++ tailWord_6444749) baseStart_6444749 baseEnd_6444749 := by
    simpa [prefixWord, tailWord_6444749, baseEnd_6444749] using wordTrace_append hprefix tailTrace_6444749
  have hstable : (prefixWord ++ tailWord_6444749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444749).length < 2 ^ (prefixWord ++ tailWord_6444749).sum := by decide
  have hdescent : baseEnd_6444749 < baseStart_6444749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444792 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_6444792 : Nat := 118140960795 + 6444792 * 2 ^ 59
def prefixEnd_6444792 : Nat := 4983230072969 + 3 ^ 40 * 6444792 * 2
def baseEnd_6444792 : Nat := 3309276014251253955360947

theorem tailTrace_6444792 : CollatzResearch.WordTrace tailWord_6444792 prefixEnd_6444792 3309276014251253955360947 := by
  unfold tailWord_6444792
  simp only [CollatzResearch.WordTrace]
  refine ⟨117530437633813370844436315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156707250178417827792581753 117530437633813370844436315)
  ·
    refine ⟨176295656450720056266654473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117530437633813370844436315 176295656450720056266654473)
    ·
      refine ⟨132221742338040042199990855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176295656450720056266654473 132221742338040042199990855)
      ·
        refine ⟨198332613507060063299986283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132221742338040042199990855 198332613507060063299986283)
        ·
          refine ⟨297498920260590094949979425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198332613507060063299986283 297498920260590094949979425)
          ·
            refine ⟨223124190195442571212484569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297498920260590094949979425 223124190195442571212484569)
            ·
              refine ⟨167343142646581928409363427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223124190195442571212484569 167343142646581928409363427)
              ·
                refine ⟨251014713969872892614045141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167343142646581928409363427 251014713969872892614045141)
                ·
                  refine ⟨5883157358668895920641683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 251014713969872892614045141 5883157358668895920641683)
                  ·
                    refine ⟨8824736038003343880962525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5883157358668895920641683 8824736038003343880962525)
                    ·
                      refine ⟨3309276014251253955360947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8824736038003343880962525 3309276014251253955360947)
                      ·
                        rfl

theorem cell23_6444792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_6444792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444792 prefixEnd_6444792 := by exact prefixLift 6444792
  have htrace : WordTrace (prefixWord ++ tailWord_6444792) baseStart_6444792 baseEnd_6444792 := by
    simpa [prefixWord, tailWord_6444792, baseEnd_6444792] using wordTrace_append hprefix tailTrace_6444792
  have hstable : (prefixWord ++ tailWord_6444792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444792).length < 2 ^ (prefixWord ++ tailWord_6444792).sum := by decide
  have hdescent : baseEnd_6444792 < baseStart_6444792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444802 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_6444802 : Nat := 118140960795 + 6444802 * 2 ^ 59
def prefixEnd_6444802 : Nat := 4983230072969 + 3 ^ 40 * 6444802 * 2
def baseEnd_6444802 : Nat := 3309281149057798916235901

theorem tailTrace_6444802 : CollatzResearch.WordTrace tailWord_6444802 prefixEnd_6444802 3309281149057798916235901 := by
  unfold tailWord_6444802
  simp only [CollatzResearch.WordTrace]
  refine ⟨58765309999397628349184165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156707493331727008931157773 58765309999397628349184165)
  ·
    refine ⟨11018495624887055315472031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58765309999397628349184165 11018495624887055315472031)
    ·
      refine ⟨16527743437330582973208047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11018495624887055315472031 16527743437330582973208047)
      ·
        refine ⟨24791615155995874459812071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16527743437330582973208047 24791615155995874459812071)
        ·
          refine ⟨37187422733993811689718107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24791615155995874459812071 37187422733993811689718107)
          ·
            refine ⟨55781134100990717534577161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37187422733993811689718107 55781134100990717534577161)
            ·
              refine ⟨41835850575743038150932871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55781134100990717534577161 41835850575743038150932871)
              ·
                refine ⟨62753775863614557226399307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41835850575743038150932871 62753775863614557226399307)
                ·
                  refine ⟨94130663795421835839598961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62753775863614557226399307 94130663795421835839598961)
                  ·
                    refine ⟨70597997846566376879699221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94130663795421835839598961 70597997846566376879699221)
                    ·
                      refine ⟨3309281149057798916235901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70597997846566376879699221 3309281149057798916235901)
                      ·
                        rfl

theorem cell23_6444802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_6444802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444802 prefixEnd_6444802 := by exact prefixLift 6444802
  have htrace : WordTrace (prefixWord ++ tailWord_6444802) baseStart_6444802 baseEnd_6444802 := by
    simpa [prefixWord, tailWord_6444802, baseEnd_6444802] using wordTrace_append hprefix tailTrace_6444802
  have hstable : (prefixWord ++ tailWord_6444802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444802).length < 2 ^ (prefixWord ++ tailWord_6444802).sum := by decide
  have hdescent : baseEnd_6444802 < baseStart_6444802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444830 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6444830 : Nat := 118140960795 + 6444830 * 2 ^ 59
def prefixEnd_6444830 : Nat := 4983230072969 + 3 ^ 40 * 6444830 * 2
def baseEnd_6444830 : Nat := 3309295526516124806685773

theorem tailTrace_6444830 : CollatzResearch.WordTrace tailWord_6444830 prefixEnd_6444830 3309295526516124806685773 := by
  unfold tailWord_6444830
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382782655186134272344493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156708174160992716119170629 29382782655186134272344493)
  ·
    refine ⟨11018543495694800352129185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29382782655186134272344493 11018543495694800352129185)
    ·
      refine ⟨8263907621771100264096889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11018543495694800352129185 8263907621771100264096889)
      ·
        refine ⟨6197930716328325198072667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8263907621771100264096889 6197930716328325198072667)
        ·
          refine ⟨9296896074492487797109001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197930716328325198072667 9296896074492487797109001)
          ·
            refine ⟨6972672055869365847831751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9296896074492487797109001 6972672055869365847831751)
            ·
              refine ⟨10459008083804048771747627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972672055869365847831751 10459008083804048771747627)
              ·
                refine ⟨15688512125706073157621441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459008083804048771747627 15688512125706073157621441)
                ·
                  refine ⟨11766384094279554868216081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15688512125706073157621441 11766384094279554868216081)
                  ·
                    refine ⟨8824788070709666151162061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11766384094279554868216081 8824788070709666151162061)
                    ·
                      refine ⟨3309295526516124806685773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8824788070709666151162061 3309295526516124806685773)
                      ·
                        rfl

theorem cell23_6444830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6444830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444830 prefixEnd_6444830 := by exact prefixLift 6444830
  have htrace : WordTrace (prefixWord ++ tailWord_6444830) baseStart_6444830 baseEnd_6444830 := by
    simpa [prefixWord, tailWord_6444830, baseEnd_6444830] using wordTrace_append hprefix tailTrace_6444830
  have hstable : (prefixWord ++ tailWord_6444830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444830).length < 2 ^ (prefixWord ++ tailWord_6444830).sum := by decide
  have hdescent : baseEnd_6444830 < baseStart_6444830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444832 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6444832 : Nat := 118140960795 + 6444832 * 2 ^ 59
def prefixEnd_6444832 : Nat := 4983230072969 + 3 ^ 40 * 6444832 * 2
def baseEnd_6444832 : Nat := 3309296553477433798860763

theorem tailTrace_6444832 : CollatzResearch.WordTrace tailWord_6444832 prefixEnd_6444832 3309296553477433798860763 := by
  unfold tailWord_6444832
  simp only [CollatzResearch.WordTrace]
  refine ⟨117531167093740914260164375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156708222791654552346885833 117531167093740914260164375)
  ·
    refine ⟨176296750640611371390246563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117531167093740914260164375 176296750640611371390246563)
    ·
      refine ⟨264445125960917057085369845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176296750640611371390246563 264445125960917057085369845)
      ·
        refine ⟨24791730558835974101753423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264445125960917057085369845 24791730558835974101753423)
        ·
          refine ⟨37187595838253961152630135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24791730558835974101753423 37187595838253961152630135)
          ·
            refine ⟨55781393757380941728945203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37187595838253961152630135 55781393757380941728945203)
            ·
              refine ⟨83672090636071412593417805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55781393757380941728945203 83672090636071412593417805)
              ·
                refine ⟨31377033988526779722531677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83672090636071412593417805 31377033988526779722531677)
                ·
                  refine ⟨11766387745697542395949379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31377033988526779722531677 11766387745697542395949379)
                  ·
                    refine ⟨17649581618546313593924069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11766387745697542395949379 17649581618546313593924069)
                    ·
                      refine ⟨3309296553477433798860763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17649581618546313593924069 3309296553477433798860763)
                      ·
                        rfl

theorem cell23_6444832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6444832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444832 prefixEnd_6444832 := by exact prefixLift 6444832
  have htrace : WordTrace (prefixWord ++ tailWord_6444832) baseStart_6444832 baseEnd_6444832 := by
    simpa [prefixWord, tailWord_6444832, baseEnd_6444832] using wordTrace_append hprefix tailTrace_6444832
  have hstable : (prefixWord ++ tailWord_6444832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444832).length < 2 ^ (prefixWord ++ tailWord_6444832).sum := by decide
  have hdescent : baseEnd_6444832 < baseStart_6444832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444836 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_6444836 : Nat := 118140960795 + 6444836 * 2 ^ 59
def prefixEnd_6444836 : Nat := 4983230072969 + 3 ^ 40 * 6444836 * 2
def baseEnd_6444836 : Nat := 3309298607400051783210745

theorem tailTrace_6444836 : CollatzResearch.WordTrace tailWord_6444836 prefixEnd_6444836 3309298607400051783210745 := by
  unfold tailWord_6444836
  simp only [CollatzResearch.WordTrace]
  refine ⟨117531240039733668601737181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156708320052978224802316241 117531240039733668601737181)
  ·
    refine ⟨44074215014900125725651443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117531240039733668601737181 44074215014900125725651443)
    ·
      refine ⟨66111322522350188588477165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44074215014900125725651443 66111322522350188588477165)
      ·
        refine ⟨24791745945881320720678937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66111322522350188588477165 24791745945881320720678937)
        ·
          refine ⟨18593809459410990540509203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24791745945881320720678937 18593809459410990540509203)
          ·
            refine ⟨27890714189116485810763805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18593809459410990540509203 27890714189116485810763805)
            ·
              refine ⟨10459017820918682179036427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27890714189116485810763805 10459017820918682179036427)
              ·
                refine ⟨15688526731378023268554641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459017820918682179036427 15688526731378023268554641)
                ·
                  refine ⟨11766395048533517451415981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15688526731378023268554641 11766395048533517451415981)
                  ·
                    refine ⟨4412398143200069044280993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11766395048533517451415981 4412398143200069044280993)
                    ·
                      refine ⟨3309298607400051783210745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412398143200069044280993 3309298607400051783210745)
                      ·
                        rfl

theorem cell23_6444836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_6444836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444836 prefixEnd_6444836 := by exact prefixLift 6444836
  have htrace : WordTrace (prefixWord ++ tailWord_6444836) baseStart_6444836 baseEnd_6444836 := by
    simpa [prefixWord, tailWord_6444836, baseEnd_6444836] using wordTrace_append hprefix tailTrace_6444836
  have hstable : (prefixWord ++ tailWord_6444836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444836).length < 2 ^ (prefixWord ++ tailWord_6444836).sum := by decide
  have hdescent : baseEnd_6444836 < baseStart_6444836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444846 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6444846 : Nat := 118140960795 + 6444846 * 2 ^ 59
def prefixEnd_6444846 : Nat := 4983230072969 + 3 ^ 40 * 6444846 * 2
def baseEnd_6444846 : Nat := 1103101247402198914695233

theorem tailTrace_6444846 : CollatzResearch.WordTrace tailWord_6444846 prefixEnd_6444846 1103101247402198914695233 := by
  unfold tailWord_6444846
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382855601178888613917299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156708563206287405940892261 29382855601178888613917299)
  ·
    refine ⟨44074283401768332920875949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29382855601178888613917299 44074283401768332920875949)
    ·
      refine ⟨16527856275663124845328481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44074283401768332920875949 16527856275663124845328481)
      ·
        refine ⟨12395892206747343633996361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16527856275663124845328481 12395892206747343633996361)
        ·
          refine ⟨9296919155060507725497271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12395892206747343633996361 9296919155060507725497271)
          ·
            refine ⟨13945378732590761588245907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9296919155060507725497271 13945378732590761588245907)
            ·
              refine ⟨20918068098886142382368861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945378732590761588245907 20918068098886142382368861)
              ·
                refine ⟨7844275537082303393388323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20918068098886142382368861 7844275537082303393388323)
                ·
                  refine ⟨11766413305623455090082485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7844275537082303393388323 11766413305623455090082485)
                  ·
                    refine ⟨1103101247402198914695233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11766413305623455090082485 1103101247402198914695233)
                    ·
                      rfl

theorem cell23_6444846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6444846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444846 prefixEnd_6444846 := by exact prefixLift 6444846
  have htrace : WordTrace (prefixWord ++ tailWord_6444846) baseStart_6444846 baseEnd_6444846 := by
    simpa [prefixWord, tailWord_6444846, baseEnd_6444846] using wordTrace_append hprefix tailTrace_6444846
  have hstable : (prefixWord ++ tailWord_6444846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444846).length < 2 ^ (prefixWord ++ tailWord_6444846).sum := by decide
  have hdescent : baseEnd_6444846 < baseStart_6444846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444849 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_6444849 : Nat := 118140960795 + 6444849 * 2 ^ 59
def prefixEnd_6444849 : Nat := 4983230072969 + 3 ^ 40 * 6444849 * 2
def baseEnd_6444849 : Nat := 3309305282648560232348185

theorem tailTrace_6444849 : CollatzResearch.WordTrace tailWord_6444849 prefixEnd_6444849 3309305282648560232348185 := by
  unfold tailWord_6444849
  simp only [CollatzResearch.WordTrace]
  refine ⟨235062954228420240423697601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156708636152280160282465067 235062954228420240423697601)
  ·
    refine ⟨176297215671315180317773201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235062954228420240423697601 176297215671315180317773201)
    ·
      refine ⟨132222911753486385238329901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176297215671315180317773201 132222911753486385238329901)
      ·
        refine ⟨49583591907557394464373713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132222911753486385238329901 49583591907557394464373713)
        ·
          refine ⟨37187693930668045848280285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49583591907557394464373713 37187693930668045848280285)
          ·
            refine ⟨13945385224000517193105107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37187693930668045848280285 13945385224000517193105107)
            ·
              refine ⟨20918077836000775789657661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945385224000517193105107 20918077836000775789657661)
              ·
                refine ⟨7844279188500290921121623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20918077836000775789657661 7844279188500290921121623)
                ·
                  refine ⟨11766418782750436381682435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7844279188500290921121623 11766418782750436381682435)
                  ·
                    refine ⟨17649628174125654572523653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11766418782750436381682435 17649628174125654572523653)
                    ·
                      refine ⟨3309305282648560232348185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17649628174125654572523653 3309305282648560232348185)
                      ·
                        rfl

theorem cell23_6444849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_6444849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444849 prefixEnd_6444849 := by exact prefixLift 6444849
  have htrace : WordTrace (prefixWord ++ tailWord_6444849) baseStart_6444849 baseEnd_6444849 := by
    simpa [prefixWord, tailWord_6444849, baseEnd_6444849] using wordTrace_append hprefix tailTrace_6444849
  have hstable : (prefixWord ++ tailWord_6444849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444849).length < 2 ^ (prefixWord ++ tailWord_6444849).sum := by decide
  have hdescent : baseEnd_6444849 < baseStart_6444849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444876 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_6444876 : Nat := 118140960795 + 6444876 * 2 ^ 59
def prefixEnd_6444876 : Nat := 4983230072969 + 3 ^ 40 * 6444876 * 2
def baseEnd_6444876 : Nat := 1103106382208743875570187

theorem tailTrace_6444876 : CollatzResearch.WordTrace tailWord_6444876 prefixEnd_6444876 1103106382208743875570187 := by
  unfold tailWord_6444876
  simp only [CollatzResearch.WordTrace]
  refine ⟨117531969499661212017465241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156709292666214949356620321 117531969499661212017465241)
  ·
    refine ⟨88148977124745909013098931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117531969499661212017465241 88148977124745909013098931)
    ·
      refine ⟨132223465687118863519648397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88148977124745909013098931 132223465687118863519648397)
      ·
        refine ⟨49583799632669573819868149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132223465687118863519648397 49583799632669573819868149)
        ·
          refine ⟨4648481215562772545612639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49583799632669573819868149 4648481215562772545612639)
          ·
            refine ⟨6972721823344158818418959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648481215562772545612639 6972721823344158818418959)
            ·
              refine ⟨10459082735016238227628439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972721823344158818418959 10459082735016238227628439)
              ·
                refine ⟨15688624102524357341442659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459082735016238227628439 15688624102524357341442659)
                ·
                  refine ⟨23532936153786536012163989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15688624102524357341442659 23532936153786536012163989)
                  ·
                    refine ⟨1103106382208743875570187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23532936153786536012163989 1103106382208743875570187)
                    ·
                      rfl

theorem cell23_6444876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_6444876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444876 prefixEnd_6444876 := by exact prefixLift 6444876
  have htrace : WordTrace (prefixWord ++ tailWord_6444876) baseStart_6444876 baseEnd_6444876 := by
    simpa [prefixWord, tailWord_6444876, baseEnd_6444876] using wordTrace_append hprefix tailTrace_6444876
  have hstable : (prefixWord ++ tailWord_6444876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444876).length < 2 ^ (prefixWord ++ tailWord_6444876).sum := by decide
  have hdescent : baseEnd_6444876 < baseStart_6444876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444905 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_6444905 : Nat := 118140960795 + 6444905 * 2 ^ 59
def prefixEnd_6444905 : Nat := 4983230072969 + 3 ^ 40 * 6444905 * 2
def baseEnd_6444905 : Nat := 3309334037565212013247927

theorem tailTrace_6444905 : CollatzResearch.WordTrace tailWord_6444905 prefixEnd_6444905 3309334037565212013247927 := by
  unfold tailWord_6444905
  simp only [CollatzResearch.WordTrace]
  refine ⟨235064996716217361987736169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156709997810811574658490779 235064996716217361987736169)
  ·
    refine ⟨176298747537163021490802127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235064996716217361987736169 176298747537163021490802127)
    ·
      refine ⟨264448121305744532236203191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176298747537163021490802127 264448121305744532236203191)
      ·
        refine ⟨396672181958616798354304787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264448121305744532236203191 396672181958616798354304787)
        ·
          refine ⟨595008272937925197531457181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396672181958616798354304787 595008272937925197531457181)
          ·
            refine ⟨223128102351721949074296443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595008272937925197531457181 223128102351721949074296443)
            ·
              refine ⟨334692153527582923611444665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223128102351721949074296443 334692153527582923611444665)
              ·
                refine ⟨251019115145687192708583499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334692153527582923611444665 251019115145687192708583499)
                ·
                  refine ⟨376528672718530789062875249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251019115145687192708583499 376528672718530789062875249)
                  ·
                    refine ⟨282396504538898091797156437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376528672718530789062875249 282396504538898091797156437)
                    ·
                      refine ⟨3309334037565212013247927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 282396504538898091797156437 3309334037565212013247927)
                      ·
                        rfl

theorem cell23_6444905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_6444905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444905 prefixEnd_6444905 := by exact prefixLift 6444905
  have htrace : WordTrace (prefixWord ++ tailWord_6444905) baseStart_6444905 baseEnd_6444905 := by
    simpa [prefixWord, tailWord_6444905, baseEnd_6444905] using wordTrace_append hprefix tailTrace_6444905
  have hstable : (prefixWord ++ tailWord_6444905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444905).length < 2 ^ (prefixWord ++ tailWord_6444905).sum := by decide
  have hdescent : baseEnd_6444905 < baseStart_6444905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444906 : List Nat := [3, 1, 3, 4, 2, 1, 9]
def baseStart_6444906 : Nat := 118140960795 + 6444906 * 2 ^ 59
def prefixEnd_6444906 : Nat := 4983230072969 + 3 ^ 40 * 6444906 * 2
def baseEnd_6444906 : Nat := 40855982111677364312783

theorem tailTrace_6444906 : CollatzResearch.WordTrace tailWord_6444906 prefixEnd_6444906 40855982111677364312783 := by
  unfold tailWord_6444906
  simp only [CollatzResearch.WordTrace]
  refine ⟨58766258297303434789630643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156710022126142492772348381 58766258297303434789630643)
  ·
    refine ⟨88149387445955152184445965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58766258297303434789630643 88149387445955152184445965)
    ·
      refine ⟨33056020292233182069167237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88149387445955152184445965 33056020292233182069167237)
      ·
        refine ⟨6198003804793721637968857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33056020292233182069167237 6198003804793721637968857)
        ·
          refine ⟨4648502853595291228476643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6198003804793721637968857 4648502853595291228476643)
          ·
            refine ⟨6972754280392936842714965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648502853595291228476643 6972754280392936842714965)
            ·
              refine ⟨40855982111677364312783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6972754280392936842714965 40855982111677364312783)
              ·
                rfl

theorem cell23_6444906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 9].length) (baseStart_6444906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444906 prefixEnd_6444906 := by exact prefixLift 6444906
  have htrace : WordTrace (prefixWord ++ tailWord_6444906) baseStart_6444906 baseEnd_6444906 := by
    simpa [prefixWord, tailWord_6444906, baseEnd_6444906] using wordTrace_append hprefix tailTrace_6444906
  have hstable : (prefixWord ++ tailWord_6444906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444906).length < 2 ^ (prefixWord ++ tailWord_6444906).sum := by decide
  have hdescent : baseEnd_6444906 < baseStart_6444906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444932 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_6444932 : Nat := 118140960795 + 6444932 * 2 ^ 59
def prefixEnd_6444932 : Nat := 4983230072969 + 3 ^ 40 * 6444932 * 2
def baseEnd_6444932 : Nat := 1103115967180961135870101

theorem tailTrace_6444932 : CollatzResearch.WordTrace tailWord_6444932 prefixEnd_6444932 1103115967180961135870101 := by
  unfold tailWord_6444932
  simp only [CollatzResearch.WordTrace]
  refine ⟨117532990743559772799484525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156710654324746363732646033 117532990743559772799484525)
  ·
    refine ⟨44074871528834914799806697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117532990743559772799484525 44074871528834914799806697)
    ·
      refine ⟨33056153646626186099855023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44074871528834914799806697 33056153646626186099855023)
      ·
        refine ⟨49584230469939279149782535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33056153646626186099855023 49584230469939279149782535)
        ·
          refine ⟨74376345704908918724673803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49584230469939279149782535 74376345704908918724673803)
          ·
            refine ⟨111564518557363378087010705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74376345704908918724673803 111564518557363378087010705)
            ·
              refine ⟨83673388918022533565258029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111564518557363378087010705 83673388918022533565258029)
              ·
                refine ⟨31377520844258450086971761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83673388918022533565258029 31377520844258450086971761)
                ·
                  refine ⟨23533140633193837565228821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31377520844258450086971761 23533140633193837565228821)
                  ·
                    refine ⟨1103115967180961135870101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23533140633193837565228821 1103115967180961135870101)
                    ·
                      rfl

theorem cell23_6444932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_6444932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444932 prefixEnd_6444932 := by exact prefixLift 6444932
  have htrace : WordTrace (prefixWord ++ tailWord_6444932) baseStart_6444932 baseEnd_6444932 := by
    simpa [prefixWord, tailWord_6444932, baseEnd_6444932] using wordTrace_append hprefix tailTrace_6444932
  have hstable : (prefixWord ++ tailWord_6444932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444932).length < 2 ^ (prefixWord ++ tailWord_6444932).sum := by decide
  have hdescent : baseEnd_6444932 < baseStart_6444932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444939 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 1, 4, 2]
def baseStart_6444939 : Nat := 118140960795 + 6444939 * 2 ^ 59
def prefixEnd_6444939 : Nat := 4983230072969 + 3 ^ 40 * 6444939 * 2
def baseEnd_6444939 : Nat := 3309351495907464880222771

theorem tailTrace_6444939 : CollatzResearch.WordTrace tailWord_6444939 prefixEnd_6444939 3309351495907464880222771 := by
  unfold tailWord_6444939
  simp only [CollatzResearch.WordTrace]
  refine ⟨235066236798094185794473871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156710824532062790529649247 235066236798094185794473871)
  ·
    refine ⟨352599355197141278691710807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235066236798094185794473871 352599355197141278691710807)
    ·
      refine ⟨528899032795711918037566211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352599355197141278691710807 528899032795711918037566211)
      ·
        refine ⟨793348549193567877056349317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528899032795711918037566211 793348549193567877056349317)
        ·
          refine ⟨148752852973793976948065497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 793348549193567877056349317 148752852973793976948065497)
          ·
            refine ⟨111564639730345482711049123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148752852973793976948065497 111564639730345482711049123)
            ·
              refine ⟨167346959595518224066573685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111564639730345482711049123 167346959595518224066573685)
              ·
                refine ⟨15688777462079833506241283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167346959595518224066573685 15688777462079833506241283)
                ·
                  refine ⟨23533166193119750259361925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15688777462079833506241283 23533166193119750259361925)
                  ·
                    refine ⟨4412468661209953173630361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23533166193119750259361925 4412468661209953173630361)
                    ·
                      refine ⟨3309351495907464880222771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412468661209953173630361 3309351495907464880222771)
                      ·
                        rfl

theorem cell23_6444939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4, 2].length) (baseStart_6444939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444939 prefixEnd_6444939 := by exact prefixLift 6444939
  have htrace : WordTrace (prefixWord ++ tailWord_6444939) baseStart_6444939 baseEnd_6444939 := by
    simpa [prefixWord, tailWord_6444939, baseEnd_6444939] using wordTrace_append hprefix tailTrace_6444939
  have hstable : (prefixWord ++ tailWord_6444939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444939).length < 2 ^ (prefixWord ++ tailWord_6444939).sum := by decide
  have hdescent : baseEnd_6444939 < baseStart_6444939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444950 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6444950 : Nat := 118140960795 + 6444950 * 2 ^ 59
def prefixEnd_6444950 : Nat := 4983230072969 + 3 ^ 40 * 6444950 * 2
def baseEnd_6444950 : Nat := 3309357144194664337185221

theorem tailTrace_6444950 : CollatzResearch.WordTrace tailWord_6444950 prefixEnd_6444950 3309357144194664337185221 := by
  unfold tailWord_6444950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691664875065895917070269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156711092000702889782082869 14691664875065895917070269)
  ·
    refine ⟨5509374328149710968901351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14691664875065895917070269 5509374328149710968901351)
    ·
      refine ⟨8264061492224566453352027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509374328149710968901351 8264061492224566453352027)
      ·
        refine ⟨12396092238336849680028041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8264061492224566453352027 12396092238336849680028041)
        ·
          refine ⟨9297069178752637260021031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12396092238336849680028041 9297069178752637260021031)
          ·
            refine ⟨13945603768128955890031547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297069178752637260021031 13945603768128955890031547)
            ·
              refine ⟨20918405652193433835047321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945603768128955890031547 20918405652193433835047321)
              ·
                refine ⟨15688804239145075376285491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20918405652193433835047321 15688804239145075376285491)
                ·
                  refine ⟨23533206358717613064428237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15688804239145075376285491 23533206358717613064428237)
                  ·
                    refine ⟨8824952384519104899160589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23533206358717613064428237 8824952384519104899160589)
                    ·
                      refine ⟨3309357144194664337185221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8824952384519104899160589 3309357144194664337185221)
                      ·
                        rfl

theorem cell23_6444950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6444950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444950 prefixEnd_6444950 := by exact prefixLift 6444950
  have htrace : WordTrace (prefixWord ++ tailWord_6444950) baseStart_6444950 baseEnd_6444950 := by
    simpa [prefixWord, tailWord_6444950, baseEnd_6444950] using wordTrace_append hprefix tailTrace_6444950
  have hstable : (prefixWord ++ tailWord_6444950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444950).length < 2 ^ (prefixWord ++ tailWord_6444950).sum := by decide
  have hdescent : baseEnd_6444950 < baseStart_6444950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444956 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6444956 : Nat := 118140960795 + 6444956 * 2 ^ 59
def prefixEnd_6444956 : Nat := 4983230072969 + 3 ^ 40 * 6444956 * 2
def baseEnd_6444956 : Nat := 3309360225078591313710193

theorem tailTrace_6444956 : CollatzResearch.WordTrace tailWord_6444956 prefixEnd_6444956 3309360225078591313710193 := by
  unfold tailWord_6444956
  simp only [CollatzResearch.WordTrace]
  refine ⟨117533428419516298848921361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156711237892688398465228481 117533428419516298848921361)
  ·
    refine ⟨88150071314637224136691021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117533428419516298848921361 88150071314637224136691021)
    ·
      refine ⟨33056276742988959051259133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88150071314637224136691021 33056276742988959051259133)
      ·
        refine ⟨12396103778620859644222175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33056276742988959051259133 12396103778620859644222175)
        ·
          refine ⟨18594155667931289466333263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12396103778620859644222175 18594155667931289466333263)
          ·
            refine ⟨27891233501896934199499895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18594155667931289466333263 27891233501896934199499895)
            ·
              refine ⟨41836850252845401299249843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27891233501896934199499895 41836850252845401299249843)
              ·
                refine ⟨62755275379268101948874765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41836850252845401299249843 62755275379268101948874765)
                ·
                  refine ⟨23533228267225538230828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62755275379268101948874765 23533228267225538230828037)
                  ·
                    refine ⟨4412480300104788418280257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23533228267225538230828037 4412480300104788418280257)
                    ·
                      refine ⟨3309360225078591313710193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412480300104788418280257 3309360225078591313710193)
                      ·
                        rfl

theorem cell23_6444956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6444956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444956 prefixEnd_6444956 := by exact prefixLift 6444956
  have htrace : WordTrace (prefixWord ++ tailWord_6444956) baseStart_6444956 baseEnd_6444956 := by
    simpa [prefixWord, tailWord_6444956, baseEnd_6444956] using wordTrace_append hprefix tailTrace_6444956
  have hstable : (prefixWord ++ tailWord_6444956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444956).length < 2 ^ (prefixWord ++ tailWord_6444956).sum := by decide
  have hdescent : baseEnd_6444956 < baseStart_6444956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444979 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 5]
def baseStart_6444979 : Nat := 118140960795 + 6444979 * 2 ^ 59
def prefixEnd_6444979 : Nat := 4983230072969 + 3 ^ 40 * 6444979 * 2
def baseEnd_6444979 : Nat := 367708003903738302635843

theorem tailTrace_6444979 : CollatzResearch.WordTrace tailWord_6444979 prefixEnd_6444979 367708003903738302635843 := by
  unfold tailWord_6444979
  simp only [CollatzResearch.WordTrace]
  refine ⟨235067695717949272625929991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156711797145299515083953327 235067695717949272625929991)
  ·
    refine ⟨352601543576923908938894987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235067695717949272625929991 352601543576923908938894987)
    ·
      refine ⟨528902315365385863408342481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352601543576923908938894987 528902315365385863408342481)
      ·
        refine ⟨396676736524039397556256861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528902315365385863408342481 396676736524039397556256861)
        ·
          refine ⟨148753776196514774083596323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396676736524039397556256861 148753776196514774083596323)
          ·
            refine ⟨223130664294772161125394485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148753776196514774083596323 223130664294772161125394485)
            ·
              refine ⟨20918499777634890105505733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223130664294772161125394485 20918499777634890105505733)
              ·
                refine ⟨3922218708306541894782325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20918499777634890105505733 3922218708306541894782325)
                ·
                  refine ⟨367708003903738302635843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922218708306541894782325 367708003903738302635843)
                  ·
                    rfl

theorem cell23_6444979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 5].length) (baseStart_6444979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444979 prefixEnd_6444979 := by exact prefixLift 6444979
  have htrace : WordTrace (prefixWord ++ tailWord_6444979) baseStart_6444979 baseEnd_6444979 := by
    simpa [prefixWord, tailWord_6444979, baseEnd_6444979] using wordTrace_append hprefix tailTrace_6444979
  have hstable : (prefixWord ++ tailWord_6444979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444979).length < 2 ^ (prefixWord ++ tailWord_6444979).sum := by decide
  have hdescent : baseEnd_6444979 < baseStart_6444979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444989 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_6444989 : Nat := 118140960795 + 6444989 * 2 ^ 59
def prefixEnd_6444989 : Nat := 4983230072969 + 3 ^ 40 * 6444989 * 2
def baseEnd_6444989 : Nat := 3309377169940189684597541

theorem tailTrace_6444989 : CollatzResearch.WordTrace tailWord_6444989 prefixEnd_6444989 3309377169940189684597541 := by
  unfold tailWord_6444989
  simp only [CollatzResearch.WordTrace]
  refine ⟨235068060447913044333794021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156712040298608696222529347 235068060447913044333794021)
  ·
    refine ⟨44075261333983695812586379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235068060447913044333794021 44075261333983695812586379)
    ·
      refine ⟨66112892000975543718879569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44075261333983695812586379 66112892000975543718879569)
      ·
        refine ⟨49584669000731657789159677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66112892000975543718879569 49584669000731657789159677)
        ·
          refine ⟨18594250875274371670934879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49584669000731657789159677 18594250875274371670934879)
          ·
            refine ⟨27891376312911557506402319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18594250875274371670934879 27891376312911557506402319)
            ·
              refine ⟨41837064469367336259603479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27891376312911557506402319 41837064469367336259603479)
              ·
                refine ⟨62755596704051004389405219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41837064469367336259603479 62755596704051004389405219)
                ·
                  refine ⟨94133395056076506584107829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62755596704051004389405219 94133395056076506584107829)
                  ·
                    refine ⟨8825005786507172492260109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94133395056076506584107829 8825005786507172492260109)
                    ·
                      refine ⟨3309377169940189684597541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825005786507172492260109 3309377169940189684597541)
                      ·
                        rfl

theorem cell23_6444989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_6444989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444989 prefixEnd_6444989 := by exact prefixLift 6444989
  have htrace : WordTrace (prefixWord ++ tailWord_6444989) baseStart_6444989 baseEnd_6444989 := by
    simpa [prefixWord, tailWord_6444989, baseEnd_6444989] using wordTrace_append hprefix tailTrace_6444989
  have hstable : (prefixWord ++ tailWord_6444989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444989).length < 2 ^ (prefixWord ++ tailWord_6444989).sum := by decide
  have hdescent : baseEnd_6444989 < baseStart_6444989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444992 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_6444992 : Nat := 118140960795 + 6444992 * 2 ^ 59
def prefixEnd_6444992 : Nat := 4983230072969 + 3 ^ 40 * 6444992 * 2
def baseEnd_6444992 : Nat := 1103126236794051057620009

theorem tailTrace_6444992 : CollatzResearch.WordTrace tailWord_6444992 prefixEnd_6444992 1103126236794051057620009 := by
  unfold tailWord_6444992
  simp only [CollatzResearch.WordTrace]
  refine ⟨117534084933451087923076615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156712113244601450564102153 117534084933451087923076615)
  ·
    refine ⟨176301127400176631884614923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117534084933451087923076615 176301127400176631884614923)
    ·
      refine ⟨264451691100264947826922385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176301127400176631884614923 264451691100264947826922385)
      ·
        refine ⟨198338768325198710870191789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264451691100264947826922385 198338768325198710870191789)
        ·
          refine ⟨74377038121949516576321921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198338768325198710870191789 74377038121949516576321921)
          ·
            refine ⟨55782778591462137432241441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74377038121949516576321921 55782778591462137432241441)
            ·
              refine ⟨41837083943596603074181081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55782778591462137432241441 41837083943596603074181081)
              ·
                refine ⟨31377812957697452305635811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41837083943596603074181081 31377812957697452305635811)
                ·
                  refine ⟨47066719436546178458453717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31377812957697452305635811 47066719436546178458453717)
                  ·
                    refine ⟨1103126236794051057620009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47066719436546178458453717 1103126236794051057620009)
                    ·
                      rfl

theorem cell23_6444992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_6444992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444992 prefixEnd_6444992 := by exact prefixLift 6444992
  have htrace : WordTrace (prefixWord ++ tailWord_6444992) baseStart_6444992 baseEnd_6444992 := by
    simpa [prefixWord, tailWord_6444992, baseEnd_6444992] using wordTrace_append hprefix tailTrace_6444992
  have hstable : (prefixWord ++ tailWord_6444992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444992).length < 2 ^ (prefixWord ++ tailWord_6444992).sum := by decide
  have hdescent : baseEnd_6444992 < baseStart_6444992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6444999 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_6444999 : Nat := 118140960795 + 6444999 * 2 ^ 59
def prefixEnd_6444999 : Nat := 4983230072969 + 3 ^ 40 * 6444999 * 2
def baseEnd_6444999 : Nat := 3309382304746734645472495

theorem tailTrace_6444999 : CollatzResearch.WordTrace tailWord_6444999 prefixEnd_6444999 3309382304746734645472495 := by
  unfold tailWord_6444999
  simp only [CollatzResearch.WordTrace]
  refine ⟨235068425177876816041658051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156712283451917877361105367 235068425177876816041658051)
  ·
    refine ⟨352602637766815224062487077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235068425177876816041658051 352602637766815224062487077)
    ·
      refine ⟨66112994581277854511716327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352602637766815224062487077 66112994581277854511716327)
      ·
        refine ⟨99169491871916781767574491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66112994581277854511716327 99169491871916781767574491)
        ·
          refine ⟨148754237807875172651361737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99169491871916781767574491 148754237807875172651361737)
          ·
            refine ⟨111565678355906379488521303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148754237807875172651361737 111565678355906379488521303)
            ·
              refine ⟨167348517533859569232781955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111565678355906379488521303 167348517533859569232781955)
              ·
                refine ⟨251022776300789353849172933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167348517533859569232781955 251022776300789353849172933)
                ·
                  refine ⟨47066770556398003846719925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251022776300789353849172933 47066770556398003846719925)
                  ·
                    refine ⟨4412509739662312860629993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47066770556398003846719925 4412509739662312860629993)
                    ·
                      refine ⟨3309382304746734645472495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412509739662312860629993 3309382304746734645472495)
                      ·
                        rfl

theorem cell23_6444999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_6444999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6444999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6444999 prefixEnd_6444999 := by exact prefixLift 6444999
  have htrace : WordTrace (prefixWord ++ tailWord_6444999) baseStart_6444999 baseEnd_6444999 := by
    simpa [prefixWord, tailWord_6444999, baseEnd_6444999] using wordTrace_append hprefix tailTrace_6444999
  have hstable : (prefixWord ++ tailWord_6444999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6444999).length < 2 ^ (prefixWord ++ tailWord_6444999).sum := by decide
  have hdescent : baseEnd_6444999 < baseStart_6444999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6444999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445002 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_6445002 : Nat := 118140960795 + 6445002 * 2 ^ 59
def prefixEnd_6445002 : Nat := 4983230072969 + 3 ^ 40 * 6445002 * 2
def baseEnd_6445002 : Nat := 3309383845188698133734981

theorem tailTrace_6445002 : CollatzResearch.WordTrace tailWord_6445002 prefixEnd_6445002 3309383845188698133734981 := by
  unfold tailWord_6445002
  simp only [CollatzResearch.WordTrace]
  refine ⟨58767133649216486888504315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156712356397910631702678173 58767133649216486888504315)
  ·
    refine ⟨88150700473824730332756473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58767133649216486888504315 88150700473824730332756473)
    ·
      refine ⟨66113025355368547749567355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88150700473824730332756473 66113025355368547749567355)
      ·
        refine ⟨99169538033052821624351033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66113025355368547749567355 99169538033052821624351033)
        ·
          refine ⟨74377153524789616218263275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99169538033052821624351033 74377153524789616218263275)
          ·
            refine ⟨111565730287184424327394913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74377153524789616218263275 111565730287184424327394913)
            ·
              refine ⟨83674297715388318245546185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111565730287184424327394913 83674297715388318245546185)
              ·
                refine ⟨62755723286541238684159639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83674297715388318245546185 62755723286541238684159639)
                ·
                  refine ⟨94133584929811858026239459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62755723286541238684159639 94133584929811858026239459)
                  ·
                    refine ⟨141200377394717787039359189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94133584929811858026239459 141200377394717787039359189)
                    ·
                      refine ⟨3309383845188698133734981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141200377394717787039359189 3309383845188698133734981)
                      ·
                        rfl

theorem cell23_6445002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_6445002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445002 prefixEnd_6445002 := by exact prefixLift 6445002
  have htrace : WordTrace (prefixWord ++ tailWord_6445002) baseStart_6445002 baseEnd_6445002 := by
    simpa [prefixWord, tailWord_6445002, baseEnd_6445002] using wordTrace_append hprefix tailTrace_6445002
  have hstable : (prefixWord ++ tailWord_6445002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445002).length < 2 ^ (prefixWord ++ tailWord_6445002).sum := by decide
  have hdescent : baseEnd_6445002 < baseStart_6445002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445049 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_6445049 : Nat := 118140960795 + 6445049 * 2 ^ 59
def prefixEnd_6445049 : Nat := 4983230072969 + 3 ^ 40 * 6445049 * 2
def baseEnd_6445049 : Nat := 3309407978779459449847265

theorem tailTrace_6445049 : CollatzResearch.WordTrace tailWord_6445049 prefixEnd_6445049 3309407978779459449847265 := by
  unfold tailWord_6445049
  simp only [CollatzResearch.WordTrace]
  refine ⟨235070248827695674580978201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156713499218463783053985467 235070248827695674580978201)
  ·
    refine ⟨176302686620771755935733651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235070248827695674580978201 176302686620771755935733651)
    ·
      refine ⟨264454029931157633903600477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176302686620771755935733651 264454029931157633903600477)
      ·
        refine ⟨99170261224184112713850179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264454029931157633903600477 99170261224184112713850179)
        ·
          refine ⟨148755391836276169070775269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99170261224184112713850179 148755391836276169070775269)
          ·
            refine ⟨27891635969301781700770363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148755391836276169070775269 27891635969301781700770363)
            ·
              refine ⟨41837453953952672551155545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27891635969301781700770363 41837453953952672551155545)
              ·
                refine ⟨31378090465464504413366659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41837453953952672551155545 31378090465464504413366659)
                ·
                  refine ⟨47067135698196756620049989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31378090465464504413366659 47067135698196756620049989)
                  ·
                    refine ⟨8825087943411891866259373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47067135698196756620049989 8825087943411891866259373)
                    ·
                      refine ⟨3309407978779459449847265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825087943411891866259373 3309407978779459449847265)
                      ·
                        rfl

theorem cell23_6445049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_6445049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445049 prefixEnd_6445049 := by exact prefixLift 6445049
  have htrace : WordTrace (prefixWord ++ tailWord_6445049) baseStart_6445049 baseEnd_6445049 := by
    simpa [prefixWord, tailWord_6445049, baseEnd_6445049] using wordTrace_append hprefix tailTrace_6445049
  have hstable : (prefixWord ++ tailWord_6445049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445049).length < 2 ^ (prefixWord ++ tailWord_6445049).sum := by decide
  have hdescent : baseEnd_6445049 < baseStart_6445049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445072 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_6445072 : Nat := 118140960795 + 6445072 * 2 ^ 59
def prefixEnd_6445072 : Nat := 4983230072969 + 3 ^ 40 * 6445072 * 2
def baseEnd_6445072 : Nat := 3309419788834512859859659

theorem tailTrace_6445072 : CollatzResearch.WordTrace tailWord_6445072 prefixEnd_6445072 3309419788834512859859659 := by
  unfold tailWord_6445072
  simp only [CollatzResearch.WordTrace]
  refine ⟨117535543853306174754532735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156714058471074899672710313 117535543853306174754532735)
  ·
    refine ⟨176303315779959262131799103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117535543853306174754532735 176303315779959262131799103)
    ·
      refine ⟨264454973669938893197698655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176303315779959262131799103 264454973669938893197698655)
      ·
        refine ⟨396682460504908339796547983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264454973669938893197698655 396682460504908339796547983)
        ·
          refine ⟨595023690757362509694821975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396682460504908339796547983 595023690757362509694821975)
          ·
            refine ⟨892535536136043764542232963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595023690757362509694821975 892535536136043764542232963)
            ·
              refine ⟨1338803304204065646813349445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892535536136043764542232963 1338803304204065646813349445)
              ·
                refine ⟨251025619538262308777503021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1338803304204065646813349445 251025619538262308777503021)
                ·
                  refine ⟨94134607326848365791563633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251025619538262308777503021 94134607326848365791563633)
                  ·
                    refine ⟨70600955495136274343672725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94134607326848365791563633 70600955495136274343672725)
                    ·
                      refine ⟨3309419788834512859859659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70600955495136274343672725 3309419788834512859859659)
                      ·
                        rfl

theorem cell23_6445072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_6445072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445072 prefixEnd_6445072 := by exact prefixLift 6445072
  have htrace : WordTrace (prefixWord ++ tailWord_6445072) baseStart_6445072 baseEnd_6445072 := by
    simpa [prefixWord, tailWord_6445072, baseEnd_6445072] using wordTrace_append hprefix tailTrace_6445072
  have hstable : (prefixWord ++ tailWord_6445072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445072).length < 2 ^ (prefixWord ++ tailWord_6445072).sum := by decide
  have hdescent : baseEnd_6445072 < baseStart_6445072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445090 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_6445090 : Nat := 118140960795 + 6445090 * 2 ^ 59
def prefixEnd_6445090 : Nat := 4983230072969 + 3 ^ 40 * 6445090 * 2
def baseEnd_6445090 : Nat := 1103143010495431263144859

theorem tailTrace_6445090 : CollatzResearch.WordTrace tailWord_6445090 prefixEnd_6445090 1103143010495431263144859 := by
  unfold tailWord_6445090
  simp only [CollatzResearch.WordTrace]
  refine ⟨58767936055136784645805181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156714496147031425722147149 58767936055136784645805181)
  ·
    refine ⟨22037976020676294242176943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58767936055136784645805181 22037976020676294242176943)
    ·
      refine ⟨33056964031014441363265415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22037976020676294242176943 33056964031014441363265415)
      ·
        refine ⟨49585446046521662044898123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33056964031014441363265415 49585446046521662044898123)
        ·
          refine ⟨74378169069782493067347185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49585446046521662044898123 74378169069782493067347185)
          ·
            refine ⟨55783626802336869800510389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74378169069782493067347185 55783626802336869800510389)
            ·
              refine ⟨5229715012719081543797849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55783626802336869800510389 5229715012719081543797849)
              ·
                refine ⟨3922286259539311157848387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229715012719081543797849 3922286259539311157848387)
                ·
                  refine ⟨5883429389308966736772581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922286259539311157848387 5883429389308966736772581)
                  ·
                    refine ⟨1103143010495431263144859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5883429389308966736772581 1103143010495431263144859)
                    ·
                      rfl

theorem cell23_6445090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_6445090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445090 prefixEnd_6445090 := by exact prefixLift 6445090
  have htrace : WordTrace (prefixWord ++ tailWord_6445090) baseStart_6445090 baseEnd_6445090 := by
    simpa [prefixWord, tailWord_6445090, baseEnd_6445090] using wordTrace_append hprefix tailTrace_6445090
  have hstable : (prefixWord ++ tailWord_6445090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445090).length < 2 ^ (prefixWord ++ tailWord_6445090).sum := by decide
  have hdescent : baseEnd_6445090 < baseStart_6445090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445129 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_6445129 : Nat := 118140960795 + 6445129 * 2 ^ 59
def prefixEnd_6445129 : Nat := 4983230072969 + 3 ^ 40 * 6445129 * 2
def baseEnd_6445129 : Nat := 1103149685743939712282299

theorem tailTrace_6445129 : CollatzResearch.WordTrace tailWord_6445129 prefixEnd_6445129 1103149685743939712282299 := by
  unfold tailWord_6445129
  simp only [CollatzResearch.WordTrace]
  refine ⟨235073166667405848243890441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156715444444937232162593627 235073166667405848243890441)
  ·
    refine ⟨176304875000554386182917831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235073166667405848243890441 176304875000554386182917831)
    ·
      refine ⟨264457312500831579274376747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176304875000554386182917831 264457312500831579274376747)
      ·
        refine ⟨396685968751247368911565121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264457312500831579274376747 396685968751247368911565121)
        ·
          refine ⟨297514476563435526683673841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396685968751247368911565121 297514476563435526683673841)
          ·
            refine ⟨223135857422576645012755381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297514476563435526683673841 223135857422576645012755381)
            ·
              refine ⟨20918986633366560469945817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223135857422576645012755381 20918986633366560469945817)
              ·
                refine ⟨15689239975024920352459363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20918986633366560469945817 15689239975024920352459363)
                ·
                  refine ⟨23533859962537380528689045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15689239975024920352459363 23533859962537380528689045)
                  ·
                    refine ⟨1103149685743939712282299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23533859962537380528689045 1103149685743939712282299)
                    ·
                      rfl

theorem cell23_6445129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_6445129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445129 prefixEnd_6445129 := by exact prefixLift 6445129
  have htrace : WordTrace (prefixWord ++ tailWord_6445129) baseStart_6445129 baseEnd_6445129 := by
    simpa [prefixWord, tailWord_6445129, baseEnd_6445129] using wordTrace_append hprefix tailTrace_6445129
  have hstable : (prefixWord ++ tailWord_6445129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445129).length < 2 ^ (prefixWord ++ tailWord_6445129).sum := by decide
  have hdescent : baseEnd_6445129 < baseStart_6445129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445153 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_6445153 : Nat := 118140960795 + 6445153 * 2 ^ 59
def prefixEnd_6445153 : Nat := 4983230072969 + 3 ^ 40 * 6445153 * 2
def baseEnd_6445153 : Nat := 3309461380767527042946787

theorem tailTrace_6445153 : CollatzResearch.WordTrace tailWord_6445153 prefixEnd_6445153 3309461380767527042946787 := by
  unfold tailWord_6445153
  simp only [CollatzResearch.WordTrace]
  refine ⟨235074042019318900342764113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156716028012879266895176075 235074042019318900342764113)
  ·
    refine ⟨176305531514489175257073085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235074042019318900342764113 176305531514489175257073085)
    ·
      refine ⟨66114574317933440721402407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176305531514489175257073085 66114574317933440721402407)
      ·
        refine ⟨99171861476900161082103611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66114574317933440721402407 99171861476900161082103611)
        ·
          refine ⟨148757792215350241623155417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99171861476900161082103611 148757792215350241623155417)
          ·
            refine ⟨111568344161512681217366563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148757792215350241623155417 111568344161512681217366563)
            ·
              refine ⟨167352516242269021826049845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111568344161512681217366563 167352516242269021826049845)
              ·
                refine ⟨15689298397712720796192173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167352516242269021826049845 15689298397712720796192173)
                ·
                  refine ⟨5883486899142270298572065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15689298397712720796192173 5883486899142270298572065)
                  ·
                    refine ⟨4412615174356702723929049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883486899142270298572065 4412615174356702723929049)
                    ·
                      refine ⟨3309461380767527042946787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412615174356702723929049 3309461380767527042946787)
                      ·
                        rfl

theorem cell23_6445153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_6445153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445153 prefixEnd_6445153 := by exact prefixLift 6445153
  have htrace : WordTrace (prefixWord ++ tailWord_6445153) baseStart_6445153 baseEnd_6445153 := by
    simpa [prefixWord, tailWord_6445153, baseEnd_6445153] using wordTrace_append hprefix tailTrace_6445153
  have hstable : (prefixWord ++ tailWord_6445153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445153).length < 2 ^ (prefixWord ++ tailWord_6445153).sum := by decide
  have hdescent : baseEnd_6445153 < baseStart_6445153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445156 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_6445156 : Nat := 118140960795 + 6445156 * 2 ^ 59
def prefixEnd_6445156 : Nat := 4983230072969 + 3 ^ 40 * 6445156 * 2
def baseEnd_6445156 : Nat := 3309462921209490531209273

theorem tailTrace_6445156 : CollatzResearch.WordTrace tailWord_6445156 prefixEnd_6445156 3309462921209490531209273 := by
  unfold tailWord_6445156
  simp only [CollatzResearch.WordTrace]
  refine ⟨117537075719154015927561661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156716100958872021236748881 117537075719154015927561661)
  ·
    refine ⟨44076403394682755972835623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117537075719154015927561661 44076403394682755972835623)
    ·
      refine ⟨66114605092024133959253435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44076403394682755972835623 66114605092024133959253435)
      ·
        refine ⟨99171907638036200938880153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66114605092024133959253435 99171907638036200938880153)
        ·
          refine ⟨74378930728527150704160115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99171907638036200938880153 74378930728527150704160115)
          ·
            refine ⟨111568396092790726056240173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74378930728527150704160115 111568396092790726056240173)
            ·
              refine ⟨41838148534796522271090065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111568396092790726056240173 41838148534796522271090065)
              ·
                refine ⟨31378611401097391703317549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41838148534796522271090065 31378611401097391703317549)
                ·
                  refine ⟨11766979275411521888744081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31378611401097391703317549 11766979275411521888744081)
                  ·
                    refine ⟨8825234456558641416558061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11766979275411521888744081 8825234456558641416558061)
                    ·
                      refine ⟨3309462921209490531209273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825234456558641416558061 3309462921209490531209273)
                      ·
                        rfl

theorem cell23_6445156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_6445156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445156 prefixEnd_6445156 := by exact prefixLift 6445156
  have htrace : WordTrace (prefixWord ++ tailWord_6445156) baseStart_6445156 baseEnd_6445156 := by
    simpa [prefixWord, tailWord_6445156, baseEnd_6445156] using wordTrace_append hprefix tailTrace_6445156
  have hstable : (prefixWord ++ tailWord_6445156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445156).length < 2 ^ (prefixWord ++ tailWord_6445156).sum := by decide
  have hdescent : baseEnd_6445156 < baseStart_6445156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445170 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_6445170 : Nat := 118140960795 + 6445170 * 2 ^ 59
def prefixEnd_6445170 : Nat := 4983230072969 + 3 ^ 40 * 6445170 * 2
def baseEnd_6445170 : Nat := 3309470109938653476434209

theorem tailTrace_6445170 : CollatzResearch.WordTrace tailWord_6445170 prefixEnd_6445170 3309470109938653476434209 := by
  unfold tailWord_6445170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58768665515064328061533241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156716441373504874830755309 58768665515064328061533241)
  ·
    refine ⟨44076499136298246046149931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58768665515064328061533241 44076499136298246046149931)
    ·
      refine ⟨66114748704447369069224897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44076499136298246046149931 66114748704447369069224897)
      ·
        refine ⟨49586061528335526801918673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66114748704447369069224897 49586061528335526801918673)
        ·
          refine ⟨37189546146251645101439005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49586061528335526801918673 37189546146251645101439005)
          ·
            refine ⟨13946079804844366913039627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37189546146251645101439005 13946079804844366913039627)
            ·
              refine ⟨20919119707266550369559441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13946079804844366913039627 20919119707266550369559441)
              ·
                refine ⟨15689339780449912777169581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20919119707266550369559441 15689339780449912777169581)
                ·
                  refine ⟨5883502417668717291438593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15689339780449912777169581 5883502417668717291438593)
                  ·
                    refine ⟨4412626813251537968578945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883502417668717291438593 4412626813251537968578945)
                    ·
                      refine ⟨3309470109938653476434209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412626813251537968578945 3309470109938653476434209)
                      ·
                        rfl

theorem cell23_6445170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_6445170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445170 prefixEnd_6445170 := by exact prefixLift 6445170
  have htrace : WordTrace (prefixWord ++ tailWord_6445170) baseStart_6445170 baseEnd_6445170 := by
    simpa [prefixWord, tailWord_6445170, baseEnd_6445170] using wordTrace_append hprefix tailTrace_6445170
  have hstable : (prefixWord ++ tailWord_6445170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445170).length < 2 ^ (prefixWord ++ tailWord_6445170).sum := by decide
  have hdescent : baseEnd_6445170 < baseStart_6445170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445187 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 1, 2, 2]
def baseStart_6445187 : Nat := 118140960795 + 6445187 * 2 ^ 59
def prefixEnd_6445187 : Nat := 4983230072969 + 3 ^ 40 * 6445187 * 2
def baseEnd_6445187 : Nat := 3309478839109779909921631

theorem tailTrace_6445187 : CollatzResearch.WordTrace tailWord_6445187 prefixEnd_6445187 3309478839109779909921631 := by
  unfold tailWord_6445187
  simp only [CollatzResearch.WordTrace]
  refine ⟨235075282101195724149501815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156716854734130482766334543 235075282101195724149501815)
  ·
    refine ⟨352612923151793586224252723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235075282101195724149501815 352612923151793586224252723)
    ·
      refine ⟨528919384727690379336379085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352612923151793586224252723 528919384727690379336379085)
      ·
        refine ⟨198344769272883892251142157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 528919384727690379336379085 198344769272883892251142157)
        ·
          refine ⟨74379288477331459594178309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198344769272883892251142157 74379288477331459594178309)
          ·
            refine ⟨13946116589499648673908433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74379288477331459594178309 13946116589499648673908433)
            ·
              refine ⟨10459587442124736505431325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13946116589499648673908433 10459587442124736505431325)
              ·
                refine ⟨3922345290796776189536747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10459587442124736505431325 3922345290796776189536747)
                ·
                  refine ⟨5883517936195164284305121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922345290796776189536747 5883517936195164284305121)
                  ·
                    refine ⟨4412638452146373213228841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883517936195164284305121 4412638452146373213228841)
                    ·
                      refine ⟨3309478839109779909921631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412638452146373213228841 3309478839109779909921631)
                      ·
                        rfl

theorem cell23_6445187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_6445187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445187 prefixEnd_6445187 := by exact prefixLift 6445187
  have htrace : WordTrace (prefixWord ++ tailWord_6445187) baseStart_6445187 baseEnd_6445187 := by
    simpa [prefixWord, tailWord_6445187, baseEnd_6445187] using wordTrace_append hprefix tailTrace_6445187
  have hstable : (prefixWord ++ tailWord_6445187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445187).length < 2 ^ (prefixWord ++ tailWord_6445187).sum := by decide
  have hdescent : baseEnd_6445187 < baseStart_6445187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445204 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6445204 : Nat := 118140960795 + 6445204 * 2 ^ 59
def prefixEnd_6445204 : Nat := 4983230072969 + 3 ^ 40 * 6445204 * 2
def baseEnd_6445204 : Nat := 3309487568280906343409053

theorem tailTrace_6445204 : CollatzResearch.WordTrace tailWord_6445204 prefixEnd_6445204 3309487568280906343409053 := by
  unfold tailWord_6445204
  simp only [CollatzResearch.WordTrace]
  refine ⟨117537951071067068026435333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156717268094756090701913777 117537951071067068026435333)
  ·
    refine ⟨22038365825825075254956625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117537951071067068026435333 22038365825825075254956625)
    ·
      refine ⟨16528774369368806441217469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22038365825825075254956625 16528774369368806441217469)
      ·
        refine ⟨6198290388513302415456551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16528774369368806441217469 6198290388513302415456551)
        ·
          refine ⟨9297435582769953623184827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198290388513302415456551 9297435582769953623184827)
          ·
            refine ⟨13946153374154930434777241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297435582769953623184827 13946153374154930434777241)
            ·
              refine ⟨10459615030616197826082931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13946153374154930434777241 10459615030616197826082931)
              ·
                refine ⟨15689422545924296739124397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459615030616197826082931 15689422545924296739124397)
                ·
                  refine ⟨5883533454721611277171649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15689422545924296739124397 5883533454721611277171649)
                  ·
                    refine ⟨4412650091041208457878737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883533454721611277171649 4412650091041208457878737)
                    ·
                      refine ⟨3309487568280906343409053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412650091041208457878737 3309487568280906343409053)
                      ·
                        rfl

theorem cell23_6445204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6445204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445204 prefixEnd_6445204 := by exact prefixLift 6445204
  have htrace : WordTrace (prefixWord ++ tailWord_6445204) baseStart_6445204 baseEnd_6445204 := by
    simpa [prefixWord, tailWord_6445204, baseEnd_6445204] using wordTrace_append hprefix tailTrace_6445204
  have hstable : (prefixWord ++ tailWord_6445204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445204).length < 2 ^ (prefixWord ++ tailWord_6445204).sum := by decide
  have hdescent : baseEnd_6445204 < baseStart_6445204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445209 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_6445209 : Nat := 118140960795 + 6445209 * 2 ^ 59
def prefixEnd_6445209 : Nat := 4983230072969 + 3 ^ 40 * 6445209 * 2
def baseEnd_6445209 : Nat := 3309490135684178823846529

theorem tailTrace_6445209 : CollatzResearch.WordTrace tailWord_6445209 prefixEnd_6445209 3309490135684178823846529 := by
  unfold tailWord_6445209
  simp only [CollatzResearch.WordTrace]
  refine ⟨235076084507116021906802681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156717389671410681271201787 235076084507116021906802681)
  ·
    refine ⟨176307063380337016430102011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235076084507116021906802681 176307063380337016430102011)
    ·
      refine ⟨264460595070505524645153017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176307063380337016430102011 264460595070505524645153017)
      ·
        refine ⟨198345446302879143483864763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264460595070505524645153017 198345446302879143483864763)
        ·
          refine ⟨297518169454318715225797145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198345446302879143483864763 297518169454318715225797145)
          ·
            refine ⟨223138627090739036419347859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297518169454318715225797145 223138627090739036419347859)
            ·
              refine ⟨334707940636108554629021789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223138627090739036419347859 334707940636108554629021789)
              ·
                refine ⟨125515477738540707985883171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334707940636108554629021789 125515477738540707985883171)
                ·
                  refine ⟨188273216607811061978824757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125515477738540707985883171 188273216607811061978824757)
                  ·
                    refine ⟨17650614056982287060514821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 188273216607811061978824757 17650614056982287060514821)
                    ·
                      refine ⟨3309490135684178823846529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17650614056982287060514821 3309490135684178823846529)
                      ·
                        rfl

theorem cell23_6445209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_6445209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445209 prefixEnd_6445209 := by exact prefixLift 6445209
  have htrace : WordTrace (prefixWord ++ tailWord_6445209) baseStart_6445209 baseEnd_6445209 := by
    simpa [prefixWord, tailWord_6445209, baseEnd_6445209] using wordTrace_append hprefix tailTrace_6445209
  have hstable : (prefixWord ++ tailWord_6445209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445209).length < 2 ^ (prefixWord ++ tailWord_6445209).sum := by decide
  have hdescent : baseEnd_6445209 < baseStart_6445209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445220 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_6445220 : Nat := 118140960795 + 6445220 * 2 ^ 59
def prefixEnd_6445220 : Nat := 4983230072969 + 3 ^ 40 * 6445220 * 2
def baseEnd_6445220 : Nat := 3309495783971378280808979

theorem tailTrace_6445220 : CollatzResearch.WordTrace tailWord_6445220 prefixEnd_6445220 3309495783971378280808979 := by
  unfold tailWord_6445220
  simp only [CollatzResearch.WordTrace]
  refine ⟨117538242855038085392726557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156717657140050780523635409 117538242855038085392726557)
  ·
    refine ⟨44076841070639282022272459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117538242855038085392726557 44076841070639282022272459)
    ·
      refine ⟨66115261605958923033408689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44076841070639282022272459 66115261605958923033408689)
      ·
        refine ⟨49586446204469192275056517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66115261605958923033408689 49586446204469192275056517)
        ·
          refine ⟨9297458663337973551573097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49586446204469192275056517 9297458663337973551573097)
          ·
            refine ⟨6973093997503480163679823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9297458663337973551573097 6973093997503480163679823)
            ·
              refine ⟨10459640996255220245519735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973093997503480163679823 10459640996255220245519735)
              ·
                refine ⟨15689461494382830368279603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459640996255220245519735 15689461494382830368279603)
                ·
                  refine ⟨23534192241574245552419405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15689461494382830368279603 23534192241574245552419405)
                  ·
                    refine ⟨8825322090590342082157277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23534192241574245552419405 8825322090590342082157277)
                    ·
                      refine ⟨3309495783971378280808979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825322090590342082157277 3309495783971378280808979)
                      ·
                        rfl

theorem cell23_6445220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_6445220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445220 prefixEnd_6445220 := by exact prefixLift 6445220
  have htrace : WordTrace (prefixWord ++ tailWord_6445220) baseStart_6445220 baseEnd_6445220 := by
    simpa [prefixWord, tailWord_6445220, baseEnd_6445220] using wordTrace_append hprefix tailTrace_6445220
  have hstable : (prefixWord ++ tailWord_6445220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445220).length < 2 ^ (prefixWord ++ tailWord_6445220).sum := by decide
  have hdescent : baseEnd_6445220 < baseStart_6445220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445243 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 6, 2, 2]
def baseStart_6445243 : Nat := 118140960795 + 6445243 * 2 ^ 59
def prefixEnd_6445243 : Nat := 4983230072969 + 3 ^ 40 * 6445243 * 2
def baseEnd_6445243 : Nat := 3309507594026431690821373

theorem tailTrace_6445243 : CollatzResearch.WordTrace tailWord_6445243 prefixEnd_6445243 3309507594026431690821373 := by
  unfold tailWord_6445243
  simp only [CollatzResearch.WordTrace]
  refine ⟨235077324588992845713540383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156718216392661897142360255 235077324588992845713540383)
  ·
    refine ⟨352615986883489268570310575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235077324588992845713540383 352615986883489268570310575)
    ·
      refine ⟨528923980325233902855465863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352615986883489268570310575 528923980325233902855465863)
      ·
        refine ⟨793385970487850854283198795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528923980325233902855465863 793385970487850854283198795)
        ·
          refine ⟨1190078955731776281424798193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793385970487850854283198795 1190078955731776281424798193)
          ·
            refine ⟨892559216798832211068598645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190078955731776281424798193 892559216798832211068598645)
            ·
              refine ⟨83677426574890519787681123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 892559216798832211068598645 83677426574890519787681123)
              ·
                refine ⟨125516139862335779681521685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83677426574890519787681123 125516139862335779681521685)
                ·
                  refine ⟨5883569056046989672571329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125516139862335779681521685 5883569056046989672571329)
                  ·
                    refine ⟨4412676792035242254428497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883569056046989672571329 4412676792035242254428497)
                    ·
                      refine ⟨3309507594026431690821373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412676792035242254428497 3309507594026431690821373)
                      ·
                        rfl

theorem cell23_6445243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 2, 2].length) (baseStart_6445243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445243 prefixEnd_6445243 := by exact prefixLift 6445243
  have htrace : WordTrace (prefixWord ++ tailWord_6445243) baseStart_6445243 baseEnd_6445243 := by
    simpa [prefixWord, tailWord_6445243, baseEnd_6445243] using wordTrace_append hprefix tailTrace_6445243
  have hstable : (prefixWord ++ tailWord_6445243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445243).length < 2 ^ (prefixWord ++ tailWord_6445243).sum := by decide
  have hdescent : baseEnd_6445243 < baseStart_6445243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445259 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_6445259 : Nat := 118140960795 + 6445259 * 2 ^ 59
def prefixEnd_6445259 : Nat := 4983230072969 + 3 ^ 40 * 6445259 * 2
def baseEnd_6445259 : Nat := 3309515809716903628221299

theorem tailTrace_6445259 : CollatzResearch.WordTrace tailWord_6445259 prefixEnd_6445259 3309515809716903628221299 := by
  unfold tailWord_6445259
  simp only [CollatzResearch.WordTrace]
  refine ⟨235077908156934880446122831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156718605437956586964081887 235077908156934880446122831)
  ·
    refine ⟨352616862235402320669184247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235077908156934880446122831 352616862235402320669184247)
    ·
      refine ⟨528925293353103481003776371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352616862235402320669184247 528925293353103481003776371)
      ·
        refine ⟨793387940029655221505664557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528925293353103481003776371 793387940029655221505664557)
        ·
          refine ⟨297520477511120708064624209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 793387940029655221505664557 297520477511120708064624209)
          ·
            refine ⟨223140358133340531048468157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297520477511120708064624209 223140358133340531048468157)
            ·
              refine ⟨83677634300002699143175559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223140358133340531048468157 83677634300002699143175559)
              ·
                refine ⟨125516451450004048714763339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83677634300002699143175559 125516451450004048714763339)
                ·
                  refine ⟨188274677175006073072145009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125516451450004048714763339 188274677175006073072145009)
                  ·
                    refine ⟨141206007881254554804108757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188274677175006073072145009 141206007881254554804108757)
                    ·
                      refine ⟨3309515809716903628221299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141206007881254554804108757 3309515809716903628221299)
                      ·
                        rfl

theorem cell23_6445259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_6445259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445259 prefixEnd_6445259 := by exact prefixLift 6445259
  have htrace : WordTrace (prefixWord ++ tailWord_6445259) baseStart_6445259 baseEnd_6445259 := by
    simpa [prefixWord, tailWord_6445259, baseEnd_6445259] using wordTrace_append hprefix tailTrace_6445259
  have hstable : (prefixWord ++ tailWord_6445259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445259).length < 2 ^ (prefixWord ++ tailWord_6445259).sum := by decide
  have hdescent : baseEnd_6445259 < baseStart_6445259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445306 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_6445306 : Nat := 118140960795 + 6445306 * 2 ^ 59
def prefixEnd_6445306 : Nat := 4983230072969 + 3 ^ 40 * 6445306 * 2
def baseEnd_6445306 : Nat := 3309539943307664944333583

theorem tailTrace_6445306 : CollatzResearch.WordTrace tailWord_6445306 prefixEnd_6445306 3309539943307664944333583 := by
  unfold tailWord_6445306
  simp only [CollatzResearch.WordTrace]
  refine ⟨58769905596941151868270943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156719748258509738315389181 58769905596941151868270943)
  ·
    refine ⟨88154858395411727802406415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58769905596941151868270943 88154858395411727802406415)
    ·
      refine ⟨132232287593117591703609623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88154858395411727802406415 132232287593117591703609623)
      ·
        refine ⟨198348431389676387555414435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132232287593117591703609623 198348431389676387555414435)
        ·
          refine ⟨297522647084514581333121653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198348431389676387555414435 297522647084514581333121653)
          ·
            refine ⟨27892748164173241999980155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297522647084514581333121653 27892748164173241999980155)
            ·
              refine ⟨41839122246259862999970233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27892748164173241999980155 41839122246259862999970233)
              ·
                refine ⟨31379341684694897249977675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41839122246259862999970233 31379341684694897249977675)
                ·
                  refine ⟨47069012527042345874966513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31379341684694897249977675 47069012527042345874966513)
                  ·
                    refine ⟨35301759395281759406224885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47069012527042345874966513 35301759395281759406224885)
                    ·
                      refine ⟨3309539943307664944333583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35301759395281759406224885 3309539943307664944333583)
                      ·
                        rfl

theorem cell23_6445306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_6445306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445306 prefixEnd_6445306 := by exact prefixLift 6445306
  have htrace : WordTrace (prefixWord ++ tailWord_6445306) baseStart_6445306 baseEnd_6445306 := by
    simpa [prefixWord, tailWord_6445306, baseEnd_6445306] using wordTrace_append hprefix tailTrace_6445306
  have hstable : (prefixWord ++ tailWord_6445306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445306).length < 2 ^ (prefixWord ++ tailWord_6445306).sum := by decide
  have hdescent : baseEnd_6445306 < baseStart_6445306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445333 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_6445333 : Nat := 118140960795 + 6445333 * 2 ^ 59
def prefixEnd_6445333 : Nat := 4983230072969 + 3 ^ 40 * 6445333 * 2
def baseEnd_6445333 : Nat := 3309553807285336338695959

theorem tailTrace_6445333 : CollatzResearch.WordTrace tailWord_6445333 prefixEnd_6445333 3309553807285336338695959 := by
  unfold tailWord_6445333
  simp only [CollatzResearch.WordTrace]
  refine ⟨235080607158666791084316653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156720404772444527389544435 235080607158666791084316653)
  ·
    refine ⟨88155227684500046656618745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235080607158666791084316653 88155227684500046656618745)
    ·
      refine ⟨66116420763375034992464059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88155227684500046656618745 66116420763375034992464059)
      ·
        refine ⟨99174631145062552488696089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66116420763375034992464059 99174631145062552488696089)
        ·
          refine ⟨74380973358796914366522067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99174631145062552488696089 74380973358796914366522067)
          ·
            refine ⟨111571460038195371549783101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74380973358796914366522067 111571460038195371549783101)
            ·
              refine ⟨41839297514323264331168663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111571460038195371549783101 41839297514323264331168663)
              ·
                refine ⟨62758946271484896496752995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41839297514323264331168663 62758946271484896496752995)
                ·
                  refine ⟨94138419407227344745129493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62758946271484896496752995 94138419407227344745129493)
                  ·
                    refine ⟨4412738409713781784927945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94138419407227344745129493 4412738409713781784927945)
                    ·
                      refine ⟨3309553807285336338695959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412738409713781784927945 3309553807285336338695959)
                      ·
                        rfl

theorem cell23_6445333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_6445333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445333 prefixEnd_6445333 := by exact prefixLift 6445333
  have htrace : WordTrace (prefixWord ++ tailWord_6445333) baseStart_6445333 baseEnd_6445333 := by
    simpa [prefixWord, tailWord_6445333, baseEnd_6445333] using wordTrace_append hprefix tailTrace_6445333
  have hstable : (prefixWord ++ tailWord_6445333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445333).length < 2 ^ (prefixWord ++ tailWord_6445333).sum := by decide
  have hdescent : baseEnd_6445333 < baseStart_6445333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445343 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 5, 4]
def baseStart_6445343 : Nat := 118140960795 + 6445343 * 2 ^ 59
def prefixEnd_6445343 : Nat := 4983230072969 + 3 ^ 40 * 6445343 * 2
def baseEnd_6445343 : Nat := 1103186314030627099856971

theorem tailTrace_6445343 : CollatzResearch.WordTrace tailWord_6445343 prefixEnd_6445343 1103186314030627099856971 := by
  unfold tailWord_6445343
  simp only [CollatzResearch.WordTrace]
  refine ⟨235080971888630562792180683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156720647925753708528120455 235080971888630562792180683)
  ·
    refine ⟨352621457832945844188271025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235080971888630562792180683 352621457832945844188271025)
    ·
      refine ⟨264466093374709383141203269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352621457832945844188271025 264466093374709383141203269)
      ·
        refine ⟨49587392507758009338975613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264466093374709383141203269 49587392507758009338975613)
        ·
          refine ⟨18595272190409253502115855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49587392507758009338975613 18595272190409253502115855)
          ·
            refine ⟨27892908285613880253173783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18595272190409253502115855 27892908285613880253173783)
            ·
              refine ⟨41839362428420820379760675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27892908285613880253173783 41839362428420820379760675)
              ·
                refine ⟨62759043642631230569641013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41839362428420820379760675 62759043642631230569641013)
                ·
                  refine ⟨5883660341496677865903845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62759043642631230569641013 5883660341496677865903845)
                  ·
                    refine ⟨1103186314030627099856971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5883660341496677865903845 1103186314030627099856971)
                    ·
                      rfl

theorem cell23_6445343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_6445343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445343 prefixEnd_6445343 := by exact prefixLift 6445343
  have htrace : WordTrace (prefixWord ++ tailWord_6445343) baseStart_6445343 baseEnd_6445343 := by
    simpa [prefixWord, tailWord_6445343, baseEnd_6445343] using wordTrace_append hprefix tailTrace_6445343
  have hstable : (prefixWord ++ tailWord_6445343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445343).length < 2 ^ (prefixWord ++ tailWord_6445343).sum := by decide
  have hdescent : baseEnd_6445343 < baseStart_6445343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445377 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6445377 : Nat := 118140960795 + 6445377 * 2 ^ 59
def prefixEnd_6445377 : Nat := 4983230072969 + 3 ^ 40 * 6445377 * 2
def baseEnd_6445377 : Nat := 1103192133478044722181919

theorem tailTrace_6445377 : CollatzResearch.WordTrace tailWord_6445377 prefixEnd_6445377 1103192133478044722181919 := by
  unfold tailWord_6445377
  simp only [CollatzResearch.WordTrace]
  refine ⟨235082211970507386598918385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156721474647004924399278923 235082211970507386598918385)
  ·
    refine ⟨176311658977880539949188789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235082211970507386598918385 176311658977880539949188789)
    ·
      refine ⟨16529218029176300620236449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176311658977880539949188789 16529218029176300620236449)
      ·
        refine ⟨12396913521882225465177337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16529218029176300620236449 12396913521882225465177337)
        ·
          refine ⟨9297685141411669098883003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12396913521882225465177337 9297685141411669098883003)
          ·
            refine ⟨13946527712117503648324505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297685141411669098883003 13946527712117503648324505)
            ·
              refine ⟨10459895784088127736243379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13946527712117503648324505 10459895784088127736243379)
              ·
                refine ⟨15689843676132191604365069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459895784088127736243379 15689843676132191604365069)
                ·
                  refine ⟨5883691378549571851636901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15689843676132191604365069 5883691378549571851636901)
                  ·
                    refine ⟨1103192133478044722181919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5883691378549571851636901 1103192133478044722181919)
                    ·
                      rfl

theorem cell23_6445377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6445377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445377 prefixEnd_6445377 := by exact prefixLift 6445377
  have htrace : WordTrace (prefixWord ++ tailWord_6445377) baseStart_6445377 baseEnd_6445377 := by
    simpa [prefixWord, tailWord_6445377, baseEnd_6445377] using wordTrace_append hprefix tailTrace_6445377
  have hstable : (prefixWord ++ tailWord_6445377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445377).length < 2 ^ (prefixWord ++ tailWord_6445377).sum := by decide
  have hdescent : baseEnd_6445377 < baseStart_6445377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445456 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_6445456 : Nat := 118140960795 + 6445456 * 2 ^ 59
def prefixEnd_6445456 : Nat := 4983230072969 + 3 ^ 40 * 6445456 * 2
def baseEnd_6445456 : Nat := 3309616965405839357457893

theorem tailTrace_6445456 : CollatzResearch.WordTrace tailWord_6445456 prefixEnd_6445456 3309616965405839357457893 := by
  unfold tailWord_6445456
  simp only [CollatzResearch.WordTrace]
  refine ⟨117542546668610591545522111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156723395558147455394029481 117542546668610591545522111)
  ·
    refine ⟨176313820002915887318283167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117542546668610591545522111 176313820002915887318283167)
    ·
      refine ⟨264470730004373830977424751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176313820002915887318283167 264470730004373830977424751)
      ·
        refine ⟨396706095006560746466137127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264470730004373830977424751 396706095006560746466137127)
        ·
          refine ⟨595059142509841119699205691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396706095006560746466137127 595059142509841119699205691)
          ·
            refine ⟨892588713764761679548808537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595059142509841119699205691 892588713764761679548808537)
            ·
              refine ⟨669441535323571259661606403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892588713764761679548808537 669441535323571259661606403)
              ·
                refine ⟨1004162302985356889492409605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669441535323571259661606403 1004162302985356889492409605)
                ·
                  refine ⟨188280431809754416779826801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004162302985356889492409605 188280431809754416779826801)
                  ·
                    refine ⟨141210323857315812584870101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188280431809754416779826801 141210323857315812584870101)
                    ·
                      refine ⟨3309616965405839357457893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141210323857315812584870101 3309616965405839357457893)
                      ·
                        rfl

theorem cell23_6445456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_6445456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445456 prefixEnd_6445456 := by exact prefixLift 6445456
  have htrace : WordTrace (prefixWord ++ tailWord_6445456) baseStart_6445456 baseEnd_6445456 := by
    simpa [prefixWord, tailWord_6445456, baseEnd_6445456] using wordTrace_append hprefix tailTrace_6445456
  have hstable : (prefixWord ++ tailWord_6445456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445456).length < 2 ^ (prefixWord ++ tailWord_6445456).sum := by decide
  have hdescent : baseEnd_6445456 < baseStart_6445456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445477 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 1, 2, 3]
def baseStart_6445477 : Nat := 118140960795 + 6445477 * 2 ^ 59
def prefixEnd_6445477 : Nat := 4983230072969 + 3 ^ 40 * 6445477 * 2
def baseEnd_6445477 : Nat := 3309627748499583775295297

theorem tailTrace_6445477 : CollatzResearch.WordTrace tailWord_6445477 prefixEnd_6445477 3309627748499583775295297 := by
  unfold tailWord_6445477
  simp only [CollatzResearch.WordTrace]
  refine ⟨235085859270145103677558685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156723906180096735785039123 235085859270145103677558685)
  ·
    refine ⟨88157197226304413879084507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235085859270145103677558685 88157197226304413879084507)
    ·
      refine ⟨132235795839456620818626761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88157197226304413879084507 132235795839456620818626761)
      ·
        refine ⟨99176846879592465613970071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132235795839456620818626761 99176846879592465613970071)
        ·
          refine ⟨148765270319388698420955107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99176846879592465613970071 148765270319388698420955107)
          ·
            refine ⟨223147905479083047631432661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148765270319388698420955107 223147905479083047631432661)
            ·
              refine ⟨5230029034666008928861703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223147905479083047631432661 5230029034666008928861703)
              ·
                refine ⟨7845043551999013393292555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230029034666008928861703 7845043551999013393292555)
                ·
                  refine ⟨11767565327998520089938833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7845043551999013393292555 11767565327998520089938833)
                  ·
                    refine ⟨8825673995998890067454125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11767565327998520089938833 8825673995998890067454125)
                    ·
                      refine ⟨3309627748499583775295297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825673995998890067454125 3309627748499583775295297)
                      ·
                        rfl

theorem cell23_6445477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_6445477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445477 prefixEnd_6445477 := by exact prefixLift 6445477
  have htrace : WordTrace (prefixWord ++ tailWord_6445477) baseStart_6445477 baseEnd_6445477 := by
    simpa [prefixWord, tailWord_6445477, baseEnd_6445477] using wordTrace_append hprefix tailTrace_6445477
  have hstable : (prefixWord ++ tailWord_6445477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445477).length < 2 ^ (prefixWord ++ tailWord_6445477).sum := by decide
  have hdescent : baseEnd_6445477 < baseStart_6445477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445485 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6445485 : Nat := 118140960795 + 6445485 * 2 ^ 59
def prefixEnd_6445485 : Nat := 4983230072969 + 3 ^ 40 * 6445485 * 2
def baseEnd_6445485 : Nat := 3309631856344819743995261

theorem tailTrace_6445485 : CollatzResearch.WordTrace tailWord_6445485 prefixEnd_6445485 3309631856344819743995261 := by
  unfold tailWord_6445485
  simp only [CollatzResearch.WordTrace]
  refine ⟨235086151054116121043849909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156724100702744080695899939 235086151054116121043849909)
  ·
    refine ⟨22039326661323386347860929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235086151054116121043849909 22039326661323386347860929)
    ·
      refine ⟨16529494995992539760895697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22039326661323386347860929 16529494995992539760895697)
      ·
        refine ⟨12397121246994404820671773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16529494995992539760895697 12397121246994404820671773)
        ·
          refine ⟨4648920467622901807751915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12397121246994404820671773 4648920467622901807751915)
          ·
            refine ⟨6973380701434352711627873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648920467622901807751915 6973380701434352711627873)
            ·
              refine ⟨5230035526075764533720905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6973380701434352711627873 5230035526075764533720905)
              ·
                refine ⟨3922526644556823400290679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5230035526075764533720905 3922526644556823400290679)
                ·
                  refine ⟨5883789966835235100436019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922526644556823400290679 5883789966835235100436019)
                  ·
                    refine ⟨8825684950252852650654029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5883789966835235100436019 8825684950252852650654029)
                    ·
                      refine ⟨3309631856344819743995261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825684950252852650654029 3309631856344819743995261)
                      ·
                        rfl

theorem cell23_6445485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6445485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445485 prefixEnd_6445485 := by exact prefixLift 6445485
  have htrace : WordTrace (prefixWord ++ tailWord_6445485) baseStart_6445485 baseEnd_6445485 := by
    simpa [prefixWord, tailWord_6445485, baseEnd_6445485] using wordTrace_append hprefix tailTrace_6445485
  have hstable : (prefixWord ++ tailWord_6445485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445485).length < 2 ^ (prefixWord ++ tailWord_6445485).sum := by decide
  have hdescent : baseEnd_6445485 < baseStart_6445485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445541 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6445541 : Nat := 118140960795 + 6445541 * 2 ^ 59
def prefixEnd_6445541 : Nat := 4983230072969 + 3 ^ 40 * 6445541 * 2
def baseEnd_6445541 : Nat := 3309660611261471524895003

theorem tailTrace_6445541 : CollatzResearch.WordTrace tailWord_6445541 prefixEnd_6445541 3309660611261471524895003 := by
  unfold tailWord_6445541
  simp only [CollatzResearch.WordTrace]
  refine ⟨235088193541913242607888477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156725462361275495071925651 235088193541913242607888477)
  ·
    refine ⟨88158072578217465977958179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235088193541913242607888477 88158072578217465977958179)
    ·
      refine ⟨132237108867326198966937269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88158072578217465977958179 132237108867326198966937269)
      ·
        refine ⟨12397228956311831153150369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132237108867326198966937269 12397228956311831153150369)
        ·
          refine ⟨9297921717233873364862777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12397228956311831153150369 9297921717233873364862777)
          ·
            refine ⟨6973441287925405023647083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9297921717233873364862777 6973441287925405023647083)
            ·
              refine ⟨10460161931888107535470625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973441287925405023647083 10460161931888107535470625)
              ·
                refine ⟨7845121448916080651602969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10460161931888107535470625 7845121448916080651602969)
                ·
                  refine ⟨5883841086687060488702227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7845121448916080651602969 5883841086687060488702227)
                  ·
                    refine ⟨8825761630030590733053341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5883841086687060488702227 8825761630030590733053341)
                    ·
                      refine ⟨3309660611261471524895003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825761630030590733053341 3309660611261471524895003)
                      ·
                        rfl

theorem cell23_6445541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6445541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445541 prefixEnd_6445541 := by exact prefixLift 6445541
  have htrace : WordTrace (prefixWord ++ tailWord_6445541) baseStart_6445541 baseEnd_6445541 := by
    simpa [prefixWord, tailWord_6445541, baseEnd_6445541] using wordTrace_append hprefix tailTrace_6445541
  have hstable : (prefixWord ++ tailWord_6445541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445541).length < 2 ^ (prefixWord ++ tailWord_6445541).sum := by decide
  have hdescent : baseEnd_6445541 < baseStart_6445541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445547 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 4, 2, 2]
def baseStart_6445547 : Nat := 118140960795 + 6445547 * 2 ^ 59
def prefixEnd_6445547 : Nat := 4983230072969 + 3 ^ 40 * 6445547 * 2
def baseEnd_6445547 : Nat := 3309663692145398501419975

theorem tailTrace_6445547 : CollatzResearch.WordTrace tailWord_6445547 prefixEnd_6445547 3309663692145398501419975 := by
  unfold tailWord_6445547
  simp only [CollatzResearch.WordTrace]
  refine ⟨235088412379891505632606895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156725608253261003755071263 235088412379891505632606895)
  ·
    refine ⟨352632618569837258448910343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235088412379891505632606895 352632618569837258448910343)
    ·
      refine ⟨528948927854755887673365515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352632618569837258448910343 528948927854755887673365515)
      ·
        refine ⟨793423391782133831510048273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528948927854755887673365515 793423391782133831510048273)
        ·
          refine ⟨595067543836600373632536205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793423391782133831510048273 595067543836600373632536205)
          ·
            refine ⟨223150328938725140112201077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595067543836600373632536205 223150328938725140112201077)
            ·
              refine ⟨20920343338005481885518851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223150328938725140112201077 20920343338005481885518851)
              ·
                refine ⟨31380515007008222828278277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20920343338005481885518851 31380515007008222828278277)
                ·
                  refine ⟨5883846563814041780302177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31380515007008222828278277 5883846563814041780302177)
                  ·
                    refine ⟨4412884922860531335226633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883846563814041780302177 4412884922860531335226633)
                    ·
                      refine ⟨3309663692145398501419975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4412884922860531335226633 3309663692145398501419975)
                      ·
                        rfl

theorem cell23_6445547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 2, 2].length) (baseStart_6445547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445547 prefixEnd_6445547 := by exact prefixLift 6445547
  have htrace : WordTrace (prefixWord ++ tailWord_6445547) baseStart_6445547 baseEnd_6445547 := by
    simpa [prefixWord, tailWord_6445547, baseEnd_6445547] using wordTrace_append hprefix tailTrace_6445547
  have hstable : (prefixWord ++ tailWord_6445547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445547).length < 2 ^ (prefixWord ++ tailWord_6445547).sum := by decide
  have hdescent : baseEnd_6445547 < baseStart_6445547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445593 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_6445593 : Nat := 118140960795 + 6445593 * 2 ^ 59
def prefixEnd_6445593 : Nat := 4983230072969 + 3 ^ 40 * 6445593 * 2
def baseEnd_6445593 : Nat := 3309687312255505321444763

theorem tailTrace_6445593 : CollatzResearch.WordTrace tailWord_6445593 prefixEnd_6445593 3309687312255505321444763 := by
  unfold tailWord_6445593
  simp only [CollatzResearch.WordTrace]
  refine ⟨235090090137724855488781433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156726726758483236992520955 235090090137724855488781433)
  ·
    refine ⟨176317567603293641616586075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235090090137724855488781433 176317567603293641616586075)
    ·
      refine ⟨264476351404940462424879113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176317567603293641616586075 264476351404940462424879113)
      ·
        refine ⟨198357263553705346818659335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264476351404940462424879113 198357263553705346818659335)
        ·
          refine ⟨297535895330558020227989003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198357263553705346818659335 297535895330558020227989003)
          ·
            refine ⟨446303842995837030341983505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297535895330558020227989003 446303842995837030341983505)
            ·
              refine ⟨334727882246877772756487629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446303842995837030341983505 334727882246877772756487629)
              ·
                refine ⟨125522955842579164783682861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334727882246877772756487629 125522955842579164783682861)
                ·
                  refine ⟨47071108440967186793881073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125522955842579164783682861 47071108440967186793881073)
                  ·
                    refine ⟨35303331330725390095410805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47071108440967186793881073 35303331330725390095410805)
                    ·
                      refine ⟨3309687312255505321444763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35303331330725390095410805 3309687312255505321444763)
                      ·
                        rfl

theorem cell23_6445593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_6445593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445593 prefixEnd_6445593 := by exact prefixLift 6445593
  have htrace : WordTrace (prefixWord ++ tailWord_6445593) baseStart_6445593 baseEnd_6445593 := by
    simpa [prefixWord, tailWord_6445593, baseEnd_6445593] using wordTrace_append hprefix tailTrace_6445593
  have hstable : (prefixWord ++ tailWord_6445593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445593).length < 2 ^ (prefixWord ++ tailWord_6445593).sum := by decide
  have hdescent : baseEnd_6445593 < baseStart_6445593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445604 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 7]
def baseStart_6445604 : Nat := 118140960795 + 6445604 * 2 ^ 59
def prefixEnd_6445604 : Nat := 4983230072969 + 3 ^ 40 * 6445604 * 2
def baseEnd_6445604 : Nat := 367743662282522753156357

theorem tailTrace_6445604 : CollatzResearch.WordTrace tailWord_6445604 prefixEnd_6445604 367743662282522753156357 := by
  unfold tailWord_6445604
  simp only [CollatzResearch.WordTrace]
  refine ⟨117545245670342502183715933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156726994227123336244954577 117545245670342502183715933)
  ·
    refine ⟨44079467126378438318893475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117545245670342502183715933 44079467126378438318893475)
    ·
      refine ⟨66119200689567657478340213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44079467126378438318893475 66119200689567657478340213)
      ·
        refine ⟨6198675064646967888594395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66119200689567657478340213 6198675064646967888594395)
        ·
          refine ⟨9298012596970451832891593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198675064646967888594395 9298012596970451832891593)
          ·
            refine ⟨6973509447727838874668695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9298012596970451832891593 6973509447727838874668695)
            ·
              refine ⟨10460264171591758312003043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973509447727838874668695 10460264171591758312003043)
              ·
                refine ⟨15690396257387637468004565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460264171591758312003043 15690396257387637468004565)
                ·
                  refine ⟨367743662282522753156357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15690396257387637468004565 367743662282522753156357)
                  ·
                    rfl

theorem cell23_6445604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_6445604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445604 prefixEnd_6445604 := by exact prefixLift 6445604
  have htrace : WordTrace (prefixWord ++ tailWord_6445604) baseStart_6445604 baseEnd_6445604 := by
    simpa [prefixWord, tailWord_6445604, baseEnd_6445604] using wordTrace_append hprefix tailTrace_6445604
  have hstable : (prefixWord ++ tailWord_6445604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445604).length < 2 ^ (prefixWord ++ tailWord_6445604).sum := by decide
  have hdescent : baseEnd_6445604 < baseStart_6445604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445610 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6445610 : Nat := 118140960795 + 6445610 * 2 ^ 59
def prefixEnd_6445610 : Nat := 4983230072969 + 3 ^ 40 * 6445610 * 2
def baseEnd_6445610 : Nat := 3309696041426631754932185

theorem tailTrace_6445610 : CollatzResearch.WordTrace tailWord_6445610 prefixEnd_6445610 3309696041426631754932185 := by
  unfold tailWord_6445610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58772677544665816848037571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156727140119108844928100189 58772677544665816848037571)
  ·
    refine ⟨88159016316998725272056357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58772677544665816848037571 88159016316998725272056357)
    ·
      refine ⟨16529815559437260988510567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88159016316998725272056357 16529815559437260988510567)
      ·
        refine ⟨24794723339155891482765851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16529815559437260988510567 24794723339155891482765851)
        ·
          refine ⟨37192085008733837224148777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24794723339155891482765851 37192085008733837224148777)
          ·
            refine ⟨27894063756550377918111583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37192085008733837224148777 27894063756550377918111583)
            ·
              refine ⟨41841095634825566877167375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27894063756550377918111583 41841095634825566877167375)
              ·
                refine ⟨62761643452238350315751063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41841095634825566877167375 62761643452238350315751063)
                ·
                  refine ⟨94142465178357525473626595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62761643452238350315751063 94142465178357525473626595)
                  ·
                    refine ⟨141213697767536288210439893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94142465178357525473626595 141213697767536288210439893)
                    ·
                      refine ⟨3309696041426631754932185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141213697767536288210439893 3309696041426631754932185)
                      ·
                        rfl

theorem cell23_6445610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6445610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445610 prefixEnd_6445610 := by exact prefixLift 6445610
  have htrace : WordTrace (prefixWord ++ tailWord_6445610) baseStart_6445610 baseEnd_6445610 := by
    simpa [prefixWord, tailWord_6445610, baseEnd_6445610] using wordTrace_append hprefix tailTrace_6445610
  have hstable : (prefixWord ++ tailWord_6445610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445610).length < 2 ^ (prefixWord ++ tailWord_6445610).sum := by decide
  have hdescent : baseEnd_6445610 < baseStart_6445610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445637 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_6445637 : Nat := 118140960795 + 6445637 * 2 ^ 59
def prefixEnd_6445637 : Nat := 4983230072969 + 3 ^ 40 * 6445637 * 2
def baseEnd_6445637 : Nat := 3309709905404303149294561

theorem tailTrace_6445637 : CollatzResearch.WordTrace tailWord_6445637 prefixEnd_6445637 3309709905404303149294561 := by
  unfold tailWord_6445637
  simp only [CollatzResearch.WordTrace]
  refine ⟨235091694949565451003383165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156727796633043634002255443 235091694949565451003383165)
  ·
    refine ⟨88159385606087044126268687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235091694949565451003383165 88159385606087044126268687)
    ·
      refine ⟨132239078409130566189403031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88159385606087044126268687 132239078409130566189403031)
      ·
        refine ⟨198358617613695849284104547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132239078409130566189403031 198358617613695849284104547)
        ·
          refine ⟨297537926420543773926156821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198358617613695849284104547 297537926420543773926156821)
          ·
            refine ⟨13947090300962989402788601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 297537926420543773926156821 13947090300962989402788601)
            ·
              refine ⟨10460317725722242052091451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13947090300962989402788601 10460317725722242052091451)
              ·
                refine ⟨15690476588583363078137177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460317725722242052091451 15690476588583363078137177)
                ·
                  refine ⟨11767857441437522308602883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15690476588583363078137177 11767857441437522308602883)
                  ·
                    refine ⟨17651786162156283462904325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11767857441437522308602883 17651786162156283462904325)
                    ·
                      refine ⟨3309709905404303149294561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17651786162156283462904325 3309709905404303149294561)
                      ·
                        rfl

theorem cell23_6445637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_6445637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445637 prefixEnd_6445637 := by exact prefixLift 6445637
  have htrace : WordTrace (prefixWord ++ tailWord_6445637) baseStart_6445637 baseEnd_6445637 := by
    simpa [prefixWord, tailWord_6445637, baseEnd_6445637] using wordTrace_append hprefix tailTrace_6445637
  have hstable : (prefixWord ++ tailWord_6445637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445637).length < 2 ^ (prefixWord ++ tailWord_6445637).sum := by decide
  have hdescent : baseEnd_6445637 < baseStart_6445637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445640 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_6445640 : Nat := 118140960795 + 6445640 * 2 ^ 59
def prefixEnd_6445640 : Nat := 4983230072969 + 3 ^ 40 * 6445640 * 2
def baseEnd_6445640 : Nat := 3309711445846266637557047

theorem tailTrace_6445640 : CollatzResearch.WordTrace tailWord_6445640 prefixEnd_6445640 3309711445846266637557047 := by
  unfold tailWord_6445640
  simp only [CollatzResearch.WordTrace]
  refine ⟨117545902184277291257871187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156727869579036388343828249 117545902184277291257871187)
  ·
    refine ⟨176318853276415936886806781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117545902184277291257871187 176318853276415936886806781)
    ·
      refine ⟨66119569978655976332552543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176318853276415936886806781 66119569978655976332552543)
      ·
        refine ⟨99179354967983964498828815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66119569978655976332552543 99179354967983964498828815)
        ·
          refine ⟨148769032451975946748243223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99179354967983964498828815 148769032451975946748243223)
          ·
            refine ⟨223153548677963920122364835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148769032451975946748243223 223153548677963920122364835)
            ·
              refine ⟨334730323016945880183547253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223153548677963920122364835 334730323016945880183547253)
              ·
                refine ⟨31380967782838676267207555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334730323016945880183547253 31380967782838676267207555)
                ·
                  refine ⟨47071451674258014400811333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31380967782838676267207555 47071451674258014400811333)
                  ·
                    refine ⟨8825897188923377700152125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47071451674258014400811333 8825897188923377700152125)
                    ·
                      refine ⟨3309711445846266637557047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825897188923377700152125 3309711445846266637557047)
                      ·
                        rfl

theorem cell23_6445640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_6445640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445640 prefixEnd_6445640 := by exact prefixLift 6445640
  have htrace : WordTrace (prefixWord ++ tailWord_6445640) baseStart_6445640 baseEnd_6445640 := by
    simpa [prefixWord, tailWord_6445640, baseEnd_6445640] using wordTrace_append hprefix tailTrace_6445640
  have hstable : (prefixWord ++ tailWord_6445640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445640).length < 2 ^ (prefixWord ++ tailWord_6445640).sum := by decide
  have hdescent : baseEnd_6445640 < baseStart_6445640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445643 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 10]
def baseStart_6445643 : Nat := 118140960795 + 6445643 * 2 ^ 59
def prefixEnd_6445643 : Nat := 4983230072969 + 3 ^ 40 * 6445643 * 2
def baseEnd_6445643 : Nat := 367745887365358902868837

theorem tailTrace_6445643 : CollatzResearch.WordTrace tailWord_6445643 prefixEnd_6445643 367745887365358902868837 := by
  unfold tailWord_6445643
  simp only [CollatzResearch.WordTrace]
  refine ⟨235091913787543714028101583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156727942525029142685401055 235091913787543714028101583)
  ·
    refine ⟨352637870681315571042152375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235091913787543714028101583 352637870681315571042152375)
    ·
      refine ⟨528956806021973356563228563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352637870681315571042152375 528956806021973356563228563)
      ·
        refine ⟨793435209032960034844842845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528956806021973356563228563 793435209032960034844842845)
        ·
          refine ⟨297538203387360013066816067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 793435209032960034844842845 297538203387360013066816067)
          ·
            refine ⟨446307305081040019600224101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297538203387360013066816067 446307305081040019600224101)
            ·
              refine ⟨83682619702695003675042019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 446307305081040019600224101 83682619702695003675042019)
              ·
                refine ⟨125523929554042505512563029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83682619702695003675042019 125523929554042505512563029)
                ·
                  refine ⟨367745887365358902868837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 125523929554042505512563029 367745887365358902868837)
                  ·
                    rfl

theorem cell23_6445643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 10].length) (baseStart_6445643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445643 prefixEnd_6445643 := by exact prefixLift 6445643
  have htrace : WordTrace (prefixWord ++ tailWord_6445643) baseStart_6445643 baseEnd_6445643 := by
    simpa [prefixWord, tailWord_6445643, baseEnd_6445643] using wordTrace_append hprefix tailTrace_6445643
  have hstable : (prefixWord ++ tailWord_6445643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445643).length < 2 ^ (prefixWord ++ tailWord_6445643).sum := by decide
  have hdescent : baseEnd_6445643 < baseStart_6445643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445650 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6445650 : Nat := 118140960795 + 6445650 * 2 ^ 59
def prefixEnd_6445650 : Nat := 4983230072969 + 3 ^ 40 * 6445650 * 2
def baseEnd_6445650 : Nat := 3309716580652811598432001

theorem tailTrace_6445650 : CollatzResearch.WordTrace tailWord_6445650 prefixEnd_6445650 3309716580652811598432001 := by
  unfold tailWord_6445650
  simp only [CollatzResearch.WordTrace]
  refine ⟨58773042274629588555901601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156728112732345569482404269 58773042274629588555901601)
  ·
    refine ⟨44079781705972191416926201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58773042274629588555901601 44079781705972191416926201)
    ·
      refine ⟨33059836279479143562694651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44079781705972191416926201 33059836279479143562694651)
      ·
        refine ⟨49589754419218715344041977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33059836279479143562694651 49589754419218715344041977)
        ·
          refine ⟨37192315814414036508031483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49589754419218715344041977 37192315814414036508031483)
          ·
            refine ⟨55788473721621054762047225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37192315814414036508031483 55788473721621054762047225)
            ·
              refine ⟨41841355291215791071535419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55788473721621054762047225 41841355291215791071535419)
              ·
                refine ⟨62762032936823686607303129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41841355291215791071535419 62762032936823686607303129)
                ·
                  refine ⟨47071524702617764955477347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62762032936823686607303129 47071524702617764955477347)
                  ·
                    refine ⟨70607287053926647433216021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47071524702617764955477347 70607287053926647433216021)
                    ·
                      refine ⟨3309716580652811598432001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70607287053926647433216021 3309716580652811598432001)
                      ·
                        rfl

theorem cell23_6445650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6445650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445650 prefixEnd_6445650 := by exact prefixLift 6445650
  have htrace : WordTrace (prefixWord ++ tailWord_6445650) baseStart_6445650 baseEnd_6445650 := by
    simpa [prefixWord, tailWord_6445650, baseEnd_6445650] using wordTrace_append hprefix tailTrace_6445650
  have hstable : (prefixWord ++ tailWord_6445650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445650).length < 2 ^ (prefixWord ++ tailWord_6445650).sum := by decide
  have hdescent : baseEnd_6445650 < baseStart_6445650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445677 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 6]
def baseStart_6445677 : Nat := 118140960795 + 6445677 * 2 ^ 59
def prefixEnd_6445677 : Nat := 4983230072969 + 3 ^ 40 * 6445677 * 2
def baseEnd_6445677 : Nat := 367747827181164776977153

theorem tailTrace_6445677 : CollatzResearch.WordTrace tailWord_6445677 prefixEnd_6445677 367747827181164776977153 := by
  unfold tailWord_6445677
  simp only [CollatzResearch.WordTrace]
  refine ⟨235093153869420537834839285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156728769246280358556559523 235093153869420537834839285)
  ·
    refine ⟨22039983175258175422016183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235093153869420537834839285 22039983175258175422016183)
    ·
      refine ⟨33059974762887263133024275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22039983175258175422016183 33059974762887263133024275)
      ·
        refine ⟨49589962144330894699536413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33059974762887263133024275 49589962144330894699536413)
        ·
          refine ⟨18596235804124085512326155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49589962144330894699536413 18596235804124085512326155)
          ·
            refine ⟨27894353706186128268489233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18596235804124085512326155 27894353706186128268489233)
            ·
              refine ⟨20920765279639596201366925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27894353706186128268489233 20920765279639596201366925)
              ·
                refine ⟨7845286979864848575512597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20920765279639596201366925 7845286979864848575512597)
                ·
                  refine ⟨367747827181164776977153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7845286979864848575512597 367747827181164776977153)
                  ·
                    rfl

theorem cell23_6445677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_6445677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445677 prefixEnd_6445677 := by exact prefixLift 6445677
  have htrace : WordTrace (prefixWord ++ tailWord_6445677) baseStart_6445677 baseEnd_6445677 := by
    simpa [prefixWord, tailWord_6445677, baseEnd_6445677] using wordTrace_append hprefix tailTrace_6445677
  have hstable : (prefixWord ++ tailWord_6445677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445677).length < 2 ^ (prefixWord ++ tailWord_6445677).sum := by decide
  have hdescent : baseEnd_6445677 < baseStart_6445677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445687 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_6445687 : Nat := 118140960795 + 6445687 * 2 ^ 59
def prefixEnd_6445687 : Nat := 4983230072969 + 3 ^ 40 * 6445687 * 2
def baseEnd_6445687 : Nat := 3309735579437027953669331

theorem tailTrace_6445687 : CollatzResearch.WordTrace tailWord_6445687 prefixEnd_6445687 3309735579437027953669331 := by
  unfold tailWord_6445687
  simp only [CollatzResearch.WordTrace]
  refine ⟨235093518599384309542703315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156729012399589539695135543 235093518599384309542703315)
  ·
    refine ⟨352640277899076464314054973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235093518599384309542703315 352640277899076464314054973)
    ·
      refine ⟨132240104212153674117770615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352640277899076464314054973 132240104212153674117770615)
      ·
        refine ⟨198360156318230511176655923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132240104212153674117770615 198360156318230511176655923)
        ·
          refine ⟨297540234477345766764983885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198360156318230511176655923 297540234477345766764983885)
          ·
            refine ⟨111577587929004662536868957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297540234477345766764983885 111577587929004662536868957)
            ·
              refine ⟨41841595473376748451325859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111577587929004662536868957 41841595473376748451325859)
              ·
                refine ⟨62762393210065122676988789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41841595473376748451325859 62762393210065122676988789)
                ·
                  refine ⟨5883974363443605250967699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62762393210065122676988789 5883974363443605250967699)
                  ·
                    refine ⟨8825961545165407876451549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5883974363443605250967699 8825961545165407876451549)
                    ·
                      refine ⟨3309735579437027953669331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8825961545165407876451549 3309735579437027953669331)
                      ·
                        rfl

theorem cell23_6445687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_6445687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445687 prefixEnd_6445687 := by exact prefixLift 6445687
  have htrace : WordTrace (prefixWord ++ tailWord_6445687) baseStart_6445687 baseEnd_6445687 := by
    simpa [prefixWord, tailWord_6445687, baseEnd_6445687] using wordTrace_append hprefix tailTrace_6445687
  have hstable : (prefixWord ++ tailWord_6445687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445687).length < 2 ^ (prefixWord ++ tailWord_6445687).sum := by decide
  have hdescent : baseEnd_6445687 < baseStart_6445687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445764 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_6445764 : Nat := 118140960795 + 6445764 * 2 ^ 59
def prefixEnd_6445764 : Nat := 4983230072969 + 3 ^ 40 * 6445764 * 2
def baseEnd_6445764 : Nat := 3309775117447424152406477

theorem tailTrace_6445764 : CollatzResearch.WordTrace tailWord_6445764 prefixEnd_6445764 3309775117447424152406477 := by
  unfold tailWord_6445764
  simp only [CollatzResearch.WordTrace]
  refine ⟨117548163510052675846628173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156730884680070234462170897 117548163510052675846628173)
  ·
    refine ⟨44080561316269753442485565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117548163510052675846628173 44080561316269753442485565)
    ·
      refine ⟨16530210493601157540932087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44080561316269753442485565 16530210493601157540932087)
      ·
        refine ⟨24795315740401736311398131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16530210493601157540932087 24795315740401736311398131)
        ·
          refine ⟨37192973610602604467097197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24795315740401736311398131 37192973610602604467097197)
          ·
            refine ⟨13947365103975976675161449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37192973610602604467097197 13947365103975976675161449)
            ·
              refine ⟨10460523827981982506371087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13947365103975976675161449 10460523827981982506371087)
              ·
                refine ⟨15690785741972973759556631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460523827981982506371087 15690785741972973759556631)
                ·
                  refine ⟨23536178612959460639334947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15690785741972973759556631 23536178612959460639334947)
                  ·
                    refine ⟨35304267919439190959002421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23536178612959460639334947 35304267919439190959002421)
                    ·
                      refine ⟨3309775117447424152406477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35304267919439190959002421 3309775117447424152406477)
                      ·
                        rfl

theorem cell23_6445764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_6445764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445764 prefixEnd_6445764 := by exact prefixLift 6445764
  have htrace : WordTrace (prefixWord ++ tailWord_6445764) baseStart_6445764 baseEnd_6445764 := by
    simpa [prefixWord, tailWord_6445764, baseEnd_6445764] using wordTrace_append hprefix tailTrace_6445764
  have hstable : (prefixWord ++ tailWord_6445764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445764).length < 2 ^ (prefixWord ++ tailWord_6445764).sum := by decide
  have hdescent : baseEnd_6445764 < baseStart_6445764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445788 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6445788 : Nat := 118140960795 + 6445788 * 2 ^ 59
def prefixEnd_6445788 : Nat := 4983230072969 + 3 ^ 40 * 6445788 * 2
def baseEnd_6445788 : Nat := 1103262480327710686168789

theorem tailTrace_6445788 : CollatzResearch.WordTrace tailWord_6445788 prefixEnd_6445788 1103262480327710686168789 := by
  unfold tailWord_6445788
  simp only [CollatzResearch.WordTrace]
  refine ⟨117548601186009201896065009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156731468248012269194753345 117548601186009201896065009)
  ·
    refine ⟨88161450889506901422048757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117548601186009201896065009 88161450889506901422048757)
    ·
      refine ⟨8265136020891272008317071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88161450889506901422048757 8265136020891272008317071)
      ·
        refine ⟨12397704031336908012475607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8265136020891272008317071 12397704031336908012475607)
        ·
          refine ⟨18596556047005362018713411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12397704031336908012475607 18596556047005362018713411)
          ·
            refine ⟨27894834070508043028070117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18596556047005362018713411 27894834070508043028070117)
            ·
              refine ⟨5230281388220258067763147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27894834070508043028070117 5230281388220258067763147)
              ·
                refine ⟨7845422082330387101644721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230281388220258067763147 7845422082330387101644721)
                ·
                  refine ⟨5884066561747790326233541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7845422082330387101644721 5884066561747790326233541)
                  ·
                    refine ⟨1103262480327710686168789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884066561747790326233541 1103262480327710686168789)
                    ·
                      rfl

theorem cell23_6445788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6445788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445788 prefixEnd_6445788 := by exact prefixLift 6445788
  have htrace : WordTrace (prefixWord ++ tailWord_6445788) baseStart_6445788 baseEnd_6445788 := by
    simpa [prefixWord, tailWord_6445788, baseEnd_6445788] using wordTrace_append hprefix tailTrace_6445788
  have hstable : (prefixWord ++ tailWord_6445788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445788).length < 2 ^ (prefixWord ++ tailWord_6445788).sum := by decide
  have hdescent : baseEnd_6445788 < baseStart_6445788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445834 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_6445834 : Nat := 118140960795 + 6445834 * 2 ^ 59
def prefixEnd_6445834 : Nat := 4983230072969 + 3 ^ 40 * 6445834 * 2
def baseEnd_6445834 : Nat := 3309811061093238878531155

theorem tailTrace_6445834 : CollatzResearch.WordTrace tailWord_6445834 prefixEnd_6445834 3309811061093238878531155 := by
  unfold tailWord_6445834
  simp only [CollatzResearch.WordTrace]
  refine ⟨58774720032462938412076139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156732586753234502432203037 58774720032462938412076139)
  ·
    refine ⟨88162080048694407618114209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58774720032462938412076139 88162080048694407618114209)
    ·
      refine ⟨66121560036520805713585657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88162080048694407618114209 66121560036520805713585657)
      ·
        refine ⟨49591170027390604285189243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66121560036520805713585657 49591170027390604285189243)
        ·
          refine ⟨74386755041085906427783865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49591170027390604285189243 74386755041085906427783865)
          ·
            refine ⟨55790066280814429820837899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74386755041085906427783865 55790066280814429820837899)
            ·
              refine ⟨83685099421221644731256849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55790066280814429820837899 83685099421221644731256849)
              ·
                refine ⟨62763824565916233548442637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83685099421221644731256849 62763824565916233548442637)
                ·
                  refine ⟨23536434212218587580665989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62763824565916233548442637 23536434212218587580665989)
                  ·
                    refine ⟨4413081414790985171374873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23536434212218587580665989 4413081414790985171374873)
                    ·
                      refine ⟨3309811061093238878531155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413081414790985171374873 3309811061093238878531155)
                      ·
                        rfl

theorem cell23_6445834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_6445834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445834 prefixEnd_6445834 := by exact prefixLift 6445834
  have htrace : WordTrace (prefixWord ++ tailWord_6445834) baseStart_6445834 baseEnd_6445834 := by
    simpa [prefixWord, tailWord_6445834, baseEnd_6445834] using wordTrace_append hprefix tailTrace_6445834
  have hstable : (prefixWord ++ tailWord_6445834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445834).length < 2 ^ (prefixWord ++ tailWord_6445834).sum := by decide
  have hdescent : baseEnd_6445834 < baseStart_6445834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445857 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 7]
def baseStart_6445857 : Nat := 118140960795 + 6445857 * 2 ^ 59
def prefixEnd_6445857 : Nat := 4983230072969 + 3 ^ 40 * 6445857 * 2
def baseEnd_6445857 : Nat := 367758096794254698727061

theorem tailTrace_6445857 : CollatzResearch.WordTrace tailWord_6445857 prefixEnd_6445857 367758096794254698727061 := by
  unfold tailWord_6445857
  simp only [CollatzResearch.WordTrace]
  refine ⟨235099719008768428576391825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156733146005845619050927883 235099719008768428576391825)
  ·
    refine ⟨176324789256576321432293869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235099719008768428576391825 176324789256576321432293869)
    ·
      refine ⟨66121795971216120537110201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176324789256576321432293869 66121795971216120537110201)
      ·
        refine ⟨49591346978412090402832651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66121795971216120537110201 49591346978412090402832651)
        ·
          refine ⟨74387020467618135604248977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49591346978412090402832651 74387020467618135604248977)
          ·
            refine ⟨55790265350713601703186733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74387020467618135604248977 55790265350713601703186733)
            ·
              refine ⟨20921349506517600638695025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55790265350713601703186733 20921349506517600638695025)
              ·
                refine ⟨15691012129888200479021269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20921349506517600638695025 15691012129888200479021269)
                ·
                  refine ⟨367758096794254698727061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15691012129888200479021269 367758096794254698727061)
                  ·
                    rfl

theorem cell23_6445857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_6445857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445857 prefixEnd_6445857 := by exact prefixLift 6445857
  have htrace : WordTrace (prefixWord ++ tailWord_6445857) baseStart_6445857 baseEnd_6445857 := by
    simpa [prefixWord, tailWord_6445857, baseEnd_6445857] using wordTrace_append hprefix tailTrace_6445857
  have hstable : (prefixWord ++ tailWord_6445857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445857).length < 2 ^ (prefixWord ++ tailWord_6445857).sum := by decide
  have hdescent : baseEnd_6445857 < baseStart_6445857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445867 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 3]
def baseStart_6445867 : Nat := 118140960795 + 6445867 * 2 ^ 59
def prefixEnd_6445867 : Nat := 4983230072969 + 3 ^ 40 * 6445867 * 2
def baseEnd_6445867 : Nat := 3309828005954837249418503

theorem tailTrace_6445867 : CollatzResearch.WordTrace tailWord_6445867 prefixEnd_6445867 3309828005954837249418503 := by
  unfold tailWord_6445867
  simp only [CollatzResearch.WordTrace]
  refine ⟨235100083738732200284255855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156733389159154800189503903 235100083738732200284255855)
  ·
    refine ⟨352650125608098300426383783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235100083738732200284255855 352650125608098300426383783)
    ·
      refine ⟨528975188412147450639575675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352650125608098300426383783 528975188412147450639575675)
      ·
        refine ⟨793462782618221175959363513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528975188412147450639575675 793462782618221175959363513)
        ·
          refine ⟨595097086963665881969522635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793462782618221175959363513 595097086963665881969522635)
          ·
            refine ⟨892645630445498822954283953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595097086963665881969522635 892645630445498822954283953)
            ·
              refine ⟨669484222834124117215712965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892645630445498822954283953 669484222834124117215712965)
              ·
                refine ⟨125528291781398271977946181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669484222834124117215712965 125528291781398271977946181)
                ·
                  refine ⟨23536554709012175995864909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125528291781398271977946181 23536554709012175995864909)
                  ·
                    refine ⟨8826208015879565998449341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23536554709012175995864909 8826208015879565998449341)
                    ·
                      refine ⟨3309828005954837249418503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8826208015879565998449341 3309828005954837249418503)
                      ·
                        rfl

theorem cell23_6445867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 3].length) (baseStart_6445867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445867 prefixEnd_6445867 := by exact prefixLift 6445867
  have htrace : WordTrace (prefixWord ++ tailWord_6445867) baseStart_6445867 baseEnd_6445867 := by
    simpa [prefixWord, tailWord_6445867, baseEnd_6445867] using wordTrace_append hprefix tailTrace_6445867
  have hstable : (prefixWord ++ tailWord_6445867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445867).length < 2 ^ (prefixWord ++ tailWord_6445867).sum := by decide
  have hdescent : baseEnd_6445867 < baseStart_6445867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445924 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_6445924 : Nat := 118140960795 + 6445924 * 2 ^ 59
def prefixEnd_6445924 : Nat := 4983230072969 + 3 ^ 40 * 6445924 * 2
def baseEnd_6445924 : Nat := 3309857274352143526405741

theorem tailTrace_6445924 : CollatzResearch.WordTrace tailWord_6445924 prefixEnd_6445924 3309857274352143526405741 := by
  unfold tailWord_6445924
  simp only [CollatzResearch.WordTrace]
  refine ⟨117551081349762849509540413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156734775133017132679387217 117551081349762849509540413)
  ·
    refine ⟨44081655506161068566077655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117551081349762849509540413 44081655506161068566077655)
    ·
      refine ⟨66122483259241602849116483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44081655506161068566077655 66122483259241602849116483)
      ·
        refine ⟨99183724888862404273674725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66122483259241602849116483 99183724888862404273674725)
        ·
          refine ⟨18596948416661700801314011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99183724888862404273674725 18596948416661700801314011)
          ·
            refine ⟨27895422624992551201971017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18596948416661700801314011 27895422624992551201971017)
            ·
              refine ⟨20921566968744413401478263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27895422624992551201971017 20921566968744413401478263)
              ·
                refine ⟨31382350453116620102217395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20921566968744413401478263 31382350453116620102217395)
                ·
                  refine ⟨47073525679674930153326093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31382350453116620102217395 47073525679674930153326093)
                  ·
                    refine ⟨17652572129878098807497285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47073525679674930153326093 17652572129878098807497285)
                    ·
                      refine ⟨3309857274352143526405741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17652572129878098807497285 3309857274352143526405741)
                      ·
                        rfl

theorem cell23_6445924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_6445924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445924 prefixEnd_6445924 := by exact prefixLift 6445924
  have htrace : WordTrace (prefixWord ++ tailWord_6445924) baseStart_6445924 baseEnd_6445924 := by
    simpa [prefixWord, tailWord_6445924, baseEnd_6445924] using wordTrace_append hprefix tailTrace_6445924
  have hstable : (prefixWord ++ tailWord_6445924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445924).length < 2 ^ (prefixWord ++ tailWord_6445924).sum := by decide
  have hdescent : baseEnd_6445924 < baseStart_6445924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445941 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6445941 : Nat := 118140960795 + 6445941 * 2 ^ 59
def prefixEnd_6445941 : Nat := 4983230072969 + 3 ^ 40 * 6445941 * 2
def baseEnd_6445941 : Nat := 3309866003523269959893163

theorem tailTrace_6445941 : CollatzResearch.WordTrace tailWord_6445941 prefixEnd_6445941 3309866003523269959893163 := by
  unfold tailWord_6445941
  simp only [CollatzResearch.WordTrace]
  refine ⟨235102782740464110922449677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156735188493642740614966451 235102782740464110922449677)
  ·
    refine ⟨88163543527674041595918629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235102782740464110922449677 88163543527674041595918629)
    ·
      refine ⟨16530664411438882799234743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88163543527674041595918629 16530664411438882799234743)
      ·
        refine ⟨24795996617158324198852115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16530664411438882799234743 24795996617158324198852115)
        ·
          refine ⟨37193994925737486298278173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24795996617158324198852115 37193994925737486298278173)
          ·
            refine ⟨13947748097151557361854315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37193994925737486298278173 13947748097151557361854315)
            ·
              refine ⟨20921622145727336042781473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13947748097151557361854315 20921622145727336042781473)
              ·
                refine ⟨15691216609295502032086105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20921622145727336042781473 15691216609295502032086105)
                ·
                  refine ⟨11768412456971626524064579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15691216609295502032086105 11768412456971626524064579)
                  ·
                    refine ⟨17652618685457439786096869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11768412456971626524064579 17652618685457439786096869)
                    ·
                      refine ⟨3309866003523269959893163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17652618685457439786096869 3309866003523269959893163)
                      ·
                        rfl

theorem cell23_6445941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6445941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445941 prefixEnd_6445941 := by exact prefixLift 6445941
  have htrace : WordTrace (prefixWord ++ tailWord_6445941) baseStart_6445941 baseEnd_6445941 := by
    simpa [prefixWord, tailWord_6445941, baseEnd_6445941] using wordTrace_append hprefix tailTrace_6445941
  have hstable : (prefixWord ++ tailWord_6445941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445941).length < 2 ^ (prefixWord ++ tailWord_6445941).sum := by decide
  have hdescent : baseEnd_6445941 < baseStart_6445941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445947 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 8]
def baseStart_6445947 : Nat := 118140960795 + 6445947 * 2 ^ 59
def prefixEnd_6445947 : Nat := 4983230072969 + 3 ^ 40 * 6445947 * 2
def baseEnd_6445947 : Nat := 367763231600799659602015

theorem tailTrace_6445947 : CollatzResearch.WordTrace tailWord_6445947 prefixEnd_6445947 367763231600799659602015 := by
  unfold tailWord_6445947
  simp only [CollatzResearch.WordTrace]
  refine ⟨235103001578442373947168095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156735334385628249298112063 235103001578442373947168095)
  ·
    refine ⟨352654502367663560920752143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235103001578442373947168095 352654502367663560920752143)
    ·
      refine ⟨528981753551495341381128215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352654502367663560920752143 528981753551495341381128215)
      ·
        refine ⟨793472630327243012071692323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528981753551495341381128215 793472630327243012071692323)
        ·
          refine ⟨1190208945490864518107538485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793472630327243012071692323 1190208945490864518107538485)
          ·
            refine ⟨111582088639768548572581733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1190208945490864518107538485 111582088639768548572581733)
            ·
              refine ⟨20921641619956602857359075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111582088639768548572581733 20921641619956602857359075)
              ·
                refine ⟨31382462429934904286038613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20921641619956602857359075 31382462429934904286038613)
                ·
                  refine ⟨367763231600799659602015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31382462429934904286038613 367763231600799659602015)
                  ·
                    rfl

theorem cell23_6445947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 8].length) (baseStart_6445947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445947 prefixEnd_6445947 := by exact prefixLift 6445947
  have htrace : WordTrace (prefixWord ++ tailWord_6445947) baseStart_6445947 baseEnd_6445947 := by
    simpa [prefixWord, tailWord_6445947, baseEnd_6445947] using wordTrace_append hprefix tailTrace_6445947
  have hstable : (prefixWord ++ tailWord_6445947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445947).length < 2 ^ (prefixWord ++ tailWord_6445947).sum := by decide
  have hdescent : baseEnd_6445947 < baseStart_6445947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445951 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 1, 4]
def baseStart_6445951 : Nat := 118140960795 + 6445951 * 2 ^ 59
def prefixEnd_6445951 : Nat := 4983230072969 + 3 ^ 40 * 6445951 * 2
def baseEnd_6445951 : Nat := 1103290379443271640256039

theorem tailTrace_6445951 : CollatzResearch.WordTrace tailWord_6445951 prefixEnd_6445951 1103290379443271640256039 := by
  unfold tailWord_6445951
  simp only [CollatzResearch.WordTrace]
  refine ⟨235103147470427882630313707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156735431646951921753542471 235103147470427882630313707)
  ·
    refine ⟨352654721205641823945470561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235103147470427882630313707 352654721205641823945470561)
    ·
      refine ⟨264491040904231367959102921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352654721205641823945470561 264491040904231367959102921)
      ·
        refine ⟨198368280678173525969327191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264491040904231367959102921 198368280678173525969327191)
        ·
          refine ⟨297552421017260288953990787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198368280678173525969327191 297552421017260288953990787)
          ·
            refine ⟨446328631525890433430986181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297552421017260288953990787 446328631525890433430986181)
            ·
              refine ⟨83686618411104456268309909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 446328631525890433430986181 83686618411104456268309909)
              ·
                refine ⟨3922810238020521387577027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83686618411104456268309909 3922810238020521387577027)
                ·
                  refine ⟨5884215357030782081365541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922810238020521387577027 5884215357030782081365541)
                  ·
                    refine ⟨1103290379443271640256039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884215357030782081365541 1103290379443271640256039)
                    ·
                      rfl

theorem cell23_6445951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 4].length) (baseStart_6445951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445951 prefixEnd_6445951 := by exact prefixLift 6445951
  have htrace : WordTrace (prefixWord ++ tailWord_6445951) baseStart_6445951 baseEnd_6445951 := by
    simpa [prefixWord, tailWord_6445951, baseEnd_6445951] using wordTrace_append hprefix tailTrace_6445951
  have hstable : (prefixWord ++ tailWord_6445951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445951).length < 2 ^ (prefixWord ++ tailWord_6445951).sum := by decide
  have hdescent : baseEnd_6445951 < baseStart_6445951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6445978 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_6445978 : Nat := 118140960795 + 6445978 * 2 ^ 59
def prefixEnd_6445978 : Nat := 4983230072969 + 3 ^ 40 * 6445978 * 2
def baseEnd_6445978 : Nat := 3309885002307486315130493

theorem tailTrace_6445978 : CollatzResearch.WordTrace tailWord_6445978 prefixEnd_6445978 3309885002307486315130493 := by
  unfold tailWord_6445978
  simp only [CollatzResearch.WordTrace]
  refine ⟨58776033060332516560386647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156736088160886710827697725 58776033060332516560386647)
  ·
    refine ⟨88164049590498774840579971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58776033060332516560386647 88164049590498774840579971)
    ·
      refine ⟨132246074385748162260869957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88164049590498774840579971 132246074385748162260869957)
      ·
        refine ⟨24796138947327780423913117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132246074385748162260869957 24796138947327780423913117)
        ·
          refine ⟨9298552105247917658967419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24796138947327780423913117 9298552105247917658967419)
          ·
            refine ⟨13947828157871876488451129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9298552105247917658967419 13947828157871876488451129)
            ·
              refine ⟨10460871118403907366338347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13947828157871876488451129 10460871118403907366338347)
              ·
                refine ⟨15691306677605861049507521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460871118403907366338347 15691306677605861049507521)
                ·
                  refine ⟨11768480008204395787130641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15691306677605861049507521 11768480008204395787130641)
                  ·
                    refine ⟨8826360006153296840347981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11768480008204395787130641 8826360006153296840347981)
                    ·
                      refine ⟨3309885002307486315130493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8826360006153296840347981 3309885002307486315130493)
                      ·
                        rfl

theorem cell23_6445978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_6445978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6445978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6445978 prefixEnd_6445978 := by exact prefixLift 6445978
  have htrace : WordTrace (prefixWord ++ tailWord_6445978) baseStart_6445978 baseEnd_6445978 := by
    simpa [prefixWord, tailWord_6445978, baseEnd_6445978] using wordTrace_append hprefix tailTrace_6445978
  have hstable : (prefixWord ++ tailWord_6445978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6445978).length < 2 ^ (prefixWord ++ tailWord_6445978).sum := by decide
  have hdescent : baseEnd_6445978 < baseStart_6445978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6445978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446029 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6446029 : Nat := 118140960795 + 6446029 * 2 ^ 59
def prefixEnd_6446029 : Nat := 4983230072969 + 3 ^ 40 * 6446029 * 2
def baseEnd_6446029 : Nat := 3309911189820865615592759

theorem tailTrace_6446029 : CollatzResearch.WordTrace tailWord_6446029 prefixEnd_6446029 3309911189820865615592759 := by
  unfold tailWord_6446029
  simp only [CollatzResearch.WordTrace]
  refine ⟨235105992364145301951653141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156737328242763534634435427 235105992364145301951653141)
  ·
    refine ⟨11020593392069311028983741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235105992364145301951653141 11020593392069311028983741)
    ·
      refine ⟨4132722522025991635868903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11020593392069311028983741 4132722522025991635868903)
      ·
        refine ⟨6199083783038987453803355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132722522025991635868903 6199083783038987453803355)
        ·
          refine ⟨9298625674558481180705033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199083783038987453803355 9298625674558481180705033)
          ·
            refine ⟨6973969255918860885528775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9298625674558481180705033 6973969255918860885528775)
            ·
              refine ⟨10460953883878291328293163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973969255918860885528775 10460953883878291328293163)
              ·
                refine ⟨15691430825817436992439745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460953883878291328293163 15691430825817436992439745)
                ·
                  refine ⟨11768573119363077744329809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15691430825817436992439745 11768573119363077744329809)
                  ·
                    refine ⟨8826429839522308308247357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11768573119363077744329809 8826429839522308308247357)
                    ·
                      refine ⟨3309911189820865615592759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8826429839522308308247357 3309911189820865615592759)
                      ·
                        rfl

theorem cell23_6446029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6446029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446029 prefixEnd_6446029 := by exact prefixLift 6446029
  have htrace : WordTrace (prefixWord ++ tailWord_6446029) baseStart_6446029 baseEnd_6446029 := by
    simpa [prefixWord, tailWord_6446029, baseEnd_6446029] using wordTrace_append hprefix tailTrace_6446029
  have hstable : (prefixWord ++ tailWord_6446029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446029).length < 2 ^ (prefixWord ++ tailWord_6446029).sum := by decide
  have hdescent : baseEnd_6446029 < baseStart_6446029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446045 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_6446045 : Nat := 118140960795 + 6446045 * 2 ^ 59
def prefixEnd_6446045 : Nat := 4983230072969 + 3 ^ 40 * 6446045 * 2
def baseEnd_6446045 : Nat := 1103306468503779184330895

theorem tailTrace_6446045 : CollatzResearch.WordTrace tailWord_6446045 prefixEnd_6446045 1103306468503779184330895 := by
  unfold tailWord_6446045
  simp only [CollatzResearch.WordTrace]
  refine ⟨235106575932087336684235589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156737717288058224456157059 235106575932087336684235589)
  ·
    refine ⟨44082482987266375628294173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235106575932087336684235589 44082482987266375628294173)
    ·
      refine ⟨16530931120224890860610315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44082482987266375628294173 16530931120224890860610315)
      ·
        refine ⟨24796396680337336290915473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16530931120224890860610315 24796396680337336290915473)
        ·
          refine ⟨18597297510253002218186605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24796396680337336290915473 18597297510253002218186605)
          ·
            refine ⟨6973986566344875831819977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18597297510253002218186605 6973986566344875831819977)
            ·
              refine ⟨5230489924758656873864983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6973986566344875831819977 5230489924758656873864983)
              ·
                refine ⟨7845734887137985310797475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230489924758656873864983 7845734887137985310797475)
                ·
                  refine ⟨11768602330706977966196213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7845734887137985310797475 11768602330706977966196213)
                  ·
                    refine ⟨1103306468503779184330895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11768602330706977966196213 1103306468503779184330895)
                    ·
                      rfl

theorem cell23_6446045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_6446045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446045 prefixEnd_6446045 := by exact prefixLift 6446045
  have htrace : WordTrace (prefixWord ++ tailWord_6446045) baseStart_6446045 baseEnd_6446045 := by
    simpa [prefixWord, tailWord_6446045, baseEnd_6446045] using wordTrace_append hprefix tailTrace_6446045
  have hstable : (prefixWord ++ tailWord_6446045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446045).length < 2 ^ (prefixWord ++ tailWord_6446045).sum := by decide
  have hdescent : baseEnd_6446045 < baseStart_6446045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446058 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_6446058 : Nat := 118140960795 + 6446058 * 2 ^ 59
def prefixEnd_6446058 : Nat := 4983230072969 + 3 ^ 40 * 6446058 * 2
def baseEnd_6446058 : Nat := 1103308693586615334043375

theorem tailTrace_6446058 : CollatzResearch.WordTrace tailWord_6446058 prefixEnd_6446058 1103308693586615334043375 := by
  unfold tailWord_6446058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58776762520260059976114707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156738033387360159936305885 58776762520260059976114707)
  ·
    refine ⟨88165143780390089964172061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58776762520260059976114707 88165143780390089964172061)
    ·
      refine ⟨33061928917646283736564523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88165143780390089964172061 33061928917646283736564523)
      ·
        refine ⟨49592893376469425604846785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33061928917646283736564523 49592893376469425604846785)
        ·
          refine ⟨37194670032352069203635089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49592893376469425604846785 37194670032352069203635089)
          ·
            refine ⟨27896002524264051902726317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37194670032352069203635089 27896002524264051902726317)
            ·
              refine ⟨10461000946599019463522369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27896002524264051902726317 10461000946599019463522369)
              ·
                refine ⟨7845750709949264597641777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10461000946599019463522369 7845750709949264597641777)
                ·
                  refine ⟨5884313032461948448231333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7845750709949264597641777 5884313032461948448231333)
                  ·
                    refine ⟨1103308693586615334043375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884313032461948448231333 1103308693586615334043375)
                    ·
                      rfl

theorem cell23_6446058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_6446058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446058 prefixEnd_6446058 := by exact prefixLift 6446058
  have htrace : WordTrace (prefixWord ++ tailWord_6446058) baseStart_6446058 baseEnd_6446058 := by
    simpa [prefixWord, tailWord_6446058, baseEnd_6446058] using wordTrace_append hprefix tailTrace_6446058
  have hstable : (prefixWord ++ tailWord_6446058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446058).length < 2 ^ (prefixWord ++ tailWord_6446058).sum := by decide
  have hdescent : baseEnd_6446058 < baseStart_6446058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446065 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 3, 2, 2]
def baseStart_6446065 : Nat := 118140960795 + 6446065 * 2 ^ 59
def prefixEnd_6446065 : Nat := 4983230072969 + 3 ^ 40 * 6446065 * 2
def baseEnd_6446065 : Nat := 3309929675124427474742593

theorem tailTrace_6446065 : CollatzResearch.WordTrace tailWord_6446065 prefixEnd_6446065 3309929675124427474742593 := by
  unfold tailWord_6446065
  simp only [CollatzResearch.WordTrace]
  refine ⟨235107305392014880099963649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156738203594676586733309099 235107305392014880099963649)
  ·
    refine ⟨176330479044011160074972737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235107305392014880099963649 176330479044011160074972737)
    ·
      refine ⟨132247859283008370056229553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176330479044011160074972737 132247859283008370056229553)
      ·
        refine ⟨99185894462256277542172165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132247859283008370056229553 99185894462256277542172165)
        ·
          refine ⟨18597355211673052039157281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99185894462256277542172165 18597355211673052039157281)
          ·
            refine ⟨13948016408754789029367961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18597355211673052039157281 13948016408754789029367961)
            ·
              refine ⟨10461012306566091772025971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13948016408754789029367961 10461012306566091772025971)
              ·
                refine ⟨15691518459849137658038957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10461012306566091772025971 15691518459849137658038957)
                ·
                  refine ⟨5884319422443426621764609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15691518459849137658038957 5884319422443426621764609)
                  ·
                    refine ⟨4413239566832569966323457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5884319422443426621764609 4413239566832569966323457)
                    ·
                      refine ⟨3309929675124427474742593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413239566832569966323457 3309929675124427474742593)
                      ·
                        rfl

theorem cell23_6446065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_6446065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446065 prefixEnd_6446065 := by exact prefixLift 6446065
  have htrace : WordTrace (prefixWord ++ tailWord_6446065) baseStart_6446065 baseEnd_6446065 := by
    simpa [prefixWord, tailWord_6446065, baseEnd_6446065] using wordTrace_append hprefix tailTrace_6446065
  have hstable : (prefixWord ++ tailWord_6446065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446065).length < 2 ^ (prefixWord ++ tailWord_6446065).sum := by decide
  have hdescent : baseEnd_6446065 < baseStart_6446065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446078 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6446078 : Nat := 118140960795 + 6446078 * 2 ^ 59
def prefixEnd_6446078 : Nat := 4983230072969 + 3 ^ 40 * 6446078 * 2
def baseEnd_6446078 : Nat := 3309936350372935923880033

theorem tailTrace_6446078 : CollatzResearch.WordTrace tailWord_6446078 prefixEnd_6446078 3309936350372935923880033 := by
  unfold tailWord_6446078
  simp only [CollatzResearch.WordTrace]
  refine ⟨29388472442620972915023361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156738519693978522213457925 29388472442620972915023361)
  ·
    refine ⟨22041354331965729686267521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29388472442620972915023361 22041354331965729686267521)
    ·
      refine ⟨16531015748974297264700641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22041354331965729686267521 16531015748974297264700641)
      ·
        refine ⟨12398261811730722948525481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16531015748974297264700641 12398261811730722948525481)
        ·
          refine ⟨9298696358798042211394111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12398261811730722948525481 9298696358798042211394111)
          ·
            refine ⟨13948044538197063317091167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9298696358798042211394111 13948044538197063317091167)
            ·
              refine ⟨20922066807295594975636751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13948044538197063317091167 20922066807295594975636751)
              ·
                refine ⟨31383100210943392463455127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20922066807295594975636751 31383100210943392463455127)
                ·
                  refine ⟨47074650316415088695182691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31383100210943392463455127 47074650316415088695182691)
                  ·
                    refine ⟨70611975474622633042774037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47074650316415088695182691 70611975474622633042774037)
                    ·
                      refine ⟨3309936350372935923880033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70611975474622633042774037 3309936350372935923880033)
                      ·
                        rfl

theorem cell23_6446078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6446078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446078 prefixEnd_6446078 := by exact prefixLift 6446078
  have htrace : WordTrace (prefixWord ++ tailWord_6446078) baseStart_6446078 baseEnd_6446078 := by
    simpa [prefixWord, tailWord_6446078, baseEnd_6446078] using wordTrace_append hprefix tailTrace_6446078
  have hstable : (prefixWord ++ tailWord_6446078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446078).length < 2 ^ (prefixWord ++ tailWord_6446078).sum := by decide
  have hdescent : baseEnd_6446078 < baseStart_6446078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446082 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6446082 : Nat := 118140960795 + 6446082 * 2 ^ 59
def prefixEnd_6446082 : Nat := 4983230072969 + 3 ^ 40 * 6446082 * 2
def baseEnd_6446082 : Nat := 3309938404295553908230015

theorem tailTrace_6446082 : CollatzResearch.WordTrace tailWord_6446082 prefixEnd_6446082 3309938404295553908230015 := by
  unfold tailWord_6446082
  simp only [CollatzResearch.WordTrace]
  refine ⟨58776981358238323000833125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156738616955302194668888333 58776981358238323000833125)
  ·
    refine ⟨11020684004669685562656211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58776981358238323000833125 11020684004669685562656211)
    ·
      refine ⟨16531026007004528343984317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11020684004669685562656211 16531026007004528343984317)
      ·
        refine ⟨6199134752626698128994119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16531026007004528343984317 6199134752626698128994119)
        ·
          refine ⟨9298702128940047193491179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199134752626698128994119 9298702128940047193491179)
          ·
            refine ⟨13948053193410070790236769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9298702128940047193491179 13948053193410070790236769)
            ·
              refine ⟨10461039895057553092677577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13948053193410070790236769 10461039895057553092677577)
              ·
                refine ⟨7845779921293164819508183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10461039895057553092677577 7845779921293164819508183)
                ·
                  refine ⟨11768669881939747229262275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7845779921293164819508183 11768669881939747229262275)
                  ·
                    refine ⟨17653004822909620843893413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11768669881939747229262275 17653004822909620843893413)
                    ·
                      refine ⟨3309938404295553908230015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17653004822909620843893413 3309938404295553908230015)
                      ·
                        rfl

theorem cell23_6446082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6446082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446082 prefixEnd_6446082 := by exact prefixLift 6446082
  have htrace : WordTrace (prefixWord ++ tailWord_6446082) baseStart_6446082 baseEnd_6446082 := by
    simpa [prefixWord, tailWord_6446082, baseEnd_6446082] using wordTrace_append hprefix tailTrace_6446082
  have hstable : (prefixWord ++ tailWord_6446082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446082).length < 2 ^ (prefixWord ++ tailWord_6446082).sum := by decide
  have hdescent : baseEnd_6446082 < baseStart_6446082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446124 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_6446124 : Nat := 118140960795 + 6446124 * 2 ^ 59
def prefixEnd_6446124 : Nat := 4983230072969 + 3 ^ 40 * 6446124 * 2
def baseEnd_6446124 : Nat := 3309959970483042743904821

theorem tailTrace_6446124 : CollatzResearch.WordTrace tailWord_6446124 prefixEnd_6446124 3309959970483042743904821 := by
  unfold tailWord_6446124
  simp only [CollatzResearch.WordTrace]
  refine ⟨117554728649400566588180713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156739638199200755450907617 117554728649400566588180713)
  ·
    refine ⟨88166046487050424941135535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117554728649400566588180713 88166046487050424941135535)
    ·
      refine ⟨132249069730575637411703303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88166046487050424941135535 132249069730575637411703303)
      ·
        refine ⟨198373604595863456117554955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132249069730575637411703303 198373604595863456117554955)
        ·
          refine ⟨297560406893795184176332433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198373604595863456117554955 297560406893795184176332433)
          ·
            refine ⟨223170305170346388132249325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297560406893795184176332433 223170305170346388132249325)
            ·
              refine ⟨83688864438879895549593497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223170305170346388132249325 83688864438879895549593497)
              ·
                refine ⟨62766648329159921662195123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83688864438879895549593497 62766648329159921662195123)
                ·
                  refine ⟨94149972493739882493292685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62766648329159921662195123 94149972493739882493292685)
                  ·
                    refine ⟨35306239685152455934984757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94149972493739882493292685 35306239685152455934984757)
                    ·
                      refine ⟨3309959970483042743904821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35306239685152455934984757 3309959970483042743904821)
                      ·
                        rfl

theorem cell23_6446124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_6446124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446124 prefixEnd_6446124 := by exact prefixLift 6446124
  have htrace : WordTrace (prefixWord ++ tailWord_6446124) baseStart_6446124 baseEnd_6446124 := by
    simpa [prefixWord, tailWord_6446124, baseEnd_6446124] using wordTrace_append hprefix tailTrace_6446124
  have hstable : (prefixWord ++ tailWord_6446124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446124).length < 2 ^ (prefixWord ++ tailWord_6446124).sum := by decide
  have hdescent : baseEnd_6446124 < baseStart_6446124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446132 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6446132 : Nat := 118140960795 + 6446132 * 2 ^ 59
def prefixEnd_6446132 : Nat := 4983230072969 + 3 ^ 40 * 6446132 * 2
def baseEnd_6446132 : Nat := 3309964078328278712604785

theorem tailTrace_6446132 : CollatzResearch.WordTrace tailWord_6446132 prefixEnd_6446132 3309964078328278712604785 := by
  unfold tailWord_6446132
  simp only [CollatzResearch.WordTrace]
  refine ⟨117554874541386075271326325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156739832721848100361768433 117554874541386075271326325)
  ·
    refine ⟨11020769488254944556686843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117554874541386075271326325 11020769488254944556686843)
    ·
      refine ⟨16531154232382416835030265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11020769488254944556686843 16531154232382416835030265)
      ·
        refine ⟨12398365674286812626272699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16531154232382416835030265 12398365674286812626272699)
        ·
          refine ⟨18597548511430218939409049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398365674286812626272699 18597548511430218939409049)
          ·
            refine ⟨13948161383572664204556787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18597548511430218939409049 13948161383572664204556787)
            ·
              refine ⟨20922242075358996306835181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13948161383572664204556787 20922242075358996306835181)
              ·
                refine ⟨7845840778259623615063193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20922242075358996306835181 7845840778259623615063193)
                ·
                  refine ⟨5884380583694717711297395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7845840778259623615063193 5884380583694717711297395)
                  ·
                    refine ⟨8826570875542076566946093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5884380583694717711297395 8826570875542076566946093)
                    ·
                      refine ⟨3309964078328278712604785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8826570875542076566946093 3309964078328278712604785)
                      ·
                        rfl

theorem cell23_6446132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6446132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446132 prefixEnd_6446132 := by exact prefixLift 6446132
  have htrace : WordTrace (prefixWord ++ tailWord_6446132) baseStart_6446132 baseEnd_6446132 := by
    simpa [prefixWord, tailWord_6446132, baseEnd_6446132] using wordTrace_append hprefix tailTrace_6446132
  have hstable : (prefixWord ++ tailWord_6446132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446132).length < 2 ^ (prefixWord ++ tailWord_6446132).sum := by decide
  have hdescent : baseEnd_6446132 < baseStart_6446132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446141 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6446141 : Nat := 118140960795 + 6446141 * 2 ^ 59
def prefixEnd_6446141 : Nat := 4983230072969 + 3 ^ 40 * 6446141 * 2
def baseEnd_6446141 : Nat := 3309968699654169177392243

theorem tailTrace_6446141 : CollatzResearch.WordTrace tailWord_6446141 prefixEnd_6446141 3309968699654169177392243 := by
  unfold tailWord_6446141
  simp only [CollatzResearch.WordTrace]
  refine ⟨235110077339739545079730277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156740051559826363386486851 235110077339739545079730277)
  ·
    refine ⟨44083139501201164702449427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235110077339739545079730277 44083139501201164702449427)
    ·
      refine ⟨66124709251801747053674141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44083139501201164702449427 66124709251801747053674141)
      ·
        refine ⟨24796765969425655145127803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66124709251801747053674141 24796765969425655145127803)
        ·
          refine ⟨37195148954138482717691705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24796765969425655145127803 37195148954138482717691705)
          ·
            refine ⟨27896361715603862038268779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37195148954138482717691705 27896361715603862038268779)
            ·
              refine ⟨41844542573405793057403169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27896361715603862038268779 41844542573405793057403169)
              ·
                refine ⟨31383406930054344793052377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41844542573405793057403169 31383406930054344793052377)
                ·
                  refine ⟨23537555197540758594789283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31383406930054344793052377 23537555197540758594789283)
                  ·
                    refine ⟨35306332796311137892183925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23537555197540758594789283 35306332796311137892183925)
                    ·
                      refine ⟨3309968699654169177392243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35306332796311137892183925 3309968699654169177392243)
                      ·
                        rfl

theorem cell23_6446141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6446141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446141 prefixEnd_6446141 := by exact prefixLift 6446141
  have htrace : WordTrace (prefixWord ++ tailWord_6446141) baseStart_6446141 baseEnd_6446141 := by
    simpa [prefixWord, tailWord_6446141, baseEnd_6446141] using wordTrace_append hprefix tailTrace_6446141
  have hstable : (prefixWord ++ tailWord_6446141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446141).length < 2 ^ (prefixWord ++ tailWord_6446141).sum := by decide
  have hdescent : baseEnd_6446141 < baseStart_6446141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446142 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6446142 : Nat := 118140960795 + 6446142 * 2 ^ 59
def prefixEnd_6446142 : Nat := 4983230072969 + 3 ^ 40 * 6446142 * 2
def baseEnd_6446142 : Nat := 3309969213134823673479739

theorem tailTrace_6446142 : CollatzResearch.WordTrace tailWord_6446142 prefixEnd_6446142 3309969213134823673479739 := by
  unfold tailWord_6446142
  simp only [CollatzResearch.WordTrace]
  refine ⟨29388764226591990281314585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156740075875157281500344453 29388764226591990281314585)
  ·
    refine ⟨22041573169943992710985939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29388764226591990281314585 22041573169943992710985939)
    ·
      refine ⟨33062359754915989066478909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22041573169943992710985939 33062359754915989066478909)
      ·
        refine ⟨12398384908093495899929591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33062359754915989066478909 12398384908093495899929591)
        ·
          refine ⟨18597577362140243849894387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398384908093495899929591 18597577362140243849894387)
          ·
            refine ⟨27896366043210365774841581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18597577362140243849894387 27896366043210365774841581)
            ·
              refine ⟨10461137266203887165565593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27896366043210365774841581 10461137266203887165565593)
              ·
                refine ⟨7845852949652915374174195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10461137266203887165565593 7845852949652915374174195)
                ·
                  refine ⟨11768779424479373061261293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7845852949652915374174195 11768779424479373061261293)
                  ·
                    refine ⟨4413292284179764897972985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11768779424479373061261293 4413292284179764897972985)
                    ·
                      refine ⟨3309969213134823673479739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413292284179764897972985 3309969213134823673479739)
                      ·
                        rfl

theorem cell23_6446142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6446142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446142 prefixEnd_6446142 := by exact prefixLift 6446142
  have htrace : WordTrace (prefixWord ++ tailWord_6446142) baseStart_6446142 baseEnd_6446142 := by
    simpa [prefixWord, tailWord_6446142, baseEnd_6446142] using wordTrace_append hprefix tailTrace_6446142
  have hstable : (prefixWord ++ tailWord_6446142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446142).length < 2 ^ (prefixWord ++ tailWord_6446142).sum := by decide
  have hdescent : baseEnd_6446142 < baseStart_6446142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446144 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 9]
def baseStart_6446144 : Nat := 118140960795 + 6446144 * 2 ^ 59
def prefixEnd_6446144 : Nat := 4983230072969 + 3 ^ 40 * 6446144 * 2
def baseEnd_6446144 : Nat := 367774471121792518406081

theorem tailTrace_6446144 : CollatzResearch.WordTrace tailWord_6446144 prefixEnd_6446144 367774471121792518406081 := by
  unfold tailWord_6446144
  simp only [CollatzResearch.WordTrace]
  refine ⟨117555093379364338296044743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156740124505819117728059657 117555093379364338296044743)
  ·
    refine ⟨176332640069046507444067115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117555093379364338296044743 176332640069046507444067115)
    ·
      refine ⟨264498960103569761166100673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176332640069046507444067115 264498960103569761166100673)
      ·
        refine ⟨198374220077677320874575505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264498960103569761166100673 198374220077677320874575505)
        ·
          refine ⟨148780665058257990655931629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198374220077677320874575505 148780665058257990655931629)
          ·
            refine ⟨55792749396846746495974361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148780665058257990655931629 55792749396846746495974361)
            ·
              refine ⟨41844562047635059871980771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55792749396846746495974361 41844562047635059871980771)
              ·
                refine ⟨62766843071452589807971157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41844562047635059871980771 62766843071452589807971157)
                ·
                  refine ⟨367774471121792518406081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62766843071452589807971157 367774471121792518406081)
                  ·
                    rfl

theorem cell23_6446144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_6446144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446144 prefixEnd_6446144 := by exact prefixLift 6446144
  have htrace : WordTrace (prefixWord ++ tailWord_6446144) baseStart_6446144 baseEnd_6446144 := by
    simpa [prefixWord, tailWord_6446144, baseEnd_6446144] using wordTrace_append hprefix tailTrace_6446144
  have hstable : (prefixWord ++ tailWord_6446144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446144).length < 2 ^ (prefixWord ++ tailWord_6446144).sum := by decide
  have hdescent : baseEnd_6446144 < baseStart_6446144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446172 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_6446172 : Nat := 118140960795 + 6446172 * 2 ^ 59
def prefixEnd_6446172 : Nat := 4983230072969 + 3 ^ 40 * 6446172 * 2
def baseEnd_6446172 : Nat := 3309984617554458556104601

theorem tailTrace_6446172 : CollatzResearch.WordTrace tailWord_6446172 prefixEnd_6446172 3309984617554458556104601 := by
  unfold tailWord_6446172
  simp only [CollatzResearch.WordTrace]
  refine ⟨117555604001313618687054385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156740805335084824916072513 117555604001313618687054385)
  ·
    refine ⟨88166703000985214015290789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117555604001313618687054385 88166703000985214015290789)
    ·
      refine ⟨16531256812684727627867023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88166703000985214015290789 16531256812684727627867023)
      ·
        refine ⟨24796885219027091441800535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16531256812684727627867023 24796885219027091441800535)
        ·
          refine ⟨37195327828540637162700803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24796885219027091441800535 37195327828540637162700803)
          ·
            refine ⟨55792991742810955744051205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37195327828540637162700803 55792991742810955744051205)
            ·
              refine ⟨10461185951777054202009601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55792991742810955744051205 10461185951777054202009601)
              ·
                refine ⟨7845889463832790651507201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10461185951777054202009601 7845889463832790651507201)
                ·
                  refine ⟨5884417097874592988630401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7845889463832790651507201 5884417097874592988630401)
                  ·
                    refine ⟨4413312823405944741472801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5884417097874592988630401 4413312823405944741472801)
                    ·
                      refine ⟨3309984617554458556104601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413312823405944741472801 3309984617554458556104601)
                      ·
                        rfl

theorem cell23_6446172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_6446172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446172 prefixEnd_6446172 := by exact prefixLift 6446172
  have htrace : WordTrace (prefixWord ++ tailWord_6446172) baseStart_6446172 baseEnd_6446172 := by
    simpa [prefixWord, tailWord_6446172, baseEnd_6446172] using wordTrace_append hprefix tailTrace_6446172
  have hstable : (prefixWord ++ tailWord_6446172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446172).length < 2 ^ (prefixWord ++ tailWord_6446172).sum := by decide
  have hdescent : baseEnd_6446172 < baseStart_6446172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446211 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4]
def baseStart_6446211 : Nat := 118140960795 + 6446211 * 2 ^ 59
def prefixEnd_6446211 : Nat := 4983230072969 + 3 ^ 40 * 6446211 * 2
def baseEnd_6446211 : Nat := 3310004643299983903516921

theorem tailTrace_6446211 : CollatzResearch.WordTrace tailWord_6446211 prefixEnd_6446211 3310004643299983903516921 := by
  unfold tailWord_6446211
  simp only [CollatzResearch.WordTrace]
  refine ⟨235112630449485947034778487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156741753632990631356518991 235112630449485947034778487)
  ·
    refine ⟨352668945674228920552167731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235112630449485947034778487 352668945674228920552167731)
    ·
      refine ⟨529003418511343380828251597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352668945674228920552167731 529003418511343380828251597)
      ·
        refine ⟨198376281941753767810594349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 529003418511343380828251597 198376281941753767810594349)
        ·
          refine ⟨74391105728157662928972881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198376281941753767810594349 74391105728157662928972881)
          ·
            refine ⟨55793329296118247196729661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74391105728157662928972881 55793329296118247196729661)
            ·
              refine ⟨20922498486044342698773623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55793329296118247196729661 20922498486044342698773623)
              ·
                refine ⟨31383747729066514048160435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20922498486044342698773623 31383747729066514048160435)
                ·
                  refine ⟨47075621593599771072240653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31383747729066514048160435 47075621593599771072240653)
                  ·
                    refine ⟨17653358097599914152090245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47075621593599771072240653 17653358097599914152090245)
                    ·
                      refine ⟨3310004643299983903516921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17653358097599914152090245 3310004643299983903516921)
                      ·
                        rfl

theorem cell23_6446211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_6446211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446211 prefixEnd_6446211 := by exact prefixLift 6446211
  have htrace : WordTrace (prefixWord ++ tailWord_6446211) baseStart_6446211 baseEnd_6446211 := by
    simpa [prefixWord, tailWord_6446211, baseEnd_6446211] using wordTrace_append hprefix tailTrace_6446211
  have hstable : (prefixWord ++ tailWord_6446211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446211).length < 2 ^ (prefixWord ++ tailWord_6446211).sum := by decide
  have hdescent : baseEnd_6446211 < baseStart_6446211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446241 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6446241 : Nat := 118140960795 + 6446241 * 2 ^ 59
def prefixEnd_6446241 : Nat := 4983230072969 + 3 ^ 40 * 6446241 * 2
def baseEnd_6446241 : Nat := 3310020047719618786141783

theorem tailTrace_6446241 : CollatzResearch.WordTrace tailWord_6446241 prefixEnd_6446241 3310020047719618786141783 := by
  unfold tailWord_6446241
  simp only [CollatzResearch.WordTrace]
  refine ⟨235113724639377262158370577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156742483092918174772247051 235113724639377262158370577)
  ·
    refine ⟨176335293479532946618777933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235113724639377262158370577 176335293479532946618777933)
    ·
      refine ⟨66125735054824854982041725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176335293479532946618777933 66125735054824854982041725)
      ·
        refine ⟨24797150645559320618265647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66125735054824854982041725 24797150645559320618265647)
        ·
          refine ⟨37195725968338980927398471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24797150645559320618265647 37195725968338980927398471)
          ·
            refine ⟨55793588952508471391097707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37195725968338980927398471 55793588952508471391097707)
            ·
              refine ⟨83690383428762707086646561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55793588952508471391097707 83690383428762707086646561)
              ·
                refine ⟨62767787571572030314984921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83690383428762707086646561 62767787571572030314984921)
                ·
                  refine ⟨47075840678679022736238691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62767787571572030314984921 47075840678679022736238691)
                  ·
                    refine ⟨70613761018018534104358037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47075840678679022736238691 70613761018018534104358037)
                    ·
                      refine ⟨3310020047719618786141783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70613761018018534104358037 3310020047719618786141783)
                      ·
                        rfl

theorem cell23_6446241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6446241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446241 prefixEnd_6446241 := by exact prefixLift 6446241
  have htrace : WordTrace (prefixWord ++ tailWord_6446241) baseStart_6446241 baseEnd_6446241 := by
    simpa [prefixWord, tailWord_6446241, baseEnd_6446241] using wordTrace_append hprefix tailTrace_6446241
  have hstable : (prefixWord ++ tailWord_6446241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446241).length < 2 ^ (prefixWord ++ tailWord_6446241).sum := by decide
  have hdescent : baseEnd_6446241 < baseStart_6446241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446295 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_6446295 : Nat := 118140960795 + 6446295 * 2 ^ 59
def prefixEnd_6446295 : Nat := 4983230072969 + 3 ^ 40 * 6446295 * 2
def baseEnd_6446295 : Nat := 3310047775674961574866535

theorem tailTrace_6446295 : CollatzResearch.WordTrace tailWord_6446295 prefixEnd_6446295 3310047775674961574866535 := by
  unfold tailWord_6446295
  simp only [CollatzResearch.WordTrace]
  refine ⟨235115694181181629380836339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156743796120787752920557559 235115694181181629380836339)
  ·
    refine ⟨352673541271772444071254509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235115694181181629380836339 352673541271772444071254509)
    ·
      refine ⟨132252577976914666526720441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352673541271772444071254509 132252577976914666526720441)
      ·
        refine ⟨99189433482685999895040331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132252577976914666526720441 99189433482685999895040331)
        ·
          refine ⟨148784150224028999842560497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99189433482685999895040331 148784150224028999842560497)
          ·
            refine ⟨111588112668021749881920373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148784150224028999842560497 111588112668021749881920373)
            ·
              refine ⟨10461385562627039051430035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111588112668021749881920373 10461385562627039051430035)
              ·
                refine ⟨15692078343940558577145053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10461385562627039051430035 15692078343940558577145053)
                ·
                  refine ⟨5884529378977709466429395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15692078343940558577145053 5884529378977709466429395)
                  ·
                    refine ⟨8826794068466564199644093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5884529378977709466429395 8826794068466564199644093)
                    ·
                      refine ⟨3310047775674961574866535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8826794068466564199644093 3310047775674961574866535)
                      ·
                        rfl

theorem cell23_6446295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_6446295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446295 prefixEnd_6446295 := by exact prefixLift 6446295
  have htrace : WordTrace (prefixWord ++ tailWord_6446295) baseStart_6446295 baseEnd_6446295 := by
    simpa [prefixWord, tailWord_6446295, baseEnd_6446295] using wordTrace_append hprefix tailTrace_6446295
  have hstable : (prefixWord ++ tailWord_6446295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446295).length < 2 ^ (prefixWord ++ tailWord_6446295).sum := by decide
  have hdescent : baseEnd_6446295 < baseStart_6446295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446315 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 1, 5]
def baseStart_6446315 : Nat := 118140960795 + 6446315 * 2 ^ 59
def prefixEnd_6446315 : Nat := 4983230072969 + 3 ^ 40 * 6446315 * 2
def baseEnd_6446315 : Nat := 1103352681762683832205481

theorem tailTrace_6446315 : CollatzResearch.WordTrace tailWord_6446315 prefixEnd_6446315 1103352681762683832205481 := by
  unfold tailWord_6446315
  simp only [CollatzResearch.WordTrace]
  refine ⟨235116423641109172796564399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156744282427406115197709599 235116423641109172796564399)
  ·
    refine ⟨352674635461663759194846599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235116423641109172796564399 352674635461663759194846599)
    ·
      refine ⟨529011953192495638792269899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352674635461663759194846599 529011953192495638792269899)
      ·
        refine ⟨793517929788743458188404849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529011953192495638792269899 793517929788743458188404849)
        ·
          refine ⟨595138447341557593641303637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793517929788743458188404849 595138447341557593641303637)
          ·
            refine ⟨6974278679783878050484027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 595138447341557593641303637 6974278679783878050484027)
            ·
              refine ⟨10461418019675817075726041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6974278679783878050484027 10461418019675817075726041)
              ·
                refine ⟨7846063514756862806794531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10461418019675817075726041 7846063514756862806794531)
                ·
                  refine ⟨11769095272135294210191797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846063514756862806794531 11769095272135294210191797)
                  ·
                    refine ⟨1103352681762683832205481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11769095272135294210191797 1103352681762683832205481)
                    ·
                      rfl

theorem cell23_6446315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 5].length) (baseStart_6446315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446315 prefixEnd_6446315 := by exact prefixLift 6446315
  have htrace : WordTrace (prefixWord ++ tailWord_6446315) baseStart_6446315 baseEnd_6446315 := by
    simpa [prefixWord, tailWord_6446315, baseEnd_6446315] using wordTrace_append hprefix tailTrace_6446315
  have hstable : (prefixWord ++ tailWord_6446315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446315).length < 2 ^ (prefixWord ++ tailWord_6446315).sum := by decide
  have hdescent : baseEnd_6446315 < baseStart_6446315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446332 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_6446332 : Nat := 118140960795 + 6446332 * 2 ^ 59
def prefixEnd_6446332 : Nat := 4983230072969 + 3 ^ 40 * 6446332 * 2
def baseEnd_6446332 : Nat := 1103355591486392643367955

theorem tailTrace_6446332 : CollatzResearch.WordTrace tailWord_6446332 prefixEnd_6446332 1103355591486392643367955 := by
  unfold tailWord_6446332
  simp only [CollatzResearch.WordTrace]
  refine ⟨117558521841023792349966625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156744695788031723133288833 117558521841023792349966625)
  ·
    refine ⟨88168891380767844262474969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117558521841023792349966625 88168891380767844262474969)
    ·
      refine ⟨66126668535575883196856227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88168891380767844262474969 66126668535575883196856227)
      ·
        refine ⟨99190002803363824795284341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66126668535575883196856227 99190002803363824795284341)
        ·
          refine ⟨9299062762815358574557907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99190002803363824795284341 9299062762815358574557907)
          ·
            refine ⟨13948594144223037861836861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9299062762815358574557907 13948594144223037861836861)
            ·
              refine ⟨5230722804083639198188823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13948594144223037861836861 5230722804083639198188823)
              ·
                refine ⟨7846084206125458797283235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230722804083639198188823 7846084206125458797283235)
                ·
                  refine ⟨11769126309188188195924853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846084206125458797283235 11769126309188188195924853)
                  ·
                    refine ⟨1103355591486392643367955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11769126309188188195924853 1103355591486392643367955)
                    ·
                      rfl

theorem cell23_6446332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_6446332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446332 prefixEnd_6446332 := by exact prefixLift 6446332
  have htrace : WordTrace (prefixWord ++ tailWord_6446332) baseStart_6446332 baseEnd_6446332 := by
    simpa [prefixWord, tailWord_6446332, baseEnd_6446332] using wordTrace_append hprefix tailTrace_6446332
  have hstable : (prefixWord ++ tailWord_6446332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446332).length < 2 ^ (prefixWord ++ tailWord_6446332).sum := by decide
  have hdescent : baseEnd_6446332 < baseStart_6446332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446345 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 2, 4]
def baseStart_6446345 : Nat := 118140960795 + 6446345 * 2 ^ 59
def prefixEnd_6446345 : Nat := 4983230072969 + 3 ^ 40 * 6446345 * 2
def baseEnd_6446345 : Nat := 1103357816569228793080435

theorem tailTrace_6446345 : CollatzResearch.WordTrace tailWord_6446345 prefixEnd_6446345 1103357816569228793080435 := by
  unfold tailWord_6446345
  simp only [CollatzResearch.WordTrace]
  refine ⟨235117517831000487920156489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156745011887333658613437659 235117517831000487920156489)
  ·
    refine ⟨176338138373250365940117367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235117517831000487920156489 176338138373250365940117367)
    ·
      refine ⟨264507207559875548910176051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176338138373250365940117367 264507207559875548910176051)
      ·
        refine ⟨396760811339813323365264077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264507207559875548910176051 396760811339813323365264077)
        ·
          refine ⟨148785304252429996261974029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396760811339813323365264077 148785304252429996261974029)
          ·
            refine ⟨55794489094661248598240261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148785304252429996261974029 55794489094661248598240261)
            ·
              refine ⟨10461466705248984112170049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55794489094661248598240261 10461466705248984112170049)
              ·
                refine ⟨7846100028936738084127537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10461466705248984112170049 7846100028936738084127537)
                ·
                  refine ⟨5884575021702553563095653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7846100028936738084127537 5884575021702553563095653)
                  ·
                    refine ⟨1103357816569228793080435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884575021702553563095653 1103357816569228793080435)
                    ·
                      rfl

theorem cell23_6446345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_6446345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446345 prefixEnd_6446345 := by exact prefixLift 6446345
  have htrace : WordTrace (prefixWord ++ tailWord_6446345) baseStart_6446345 baseEnd_6446345 := by
    simpa [prefixWord, tailWord_6446345, baseEnd_6446345] using wordTrace_append hprefix tailTrace_6446345
  have hstable : (prefixWord ++ tailWord_6446345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446345).length < 2 ^ (prefixWord ++ tailWord_6446345).sum := by decide
  have hdescent : baseEnd_6446345 < baseStart_6446345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446365 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6446365 : Nat := 118140960795 + 6446365 * 2 ^ 59
def prefixEnd_6446365 : Nat := 4983230072969 + 3 ^ 40 * 6446365 * 2
def baseEnd_6446365 : Nat := 3310083719320776300991213

theorem tailTrace_6446365 : CollatzResearch.WordTrace tailWord_6446365 prefixEnd_6446365 3310083719320776300991213 := by
  unfold tailWord_6446365
  simp only [CollatzResearch.WordTrace]
  refine ⟨235118247290928031335884549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156745498193952020890589699 235118247290928031335884549)
  ·
    refine ⟨44084671367049005875478353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235118247290928031335884549 44084671367049005875478353)
    ·
      refine ⟨33063503525286754406608765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44084671367049005875478353 33063503525286754406608765)
      ·
        refine ⟨12398813821982532902478287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33063503525286754406608765 12398813821982532902478287)
        ·
          refine ⟨18598220732973799353717431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398813821982532902478287 18598220732973799353717431)
          ·
            refine ⟨27897331099460699030576147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18598220732973799353717431 27897331099460699030576147)
            ·
              refine ⟨41845996649191048545864221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27897331099460699030576147 41845996649191048545864221)
              ·
                refine ⟨15692248743446643204699083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41845996649191048545864221 15692248743446643204699083)
                ·
                  refine ⟨23538373115169964807048625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15692248743446643204699083 23538373115169964807048625)
                  ·
                    refine ⟨17653779836377473605286469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23538373115169964807048625 17653779836377473605286469)
                    ·
                      refine ⟨3310083719320776300991213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17653779836377473605286469 3310083719320776300991213)
                      ·
                        rfl

theorem cell23_6446365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6446365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446365 prefixEnd_6446365 := by exact prefixLift 6446365
  have htrace : WordTrace (prefixWord ++ tailWord_6446365) baseStart_6446365 baseEnd_6446365 := by
    simpa [prefixWord, tailWord_6446365, baseEnd_6446365] using wordTrace_append hprefix tailTrace_6446365
  have hstable : (prefixWord ++ tailWord_6446365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446365).length < 2 ^ (prefixWord ++ tailWord_6446365).sum := by decide
  have hdescent : baseEnd_6446365 < baseStart_6446365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446385 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_6446385 : Nat := 118140960795 + 6446385 * 2 ^ 59
def prefixEnd_6446385 : Nat := 4983230072969 + 3 ^ 40 * 6446385 * 2
def baseEnd_6446385 : Nat := 3310093988933866222741121

theorem tailTrace_6446385 : CollatzResearch.WordTrace tailWord_6446385 prefixEnd_6446385 3310093988933866222741121 := by
  unfold tailWord_6446385
  simp only [CollatzResearch.WordTrace]
  refine ⟨235118976750855574751612609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156745984500570383167741739 235118976750855574751612609)
  ·
    refine ⟨176339232563141681063709457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235118976750855574751612609 176339232563141681063709457)
    ·
      refine ⟨132254424422356260797782093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176339232563141681063709457 132254424422356260797782093)
      ·
        refine ⟨49595409158383597799168285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132254424422356260797782093 49595409158383597799168285)
        ·
          refine ⟨18598278434393849174688107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49595409158383597799168285 18598278434393849174688107)
          ·
            refine ⟨27897417651590773762032161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18598278434393849174688107 27897417651590773762032161)
            ·
              refine ⟨20923063238693080321524121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27897417651590773762032161 20923063238693080321524121)
              ·
                refine ⟨15692297429019810241143091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20923063238693080321524121 15692297429019810241143091)
                ·
                  refine ⟨23538446143529715361714637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15692297429019810241143091 23538446143529715361714637)
                  ·
                    refine ⟨8826917303823643260642989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23538446143529715361714637 8826917303823643260642989)
                    ·
                      refine ⟨3310093988933866222741121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8826917303823643260642989 3310093988933866222741121)
                      ·
                        rfl

theorem cell23_6446385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_6446385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446385 prefixEnd_6446385 := by exact prefixLift 6446385
  have htrace : WordTrace (prefixWord ++ tailWord_6446385) baseStart_6446385 baseEnd_6446385 := by
    simpa [prefixWord, tailWord_6446385, baseEnd_6446385] using wordTrace_append hprefix tailTrace_6446385
  have hstable : (prefixWord ++ tailWord_6446385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446385).length < 2 ^ (prefixWord ++ tailWord_6446385).sum := by decide
  have hdescent : baseEnd_6446385 < baseStart_6446385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446386 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_6446386 : Nat := 118140960795 + 6446386 * 2 ^ 59
def prefixEnd_6446386 : Nat := 4983230072969 + 3 ^ 40 * 6446386 * 2
def baseEnd_6446386 : Nat := 3310094502414520718828617

theorem tailTrace_6446386 : CollatzResearch.WordTrace tailWord_6446386 prefixEnd_6446386 3310094502414520718828617 := by
  unfold tailWord_6446386
  simp only [CollatzResearch.WordTrace]
  refine ⟨58779753305962987980599753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156746008815901301281599341 58779753305962987980599753)
  ·
    refine ⟨44084814979472240985449815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58779753305962987980599753 44084814979472240985449815)
    ·
      refine ⟨66127222469208361478174723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44084814979472240985449815 66127222469208361478174723)
      ·
        refine ⟨99190833703812542217262085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66127222469208361478174723 99190833703812542217262085)
        ·
          refine ⟨18598281319464851665736641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99190833703812542217262085 18598281319464851665736641)
          ·
            refine ⟨13948710989598638749302481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18598281319464851665736641 13948710989598638749302481)
            ·
              refine ⟨10461533242198979061976861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13948710989598638749302481 10461533242198979061976861)
              ·
                refine ⟨3923074965824617148241323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10461533242198979061976861 3923074965824617148241323)
                ·
                  refine ⟨5884612448736925722361985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923074965824617148241323 5884612448736925722361985)
                  ·
                    refine ⟨4413459336552694291771489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5884612448736925722361985 4413459336552694291771489)
                    ·
                      refine ⟨3310094502414520718828617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413459336552694291771489 3310094502414520718828617)
                      ·
                        rfl

theorem cell23_6446386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_6446386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446386 prefixEnd_6446386 := by exact prefixLift 6446386
  have htrace : WordTrace (prefixWord ++ tailWord_6446386) baseStart_6446386 baseEnd_6446386 := by
    simpa [prefixWord, tailWord_6446386, baseEnd_6446386] using wordTrace_append hprefix tailTrace_6446386
  have hstable : (prefixWord ++ tailWord_6446386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446386).length < 2 ^ (prefixWord ++ tailWord_6446386).sum := by decide
  have hdescent : baseEnd_6446386 < baseStart_6446386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446389 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_6446389 : Nat := 118140960795 + 6446389 * 2 ^ 59
def prefixEnd_6446389 : Nat := 4983230072969 + 3 ^ 40 * 6446389 * 2
def baseEnd_6446389 : Nat := 3310096042856484207091103

theorem tailTrace_6446389 : CollatzResearch.WordTrace tailWord_6446389 prefixEnd_6446389 3310096042856484207091103 := by
  unfold tailWord_6446389
  simp only [CollatzResearch.WordTrace]
  refine ⟨235119122642841083434758221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156746081761894055623172147 235119122642841083434758221)
  ·
    refine ⟨88169670991065406288034333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235119122642841083434758221 88169670991065406288034333)
    ·
      refine ⟨33063626621649527358012875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88169670991065406288034333 33063626621649527358012875)
      ·
        refine ⟨49595439932474291037019313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33063626621649527358012875 49595439932474291037019313)
        ·
          refine ⟨37196579949355718277764485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49595439932474291037019313 37196579949355718277764485)
          ·
            refine ⟨6974358740504197177080841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37196579949355718277764485 6974358740504197177080841)
            ·
              refine ⟨5230769055378147882810631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6974358740504197177080841 5230769055378147882810631)
              ·
                refine ⟨7846153583067221824215947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230769055378147882810631 7846153583067221824215947)
                ·
                  refine ⟨11769230374600832736323921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846153583067221824215947 11769230374600832736323921)
                  ·
                    refine ⟨8826922780950624552242941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11769230374600832736323921 8826922780950624552242941)
                    ·
                      refine ⟨3310096042856484207091103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8826922780950624552242941 3310096042856484207091103)
                      ·
                        rfl

theorem cell23_6446389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_6446389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446389 prefixEnd_6446389 := by exact prefixLift 6446389
  have htrace : WordTrace (prefixWord ++ tailWord_6446389) baseStart_6446389 baseEnd_6446389 := by
    simpa [prefixWord, tailWord_6446389, baseEnd_6446389] using wordTrace_append hprefix tailTrace_6446389
  have hstable : (prefixWord ++ tailWord_6446389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446389).length < 2 ^ (prefixWord ++ tailWord_6446389).sum := by decide
  have hdescent : baseEnd_6446389 < baseStart_6446389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446445 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6446445 : Nat := 118140960795 + 6446445 * 2 ^ 59
def prefixEnd_6446445 : Nat := 4983230072969 + 3 ^ 40 * 6446445 * 2
def baseEnd_6446445 : Nat := 3310124797773135987990845

theorem tailTrace_6446445 : CollatzResearch.WordTrace tailWord_6446445 prefixEnd_6446445 3310124797773135987990845 := by
  unfold tailWord_6446445
  simp only [CollatzResearch.WordTrace]
  refine ⟨235121165130638204998796789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156747443420425469999197859 235121165130638204998796789)
  ·
    refine ⟨22042609230997331718637199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235121165130638204998796789 22042609230997331718637199)
    ·
      refine ⟨33063913846495997577955799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22042609230997331718637199 33063913846495997577955799)
      ·
        refine ⟨49595870769743996366933699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33063913846495997577955799 49595870769743996366933699)
        ·
          refine ⟨74393806154615994550400549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49595870769743996366933699 74393806154615994550400549)
          ·
            refine ⟨13948838653990498978200103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74393806154615994550400549 13948838653990498978200103)
            ·
              refine ⟨20923257980985748467300155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13948838653990498978200103 20923257980985748467300155)
              ·
                refine ⟨31384886971478622700950233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20923257980985748467300155 31384886971478622700950233)
                ·
                  refine ⟨23538665228608967025712675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31384886971478622700950233 23538665228608967025712675)
                  ·
                    refine ⟨35307997842913450538569013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23538665228608967025712675 35307997842913450538569013)
                    ·
                      refine ⟨3310124797773135987990845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35307997842913450538569013 3310124797773135987990845)
                      ·
                        rfl

theorem cell23_6446445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6446445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446445 prefixEnd_6446445 := by exact prefixLift 6446445
  have htrace : WordTrace (prefixWord ++ tailWord_6446445) baseStart_6446445 baseEnd_6446445 := by
    simpa [prefixWord, tailWord_6446445, baseEnd_6446445] using wordTrace_append hprefix tailTrace_6446445
  have hstable : (prefixWord ++ tailWord_6446445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446445).length < 2 ^ (prefixWord ++ tailWord_6446445).sum := by decide
  have hdescent : baseEnd_6446445 < baseStart_6446445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446495 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 2, 5]
def baseStart_6446495 : Nat := 118140960795 + 6446495 * 2 ^ 59
def prefixEnd_6446495 : Nat := 4983230072969 + 3 ^ 40 * 6446495 * 2
def baseEnd_6446495 : Nat := 1103383490601953597455205

theorem tailTrace_6446495 : CollatzResearch.WordTrace tailWord_6446495 prefixEnd_6446495 1103383490601953597455205 := by
  unfold tailWord_6446495
  simp only [CollatzResearch.WordTrace]
  refine ⟨235122988780457063538116939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156748659186971375692077959 235122988780457063538116939)
  ·
    refine ⟨352684483170685595307175409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235122988780457063538116939 352684483170685595307175409)
    ·
      refine ⟨264513362378014196480381557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352684483170685595307175409 264513362378014196480381557)
      ·
        refine ⟨24798127722938830920035771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264513362378014196480381557 24798127722938830920035771)
        ·
          refine ⟨37197191584408246380053657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24798127722938830920035771 37197191584408246380053657)
          ·
            refine ⟨27897893688306184785040243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37197191584408246380053657 27897893688306184785040243)
            ·
              refine ⟨41846840532459277177560365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27897893688306184785040243 41846840532459277177560365)
              ·
                refine ⟨15692565199672228941585137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41846840532459277177560365 15692565199672228941585137)
                ·
                  refine ⟨11769423899754171706188853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15692565199672228941585137 11769423899754171706188853)
                  ·
                    refine ⟨1103383490601953597455205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11769423899754171706188853 1103383490601953597455205)
                    ·
                      rfl

theorem cell23_6446495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_6446495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446495 prefixEnd_6446495 := by exact prefixLift 6446495
  have htrace : WordTrace (prefixWord ++ tailWord_6446495) baseStart_6446495 baseEnd_6446495 := by
    simpa [prefixWord, tailWord_6446495, baseEnd_6446495] using wordTrace_append hprefix tailTrace_6446495
  have hstable : (prefixWord ++ tailWord_6446495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446495).length < 2 ^ (prefixWord ++ tailWord_6446495).sum := by decide
  have hdescent : baseEnd_6446495 < baseStart_6446495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446515 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 6, 2]
def baseStart_6446515 : Nat := 118140960795 + 6446515 * 2 ^ 59
def prefixEnd_6446515 : Nat := 4983230072969 + 3 ^ 40 * 6446515 * 2
def baseEnd_6446515 : Nat := 3310160741418950714115523

theorem tailTrace_6446515 : CollatzResearch.WordTrace tailWord_6446515 prefixEnd_6446515 3310160741418950714115523 := by
  unfold tailWord_6446515
  simp only [CollatzResearch.WordTrace]
  refine ⟨235123718240384606953844999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156749145493589737969229999 235123718240384606953844999)
  ·
    refine ⟨352685577360576910430767499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235123718240384606953844999 352685577360576910430767499)
    ·
      refine ⟨529028366040865365646151249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352685577360576910430767499 529028366040865365646151249)
      ·
        refine ⟨396771274530649024234613437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529028366040865365646151249 396771274530649024234613437)
        ·
          refine ⟨148789227948993384087980039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396771274530649024234613437 148789227948993384087980039)
          ·
            refine ⟨223183841923490076131970059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148789227948993384087980039 223183841923490076131970059)
            ·
              refine ⟨334775762885235114197955089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223183841923490076131970059 334775762885235114197955089)
              ·
                refine ⟨251081822163926335648466317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334775762885235114197955089 251081822163926335648466317)
                ·
                  refine ⟨94155683311472375868174869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251081822163926335648466317 94155683311472375868174869)
                  ·
                    refine ⟨4413547655225267618820697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94155683311472375868174869 4413547655225267618820697)
                    ·
                      refine ⟨3310160741418950714115523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413547655225267618820697 3310160741418950714115523)
                      ·
                        rfl

theorem cell23_6446515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6, 2].length) (baseStart_6446515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446515 prefixEnd_6446515 := by exact prefixLift 6446515
  have htrace : WordTrace (prefixWord ++ tailWord_6446515) baseStart_6446515 baseEnd_6446515 := by
    simpa [prefixWord, tailWord_6446515, baseEnd_6446515] using wordTrace_append hprefix tailTrace_6446515
  have hstable : (prefixWord ++ tailWord_6446515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446515).length < 2 ^ (prefixWord ++ tailWord_6446515).sum := by decide
  have hdescent : baseEnd_6446515 < baseStart_6446515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446535 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_6446535 : Nat := 118140960795 + 6446535 * 2 ^ 59
def prefixEnd_6446535 : Nat := 4983230072969 + 3 ^ 40 * 6446535 * 2
def baseEnd_6446535 : Nat := 3310171011032040635865431

theorem tailTrace_6446535 : CollatzResearch.WordTrace tailWord_6446535 prefixEnd_6446535 3310171011032040635865431 := by
  unfold tailWord_6446535
  simp only [CollatzResearch.WordTrace]
  refine ⟨235124447700312150369573059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156749631800208100246382039 235124447700312150369573059)
  ·
    refine ⟨352686671550468225554359589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235124447700312150369573059 352686671550468225554359589)
    ·
      refine ⟨66128750915712792291442423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352686671550468225554359589 66128750915712792291442423)
      ·
        refine ⟨99193126373569188437163635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66128750915712792291442423 99193126373569188437163635)
        ·
          refine ⟨148789689560353782655745453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99193126373569188437163635 148789689560353782655745453)
          ·
            refine ⟨55796133585132668495904545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148789689560353782655745453 55796133585132668495904545)
            ·
              refine ⟨41847100188849501371928409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55796133585132668495904545 41847100188849501371928409)
              ·
                refine ⟨31385325141637126028946307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41847100188849501371928409 31385325141637126028946307)
                ·
                  refine ⟨47077987712455689043419461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31385325141637126028946307 47077987712455689043419461)
                  ·
                    refine ⟨8827122696085441695641149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47077987712455689043419461 8827122696085441695641149)
                    ·
                      refine ⟨3310171011032040635865431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827122696085441695641149 3310171011032040635865431)
                      ·
                        rfl

theorem cell23_6446535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_6446535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446535 prefixEnd_6446535 := by exact prefixLift 6446535
  have htrace : WordTrace (prefixWord ++ tailWord_6446535) baseStart_6446535 baseEnd_6446535 := by
    simpa [prefixWord, tailWord_6446535, baseEnd_6446535] using wordTrace_append hprefix tailTrace_6446535
  have hstable : (prefixWord ++ tailWord_6446535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446535).length < 2 ^ (prefixWord ++ tailWord_6446535).sum := by decide
  have hdescent : baseEnd_6446535 < baseStart_6446535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446552 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_6446552 : Nat := 118140960795 + 6446552 * 2 ^ 59
def prefixEnd_6446552 : Nat := 4983230072969 + 3 ^ 40 * 6446552 * 2
def baseEnd_6446552 : Nat := 3310179740203167069352853

theorem tailTrace_6446552 : CollatzResearch.WordTrace tailWord_6446552 prefixEnd_6446552 3310179740203167069352853 := by
  unfold tailWord_6446552
  simp only [CollatzResearch.WordTrace]
  refine ⟨117562533870625281136470955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156750045160833708181961273 117562533870625281136470955)
  ·
    refine ⟨176343800805937921704706433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117562533870625281136470955 176343800805937921704706433)
    ·
      refine ⟨132257850604453441278529825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176343800805937921704706433 132257850604453441278529825)
      ·
        refine ⟨99193387953340080958897369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132257850604453441278529825 99193387953340080958897369)
        ·
          refine ⟨74395040965005060719173027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99193387953340080958897369 74395040965005060719173027)
          ·
            refine ⟨111592561447507591078759541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74395040965005060719173027 111592561447507591078759541)
            ·
              refine ⟨10461802635703836663633707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111592561447507591078759541 10461802635703836663633707)
              ·
                refine ⟨15692703953555754995450561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10461802635703836663633707 15692703953555754995450561)
                ·
                  refine ⟨11769527965166816246587921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15692703953555754995450561 11769527965166816246587921)
                  ·
                    refine ⟨8827145973875112184940941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11769527965166816246587921 8827145973875112184940941)
                    ·
                      refine ⟨3310179740203167069352853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827145973875112184940941 3310179740203167069352853)
                      ·
                        rfl

theorem cell23_6446552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_6446552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446552 prefixEnd_6446552 := by exact prefixLift 6446552
  have htrace : WordTrace (prefixWord ++ tailWord_6446552) baseStart_6446552 baseEnd_6446552 := by
    simpa [prefixWord, tailWord_6446552, baseEnd_6446552] using wordTrace_append hprefix tailTrace_6446552
  have hstable : (prefixWord ++ tailWord_6446552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446552).length < 2 ^ (prefixWord ++ tailWord_6446552).sum := by decide
  have hdescent : baseEnd_6446552 < baseStart_6446552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446559 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 1, 4]
def baseStart_6446559 : Nat := 118140960795 + 6446559 * 2 ^ 59
def prefixEnd_6446559 : Nat := 4983230072969 + 3 ^ 40 * 6446559 * 2
def baseEnd_6446559 : Nat := 1103394444855916180655107

theorem tailTrace_6446559 : CollatzResearch.WordTrace tailWord_6446559 prefixEnd_6446559 1103394444855916180655107 := by
  unfold tailWord_6446559
  simp only [CollatzResearch.WordTrace]
  refine ⟨235125323052225202468446731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156750215368150134978964487 235125323052225202468446731)
  ·
    refine ⟨352687984578337803702670097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235125323052225202468446731 352687984578337803702670097)
    ·
      refine ⟨264515988433753352777002573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352687984578337803702670097 264515988433753352777002573)
      ·
        refine ⟨99193495662657507291375965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264515988433753352777002573 99193495662657507291375965)
        ·
          refine ⟨37197560873496565234265987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99193495662657507291375965 37197560873496565234265987)
          ·
            refine ⟨55796341310244847851398981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37197560873496565234265987 55796341310244847851398981)
            ·
              refine ⟨10461813995670908972137309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55796341310244847851398981 10461813995670908972137309)
              ·
                refine ⟨3923180248376590864551491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10461813995670908972137309 3923180248376590864551491)
                ·
                  refine ⟨5884770372564886296827237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923180248376590864551491 5884770372564886296827237)
                  ·
                    refine ⟨1103394444855916180655107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884770372564886296827237 1103394444855916180655107)
                    ·
                      rfl

theorem cell23_6446559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 4].length) (baseStart_6446559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446559 prefixEnd_6446559 := by exact prefixLift 6446559
  have htrace : WordTrace (prefixWord ++ tailWord_6446559) baseStart_6446559 baseEnd_6446559 := by
    simpa [prefixWord, tailWord_6446559, baseEnd_6446559] using wordTrace_append hprefix tailTrace_6446559
  have hstable : (prefixWord ++ tailWord_6446559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446559).length < 2 ^ (prefixWord ++ tailWord_6446559).sum := by decide
  have hdescent : baseEnd_6446559 < baseStart_6446559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446599 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_6446599 : Nat := 118140960795 + 6446599 * 2 ^ 59
def prefixEnd_6446599 : Nat := 4983230072969 + 3 ^ 40 * 6446599 * 2
def baseEnd_6446599 : Nat := 3310203873793928385465137

theorem tailTrace_6446599 : CollatzResearch.WordTrace tailWord_6446599 prefixEnd_6446599 3310203873793928385465137 := by
  unfold tailWord_6446599
  simp only [CollatzResearch.WordTrace]
  refine ⟨235126781972080289299902851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156751187981386859533268567 235126781972080289299902851)
  ·
    refine ⟨352690172958120433949854277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235126781972080289299902851 352690172958120433949854277)
    ·
      refine ⟨66129407429647581365597677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352690172958120433949854277 66129407429647581365597677)
      ·
        refine ⟨24798527786117843012099129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66129407429647581365597677 24798527786117843012099129)
        ·
          refine ⟨18598895839588382259074347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24798527786117843012099129 18598895839588382259074347)
          ·
            refine ⟨27898343759382573388611521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18598895839588382259074347 27898343759382573388611521)
            ·
              refine ⟨20923757819536930041458641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27898343759382573388611521 20923757819536930041458641)
              ·
                refine ⟨15692818364652697531093981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20923757819536930041458641 15692818364652697531093981)
                ·
                  refine ⟨5884806886744761574160243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15692818364652697531093981 5884806886744761574160243)
                  ·
                    refine ⟨8827210330117142361240365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5884806886744761574160243 8827210330117142361240365)
                    ·
                      refine ⟨3310203873793928385465137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827210330117142361240365 3310203873793928385465137)
                      ·
                        rfl

theorem cell23_6446599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_6446599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446599 prefixEnd_6446599 := by exact prefixLift 6446599
  have htrace : WordTrace (prefixWord ++ tailWord_6446599) baseStart_6446599 baseEnd_6446599 := by
    simpa [prefixWord, tailWord_6446599, baseEnd_6446599] using wordTrace_append hprefix tailTrace_6446599
  have hstable : (prefixWord ++ tailWord_6446599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446599).length < 2 ^ (prefixWord ++ tailWord_6446599).sum := by decide
  have hdescent : baseEnd_6446599 < baseStart_6446599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446602 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_6446602 : Nat := 118140960795 + 6446602 * 2 ^ 59
def prefixEnd_6446602 : Nat := 4983230072969 + 3 ^ 40 * 6446602 * 2
def baseEnd_6446602 : Nat := 1103401804745297291242541

theorem tailTrace_6446602 : CollatzResearch.WordTrace tailWord_6446602 prefixEnd_6446602 1103401804745297291242541 := by
  unfold tailWord_6446602
  simp only [CollatzResearch.WordTrace]
  refine ⟨58781722847767355203065515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156751260927379613874841373 58781722847767355203065515)
  ·
    refine ⟨88172584271651032804598273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58781722847767355203065515 88172584271651032804598273)
    ·
      refine ⟨66129438203738274603448705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88172584271651032804598273 66129438203738274603448705)
      ·
        refine ⟨49597078652803705952586529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66129438203738274603448705 49597078652803705952586529)
        ·
          refine ⟨37197808989602779464439897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49597078652803705952586529 37197808989602779464439897)
          ·
            refine ⟨27898356742202084598329923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37197808989602779464439897 27898356742202084598329923)
            ·
              refine ⟨41847535113303126897494885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27898356742202084598329923 41847535113303126897494885)
              ·
                refine ⟨7846412833744336293280291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41847535113303126897494885 7846412833744336293280291)
                ·
                  refine ⟨11769619250616504439920437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846412833744336293280291 11769619250616504439920437)
                  ·
                    refine ⟨1103401804745297291242541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11769619250616504439920437 1103401804745297291242541)
                    ·
                      rfl

theorem cell23_6446602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_6446602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446602 prefixEnd_6446602 := by exact prefixLift 6446602
  have htrace : WordTrace (prefixWord ++ tailWord_6446602) baseStart_6446602 baseEnd_6446602 := by
    simpa [prefixWord, tailWord_6446602, baseEnd_6446602] using wordTrace_append hprefix tailTrace_6446602
  have hstable : (prefixWord ++ tailWord_6446602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446602).length < 2 ^ (prefixWord ++ tailWord_6446602).sum := by decide
  have hdescent : baseEnd_6446602 < baseStart_6446602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446642 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_6446642 : Nat := 118140960795 + 6446642 * 2 ^ 59
def prefixEnd_6446642 : Nat := 4983230072969 + 3 ^ 40 * 6446642 * 2
def baseEnd_6446642 : Nat := 3310225953462071717227439

theorem tailTrace_6446642 : CollatzResearch.WordTrace tailWord_6446642 prefixEnd_6446642 3310225953462071717227439 := by
  unfold tailWord_6446642
  simp only [CollatzResearch.WordTrace]
  refine ⟨58782087577731126910929545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156752233540616338429145453 58782087577731126910929545)
  ·
    refine ⟨44086565683298345183197159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58782087577731126910929545 44086565683298345183197159)
    ·
      refine ⟨66129848524947517774795739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44086565683298345183197159 66129848524947517774795739)
      ·
        refine ⟨99194772787421276662193609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66129848524947517774795739 99194772787421276662193609)
        ·
          refine ⟨74396079590565957496645207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99194772787421276662193609 74396079590565957496645207)
          ·
            refine ⟨111594119385848936244967811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74396079590565957496645207 111594119385848936244967811)
            ·
              refine ⟨167391179078773404367451717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111594119385848936244967811 167391179078773404367451717)
              ·
                refine ⟨31385846077270013318897197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167391179078773404367451717 31385846077270013318897197)
                ·
                  refine ⟨11769692278976254994586449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31385846077270013318897197 11769692278976254994586449)
                  ·
                    refine ⟨8827269209232191245939837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11769692278976254994586449 8827269209232191245939837)
                    ·
                      refine ⟨3310225953462071717227439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827269209232191245939837 3310225953462071717227439)
                      ·
                        rfl

theorem cell23_6446642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_6446642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446642 prefixEnd_6446642 := by exact prefixLift 6446642
  have htrace : WordTrace (prefixWord ++ tailWord_6446642) baseStart_6446642 baseEnd_6446642 := by
    simpa [prefixWord, tailWord_6446642, baseEnd_6446642] using wordTrace_append hprefix tailTrace_6446642
  have hstable : (prefixWord ++ tailWord_6446642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446642).length < 2 ^ (prefixWord ++ tailWord_6446642).sum := by decide
  have hdescent : baseEnd_6446642 < baseStart_6446642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446645 : List Nat := [1, 3, 3, 1, 1, 3, 1, 10]
def baseStart_6446645 : Nat := 118140960795 + 6446645 * 2 ^ 59
def prefixEnd_6446645 : Nat := 4983230072969 + 3 ^ 40 * 6446645 * 2
def baseEnd_6446645 : Nat := 122601018292742044647775

theorem tailTrace_6446645 : CollatzResearch.WordTrace tailWord_6446645 prefixEnd_6446645 122601018292742044647775 := by
  unfold tailWord_6446645
  simp only [CollatzResearch.WordTrace]
  refine ⟨235128459729913639156077389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156752306486609092770718259 235128459729913639156077389)
  ·
    refine ⟨88173172398717614683529021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235128459729913639156077389 88173172398717614683529021)
    ·
      refine ⟨33064939649519105506323383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88173172398717614683529021 33064939649519105506323383)
      ·
        refine ⟨49597409474278658259485075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33064939649519105506323383 49597409474278658259485075)
        ·
          refine ⟨74396114211417987389227613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49597409474278658259485075 74396114211417987389227613)
          ·
            refine ⟨27898542829281745270960355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74396114211417987389227613 27898542829281745270960355)
            ·
              refine ⟨41847814243922617906440533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27898542829281745270960355 41847814243922617906440533)
              ·
                refine ⟨122601018292742044647775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41847814243922617906440533 122601018292742044647775)
                ·
                  rfl

theorem cell23_6446645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 10].length) (baseStart_6446645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446645 prefixEnd_6446645 := by exact prefixLift 6446645
  have htrace : WordTrace (prefixWord ++ tailWord_6446645) baseStart_6446645 baseEnd_6446645 := by
    simpa [prefixWord, tailWord_6446645, baseEnd_6446645] using wordTrace_append hprefix tailTrace_6446645
  have hstable : (prefixWord ++ tailWord_6446645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446645).length < 2 ^ (prefixWord ++ tailWord_6446645).sum := by decide
  have hdescent : baseEnd_6446645 < baseStart_6446645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446649 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 2, 4]
def baseStart_6446649 : Nat := 118140960795 + 6446649 * 2 ^ 59
def prefixEnd_6446649 : Nat := 4983230072969 + 3 ^ 40 * 6446649 * 2
def baseEnd_6446649 : Nat := 1103409849275551063279969

theorem tailTrace_6446649 : CollatzResearch.WordTrace tailWord_6446649 prefixEnd_6446649 1103409849275551063279969 := by
  unfold tailWord_6446649
  simp only [CollatzResearch.WordTrace]
  refine ⟨235128605621899147839223001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156752403747932765226148667 235128605621899147839223001)
  ·
    refine ⟨176346454216424360879417251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235128605621899147839223001 176346454216424360879417251)
    ·
      refine ⟨264519681324636541319125877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176346454216424360879417251 264519681324636541319125877)
      ·
        refine ⟨24798720124184675748668051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264519681324636541319125877 24798720124184675748668051)
        ·
          refine ⟨37198080186277013623002077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24798720124184675748668051 37198080186277013623002077)
          ·
            refine ⟨13949280069853880108625779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37198080186277013623002077 13949280069853880108625779)
            ·
              refine ⟨20923920104780820162938669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13949280069853880108625779 20923920104780820162938669)
              ·
                refine ⟨7846470039292807561102001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20923920104780820162938669 7846470039292807561102001)
                ·
                  refine ⟨5884852529469605670826501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7846470039292807561102001 5884852529469605670826501)
                  ·
                    refine ⟨1103409849275551063279969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5884852529469605670826501 1103409849275551063279969)
                    ·
                      rfl

theorem cell23_6446649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_6446649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446649 prefixEnd_6446649 := by exact prefixLift 6446649
  have htrace : WordTrace (prefixWord ++ tailWord_6446649) baseStart_6446649 baseEnd_6446649 := by
    simpa [prefixWord, tailWord_6446649, baseEnd_6446649] using wordTrace_append hprefix tailTrace_6446649
  have hstable : (prefixWord ++ tailWord_6446649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446649).length < 2 ^ (prefixWord ++ tailWord_6446649).sum := by decide
  have hdescent : baseEnd_6446649 < baseStart_6446649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446672 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_6446672 : Nat := 118140960795 + 6446672 * 2 ^ 59
def prefixEnd_6446672 : Nat := 4983230072969 + 3 ^ 40 * 6446672 * 2
def baseEnd_6446672 : Nat := 3310241357881706599852301

theorem tailTrace_6446672 : CollatzResearch.WordTrace tailWord_6446672 prefixEnd_6446672 3310241357881706599852301 := by
  unfold tailWord_6446672
  simp only [CollatzResearch.WordTrace]
  refine ⟨117564722250407911383655135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156752963000543881844873513 117564722250407911383655135)
  ·
    refine ⟨176347083375611867075482703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117564722250407911383655135 176347083375611867075482703)
    ·
      refine ⟨264520625063417800613224055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176347083375611867075482703 264520625063417800613224055)
      ·
        refine ⟨396780937595126700919836083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264520625063417800613224055 396780937595126700919836083)
        ·
          refine ⟨595171406392690051379754125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396780937595126700919836083 595171406392690051379754125)
          ·
            refine ⟨223189277397258769267407797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595171406392690051379754125 223189277397258769267407797)
            ·
              refine ⟨20923994755993009618819481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223189277397258769267407797 20923994755993009618819481)
              ·
                refine ⟨15692996066994757214114611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20923994755993009618819481 15692996066994757214114611)
                ·
                  refine ⟨23539494100492135821171917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15692996066994757214114611 23539494100492135821171917)
                  ·
                    refine ⟨8827310287684550932939469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23539494100492135821171917 8827310287684550932939469)
                    ·
                      refine ⟨3310241357881706599852301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827310287684550932939469 3310241357881706599852301)
                      ·
                        rfl

theorem cell23_6446672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_6446672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446672 prefixEnd_6446672 := by exact prefixLift 6446672
  have htrace : WordTrace (prefixWord ++ tailWord_6446672) baseStart_6446672 baseEnd_6446672 := by
    simpa [prefixWord, tailWord_6446672, baseEnd_6446672] using wordTrace_append hprefix tailTrace_6446672
  have hstable : (prefixWord ++ tailWord_6446672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446672).length < 2 ^ (prefixWord ++ tailWord_6446672).sum := by decide
  have hdescent : baseEnd_6446672 < baseStart_6446672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446676 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_6446676 : Nat := 118140960795 + 6446676 * 2 ^ 59
def prefixEnd_6446676 : Nat := 4983230072969 + 3 ^ 40 * 6446676 * 2
def baseEnd_6446676 : Nat := 3310243411804324584202283

theorem tailTrace_6446676 : CollatzResearch.WordTrace tailWord_6446676 prefixEnd_6446676 3310243411804324584202283 := by
  unfold tailWord_6446676
  simp only [CollatzResearch.WordTrace]
  refine ⟨117564795196400665725227941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156753060261867554300303921 117564795196400665725227941)
  ·
    refine ⟨22043399099325124823480239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117564795196400665725227941 22043399099325124823480239)
    ·
      refine ⟨33065098648987687235220359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22043399099325124823480239 33065098648987687235220359)
      ·
        refine ⟨49597647973481530852830539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33065098648987687235220359 49597647973481530852830539)
        ·
          refine ⟨74396471960222296279245809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49597647973481530852830539 74396471960222296279245809)
          ·
            refine ⟨55797353970166722209434357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74396471960222296279245809 55797353970166722209434357)
            ·
              refine ⟨5231001934703130207134471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55797353970166722209434357 5231001934703130207134471)
              ·
                refine ⟨7846502902054695310701707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5231001934703130207134471 7846502902054695310701707)
                ·
                  refine ⟨11769754353082042966052561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846502902054695310701707 11769754353082042966052561)
                  ·
                    refine ⟨8827315764811532224539421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11769754353082042966052561 8827315764811532224539421)
                    ·
                      refine ⟨3310243411804324584202283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827315764811532224539421 3310243411804324584202283)
                      ·
                        rfl

theorem cell23_6446676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_6446676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446676 prefixEnd_6446676 := by exact prefixLift 6446676
  have htrace : WordTrace (prefixWord ++ tailWord_6446676) baseStart_6446676 baseEnd_6446676 := by
    simpa [prefixWord, tailWord_6446676, baseEnd_6446676] using wordTrace_append hprefix tailTrace_6446676
  have hstable : (prefixWord ++ tailWord_6446676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446676).length < 2 ^ (prefixWord ++ tailWord_6446676).sum := by decide
  have hdescent : baseEnd_6446676 < baseStart_6446676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446706 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_6446706 : Nat := 118140960795 + 6446706 * 2 ^ 59
def prefixEnd_6446706 : Nat := 4983230072969 + 3 ^ 40 * 6446706 * 2
def baseEnd_6446706 : Nat := 3310258816223959466827145

theorem tailTrace_6446706 : CollatzResearch.WordTrace tailWord_6446706 prefixEnd_6446706 3310258816223959466827145 := by
  unfold tailWord_6446706
  simp only [CollatzResearch.WordTrace]
  refine ⟨58782671145673161643511993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156753789721795097716031981 58782671145673161643511993)
  ·
    refine ⟨44087003359254871232633995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58782671145673161643511993 44087003359254871232633995)
    ·
      refine ⟨66130505038882306848950993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44087003359254871232633995 66130505038882306848950993)
      ·
        refine ⟨49597878779161730136713245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66130505038882306848950993 49597878779161730136713245)
        ·
          refine ⟨18599204542185648801267467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49597878779161730136713245 18599204542185648801267467)
          ·
            refine ⟨27898806813278473201901201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18599204542185648801267467 27898806813278473201901201)
            ·
              refine ⟨20924105109958854901425901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27898806813278473201901201 20924105109958854901425901)
              ·
                refine ⟨7846539416234570588034713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20924105109958854901425901 7846539416234570588034713)
                ·
                  refine ⟨5884904562175927941026035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7846539416234570588034713 5884904562175927941026035)
                  ·
                    refine ⟨8827356843263891911539053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5884904562175927941026035 8827356843263891911539053)
                    ·
                      refine ⟨3310258816223959466827145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827356843263891911539053 3310258816223959466827145)
                      ·
                        rfl

theorem cell23_6446706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_6446706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446706 prefixEnd_6446706 := by exact prefixLift 6446706
  have htrace : WordTrace (prefixWord ++ tailWord_6446706) baseStart_6446706 baseEnd_6446706 := by
    simpa [prefixWord, tailWord_6446706, baseEnd_6446706] using wordTrace_append hprefix tailTrace_6446706
  have hstable : (prefixWord ++ tailWord_6446706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446706).length < 2 ^ (prefixWord ++ tailWord_6446706).sum := by decide
  have hdescent : baseEnd_6446706 < baseStart_6446706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446729 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 1, 4, 2]
def baseStart_6446729 : Nat := 118140960795 + 6446729 * 2 ^ 59
def prefixEnd_6446729 : Nat := 4983230072969 + 3 ^ 40 * 6446729 * 2
def baseEnd_6446729 : Nat := 3310270626279012876839539

theorem tailTrace_6446729 : CollatzResearch.WordTrace tailWord_6446729 prefixEnd_6446729 3310270626279012876839539 := by
  unfold tailWord_6446729
  simp only [CollatzResearch.WordTrace]
  refine ⟨235131523461609321502135241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156754348974406214334756827 235131523461609321502135241)
  ·
    refine ⟨176348642596206991126601431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235131523461609321502135241 176348642596206991126601431)
    ·
      refine ⟨264522963894310486689902147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176348642596206991126601431 264522963894310486689902147)
      ·
        refine ⟨396784445841465730034853221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264522963894310486689902147 396784445841465730034853221)
        ·
          refine ⟨74397083595274824381534979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 396784445841465730034853221 74397083595274824381534979)
          ·
            refine ⟨111595625392912236572302469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74397083595274824381534979 111595625392912236572302469)
            ·
              refine ⟨20924179761171044357306713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111595625392912236572302469 20924179761171044357306713)
              ·
                refine ⟨15693134820878283267980035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20924179761171044357306713 15693134820878283267980035)
                ·
                  refine ⟨23539702231317424901970053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15693134820878283267980035 23539702231317424901970053)
                  ·
                    refine ⟨4413694168372017169119385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23539702231317424901970053 4413694168372017169119385)
                    ·
                      refine ⟨3310270626279012876839539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413694168372017169119385 3310270626279012876839539)
                      ·
                        rfl

theorem cell23_6446729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 4, 2].length) (baseStart_6446729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446729 prefixEnd_6446729 := by exact prefixLift 6446729
  have htrace : WordTrace (prefixWord ++ tailWord_6446729) baseStart_6446729 baseEnd_6446729 := by
    simpa [prefixWord, tailWord_6446729, baseEnd_6446729] using wordTrace_append hprefix tailTrace_6446729
  have hstable : (prefixWord ++ tailWord_6446729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446729).length < 2 ^ (prefixWord ++ tailWord_6446729).sum := by decide
  have hdescent : baseEnd_6446729 < baseStart_6446729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446740 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6446740 : Nat := 118140960795 + 6446740 * 2 ^ 59
def prefixEnd_6446740 : Nat := 4983230072969 + 3 ^ 40 * 6446740 * 2
def baseEnd_6446740 : Nat := 3310276274566212333801989

theorem tailTrace_6446740 : CollatzResearch.WordTrace tailWord_6446740 prefixEnd_6446740 3310276274566212333801989 := by
  unfold tailWord_6446740
  simp only [CollatzResearch.WordTrace]
  refine ⟨117565962332284735190392837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156754616443046313587190449 117565962332284735190392837)
  ·
    refine ⟨22043617937303387848198657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117565962332284735190392837 22043617937303387848198657)
    ·
      refine ⟨16532713452977540886148993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22043617937303387848198657 16532713452977540886148993)
      ·
        refine ⟨12399535089733155664611745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16532713452977540886148993 12399535089733155664611745)
        ·
          refine ⟨9299651317299866748458809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12399535089733155664611745 9299651317299866748458809)
          ·
            refine ⟨6974738487974900061344107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9299651317299866748458809 6974738487974900061344107)
            ·
              refine ⟨10462107731962350092016161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6974738487974900061344107 10462107731962350092016161)
              ·
                refine ⟨7846580798971762569012121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10462107731962350092016161 7846580798971762569012121)
                ·
                  refine ⟨5884935599228821926759091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7846580798971762569012121 5884935599228821926759091)
                  ·
                    refine ⟨8827403398843232890138637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5884935599228821926759091 8827403398843232890138637)
                    ·
                      refine ⟨3310276274566212333801989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827403398843232890138637 3310276274566212333801989)
                      ·
                        rfl

theorem cell23_6446740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6446740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446740 prefixEnd_6446740 := by exact prefixLift 6446740
  have htrace : WordTrace (prefixWord ++ tailWord_6446740) baseStart_6446740 baseEnd_6446740 := by
    simpa [prefixWord, tailWord_6446740, baseEnd_6446740] using wordTrace_append hprefix tailTrace_6446740
  have hstable : (prefixWord ++ tailWord_6446740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446740).length < 2 ^ (prefixWord ++ tailWord_6446740).sum := by decide
  have hdescent : baseEnd_6446740 < baseStart_6446740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446745 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_6446745 : Nat := 118140960795 + 6446745 * 2 ^ 59
def prefixEnd_6446745 : Nat := 4983230072969 + 3 ^ 40 * 6446745 * 2
def baseEnd_6446745 : Nat := 3310278841969484814239465

theorem tailTrace_6446745 : CollatzResearch.WordTrace tailWord_6446745 prefixEnd_6446745 3310278841969484814239465 := by
  unfold tailWord_6446745
  simp only [CollatzResearch.WordTrace]
  refine ⟨235132107029551356234717689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156754738019700904156478459 235132107029551356234717689)
  ·
    refine ⟨176349080272163517176038267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235132107029551356234717689 176349080272163517176038267)
    ·
      refine ⟨264523620408245275764057401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176349080272163517176038267 264523620408245275764057401)
      ·
        refine ⟨198392715306183956823043051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264523620408245275764057401 198392715306183956823043051)
        ·
          refine ⟨297589072959275935234564577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198392715306183956823043051 297589072959275935234564577)
          ·
            refine ⟨223191804719456951425923433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297589072959275935234564577 223191804719456951425923433)
            ·
              refine ⟨167393853539592713569442575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223191804719456951425923433 167393853539592713569442575)
              ·
                refine ⟨251090780309389070354163863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167393853539592713569442575 251090780309389070354163863)
                ·
                  refine ⟨376636170464083605531245795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251090780309389070354163863 376636170464083605531245795)
                  ·
                    refine ⟨564954255696125408296868693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 376636170464083605531245795 564954255696125408296868693)
                    ·
                      refine ⟨3310278841969484814239465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 564954255696125408296868693 3310278841969484814239465)
                      ·
                        rfl

theorem cell23_6446745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_6446745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446745 prefixEnd_6446745 := by exact prefixLift 6446745
  have htrace : WordTrace (prefixWord ++ tailWord_6446745) baseStart_6446745 baseEnd_6446745 := by
    simpa [prefixWord, tailWord_6446745, baseEnd_6446745] using wordTrace_append hprefix tailTrace_6446745
  have hstable : (prefixWord ++ tailWord_6446745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446745).length < 2 ^ (prefixWord ++ tailWord_6446745).sum := by decide
  have hdescent : baseEnd_6446745 < baseStart_6446745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446752 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 7]
def baseStart_6446752 : Nat := 118140960795 + 6446752 * 2 ^ 59
def prefixEnd_6446752 : Nat := 4983230072969 + 3 ^ 40 * 6446752 * 2
def baseEnd_6446752 : Nat := 367809159592674031872437

theorem tailTrace_6446752 : CollatzResearch.WordTrace tailWord_6446752 prefixEnd_6446752 367809159592674031872437 := by
  unfold tailWord_6446752
  simp only [CollatzResearch.WordTrace]
  refine ⟨117566181170262998215111255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156754908227017330953481673 117566181170262998215111255)
  ·
    refine ⟨176349271755394497322666883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117566181170262998215111255 176349271755394497322666883)
    ·
      refine ⟨264523907633091745984000325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176349271755394497322666883 264523907633091745984000325)
      ·
        refine ⟨49598232681204702372000061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264523907633091745984000325 49598232681204702372000061)
        ·
          refine ⟨18599337255451763389500023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49598232681204702372000061 18599337255451763389500023)
          ·
            refine ⟨27899005883177645084250035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18599337255451763389500023 27899005883177645084250035)
            ·
              refine ⟨41848508824766467626375053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27899005883177645084250035 41848508824766467626375053)
              ·
                refine ⟨15693190809287425359890645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41848508824766467626375053 15693190809287425359890645)
                ·
                  refine ⟨367809159592674031872437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15693190809287425359890645 367809159592674031872437)
                  ·
                    rfl

theorem cell23_6446752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_6446752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446752 prefixEnd_6446752 := by exact prefixLift 6446752
  have htrace : WordTrace (prefixWord ++ tailWord_6446752) baseStart_6446752 baseEnd_6446752 := by
    simpa [prefixWord, tailWord_6446752, baseEnd_6446752] using wordTrace_append hprefix tailTrace_6446752
  have hstable : (prefixWord ++ tailWord_6446752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446752).length < 2 ^ (prefixWord ++ tailWord_6446752).sum := by decide
  have hdescent : baseEnd_6446752 < baseStart_6446752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446792 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_6446792 : Nat := 118140960795 + 6446792 * 2 ^ 59
def prefixEnd_6446792 : Nat := 4983230072969 + 3 ^ 40 * 6446792 * 2
def baseEnd_6446792 : Nat := 3310302975560246130351749

theorem tailTrace_6446792 : CollatzResearch.WordTrace tailWord_6446792 prefixEnd_6446792 3310302975560246130351749 := by
  unfold tailWord_6446792
  simp only [CollatzResearch.WordTrace]
  refine ⟨117566910630190541630839315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156755880840254055507785753 117566910630190541630839315)
  ·
    refine ⟨176350365945285812446258973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117566910630190541630839315 176350365945285812446258973)
    ·
      refine ⟨66131387229482179667347115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176350365945285812446258973 66131387229482179667347115)
      ·
        refine ⟨99197080844223269501020673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66131387229482179667347115 99197080844223269501020673)
        ·
          refine ⟨74397810633167452125765505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99197080844223269501020673 74397810633167452125765505)
          ·
            refine ⟨55798357974875589094324129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74397810633167452125765505 55798357974875589094324129)
            ·
              refine ⟨41848768481156691820743097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55798357974875589094324129 41848768481156691820743097)
              ·
                refine ⟨31386576360867518865557323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41848768481156691820743097 31386576360867518865557323)
                ·
                  refine ⟨47079864541301278298335985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31386576360867518865557323 47079864541301278298335985)
                  ·
                    refine ⟨35309898405975958723751989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47079864541301278298335985 35309898405975958723751989)
                    ·
                      refine ⟨3310302975560246130351749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35309898405975958723751989 3310302975560246130351749)
                      ·
                        rfl

theorem cell23_6446792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_6446792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446792 prefixEnd_6446792 := by exact prefixLift 6446792
  have htrace : WordTrace (prefixWord ++ tailWord_6446792) baseStart_6446792 baseEnd_6446792 := by
    simpa [prefixWord, tailWord_6446792, baseEnd_6446792] using wordTrace_append hprefix tailTrace_6446792
  have hstable : (prefixWord ++ tailWord_6446792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446792).length < 2 ^ (prefixWord ++ tailWord_6446792).sum := by decide
  have hdescent : baseEnd_6446792 < baseStart_6446792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446839 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_6446839 : Nat := 118140960795 + 6446839 * 2 ^ 59
def prefixEnd_6446839 : Nat := 4983230072969 + 3 ^ 40 * 6446839 * 2
def baseEnd_6446839 : Nat := 3310327109151007446464033

theorem tailTrace_6446839 : CollatzResearch.WordTrace tailWord_6446839 prefixEnd_6446839 3310327109151007446464033 := by
  unfold tailWord_6446839
  simp only [CollatzResearch.WordTrace]
  refine ⟨235135535491210810288639571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156757023660807206859093047 235135535491210810288639571)
  ·
    refine ⟨352703303236816215432959357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235135535491210810288639571 352703303236816215432959357)
    ·
      refine ⟨132263738713806080787359759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352703303236816215432959357 132263738713806080787359759)
      ·
        refine ⟨198395608070709121181039639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132263738713806080787359759 198395608070709121181039639)
        ·
          refine ⟨297593412106063681771559459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198395608070709121181039639 297593412106063681771559459)
          ·
            refine ⟨446390118159095522657339189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297593412106063681771559459 446390118159095522657339189)
            ·
              refine ⟨41849073577415205249125549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446390118159095522657339189 41849073577415205249125549)
              ·
                refine ⟨15693402591530701968422081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41849073577415205249125549 15693402591530701968422081)
                ·
                  refine ⟨11770051943648026476316561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15693402591530701968422081 11770051943648026476316561)
                  ·
                    refine ⟨8827538957736019857237421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11770051943648026476316561 8827538957736019857237421)
                    ·
                      refine ⟨3310327109151007446464033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827538957736019857237421 3310327109151007446464033)
                      ·
                        rfl

theorem cell23_6446839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_6446839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446839 prefixEnd_6446839 := by exact prefixLift 6446839
  have htrace : WordTrace (prefixWord ++ tailWord_6446839) baseStart_6446839 baseEnd_6446839 := by
    simpa [prefixWord, tailWord_6446839, baseEnd_6446839] using wordTrace_append hprefix tailTrace_6446839
  have hstable : (prefixWord ++ tailWord_6446839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446839).length < 2 ^ (prefixWord ++ tailWord_6446839).sum := by decide
  have hdescent : baseEnd_6446839 < baseStart_6446839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446854 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_6446854 : Nat := 118140960795 + 6446854 * 2 ^ 59
def prefixEnd_6446854 : Nat := 4983230072969 + 3 ^ 40 * 6446854 * 2
def baseEnd_6446854 : Nat := 367814979040091654197385

theorem tailTrace_6446854 : CollatzResearch.WordTrace tailWord_6446854 prefixEnd_6446854 367814979040091654197385 := by
  unfold tailWord_6446854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348002580817389620326113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156757388390770978566957077 7348002580817389620326113)
  ·
    refine ⟨5511001935613042215244585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7348002580817389620326113 5511001935613042215244585)
    ·
      refine ⟨4133251451709781661433439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5511001935613042215244585 4133251451709781661433439)
      ·
        refine ⟨6199877177564672492150159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133251451709781661433439 6199877177564672492150159)
        ·
          refine ⟨9299815766347008738225239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199877177564672492150159 9299815766347008738225239)
          ·
            refine ⟨13949723649520513107337859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9299815766347008738225239 13949723649520513107337859)
            ·
              refine ⟨20924585474280769661006789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13949723649520513107337859 20924585474280769661006789)
              ·
                refine ⟨3923359776427644311438773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20924585474280769661006789 3923359776427644311438773)
                ·
                  refine ⟨367814979040091654197385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3923359776427644311438773 367814979040091654197385)
                  ·
                    rfl

theorem cell23_6446854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_6446854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446854 prefixEnd_6446854 := by exact prefixLift 6446854
  have htrace : WordTrace (prefixWord ++ tailWord_6446854) baseStart_6446854 baseEnd_6446854 := by
    simpa [prefixWord, tailWord_6446854, baseEnd_6446854] using wordTrace_append hprefix tailTrace_6446854
  have hstable : (prefixWord ++ tailWord_6446854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446854).length < 2 ^ (prefixWord ++ tailWord_6446854).sum := by decide
  have hdescent : baseEnd_6446854 < baseStart_6446854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446906 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_6446906 : Nat := 118140960795 + 6446906 * 2 ^ 59
def prefixEnd_6446906 : Nat := 4983230072969 + 3 ^ 40 * 6446906 * 2
def baseEnd_6446906 : Nat := 1103453837451619561442075

theorem tailTrace_6446906 : CollatzResearch.WordTrace tailWord_6446906 prefixEnd_6446906 1103453837451619561442075 := by
  unfold tailWord_6446906
  simp only [CollatzResearch.WordTrace]
  refine ⟨58784494795492020182832143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156758652787978720487552381 58784494795492020182832143)
  ·
    refine ⟨88176742193238030274248215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58784494795492020182832143 88176742193238030274248215)
    ·
      refine ⟨132265113289857045411372323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88176742193238030274248215 132265113289857045411372323)
      ·
        refine ⟨198397669934785568117058485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132265113289857045411372323 198397669934785568117058485)
        ·
          refine ⟨18599781556386147010974233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198397669934785568117058485 18599781556386147010974233)
          ·
            refine ⟨13949836167289610258230675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18599781556386147010974233 13949836167289610258230675)
            ·
              refine ⟨20924754250934415387346013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13949836167289610258230675 20924754250934415387346013)
              ·
                refine ⟨7846782844100405770254755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20924754250934415387346013 7846782844100405770254755)
                ·
                  refine ⟨11770174266150608655382133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846782844100405770254755 11770174266150608655382133)
                  ·
                    refine ⟨1103453837451619561442075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11770174266150608655382133 1103453837451619561442075)
                    ·
                      rfl

theorem cell23_6446906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_6446906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446906 prefixEnd_6446906 := by exact prefixLift 6446906
  have htrace : WordTrace (prefixWord ++ tailWord_6446906) baseStart_6446906 baseEnd_6446906 := by
    simpa [prefixWord, tailWord_6446906, baseEnd_6446906] using wordTrace_append hprefix tailTrace_6446906
  have hstable : (prefixWord ++ tailWord_6446906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446906).length < 2 ^ (prefixWord ++ tailWord_6446906).sum := by decide
  have hdescent : baseEnd_6446906 < baseStart_6446906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446929 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_6446929 : Nat := 118140960795 + 6446929 * 2 ^ 59
def prefixEnd_6446929 : Nat := 4983230072969 + 3 ^ 40 * 6446929 * 2
def baseEnd_6446929 : Nat := 3310373322409912094338619

theorem tailTrace_6446929 : CollatzResearch.WordTrace tailWord_6446929 prefixEnd_6446929 3310373322409912094338619 := by
  unfold tailWord_6446929
  simp only [CollatzResearch.WordTrace]
  refine ⟨235138818060884755659415841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156759212040589837106277227 235138818060884755659415841)
  ·
    refine ⟨176354113545663566744561881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235138818060884755659415841 176354113545663566744561881)
    ·
      refine ⟨132265585159247675058421411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176354113545663566744561881 132265585159247675058421411)
      ·
        refine ⟨198398377738871512587632117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132265585159247675058421411 198398377738871512587632117)
        ·
          refine ⟨18599847913019204305090511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198398377738871512587632117 18599847913019204305090511)
          ·
            refine ⟨27899771869528806457635767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18599847913019204305090511 27899771869528806457635767)
            ·
              refine ⟨41849657804293209686453651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27899771869528806457635767 41849657804293209686453651)
              ·
                refine ⟨62774486706439814529680477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41849657804293209686453651 62774486706439814529680477)
                ·
                  refine ⟨23540432514914930448630179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62774486706439814529680477 23540432514914930448630179)
                  ·
                    refine ⟨35310648772372395672945269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23540432514914930448630179 35310648772372395672945269)
                    ·
                      refine ⟨3310373322409912094338619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35310648772372395672945269 3310373322409912094338619)
                      ·
                        rfl

theorem cell23_6446929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_6446929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446929 prefixEnd_6446929 := by exact prefixLift 6446929
  have htrace : WordTrace (prefixWord ++ tailWord_6446929) baseStart_6446929 baseEnd_6446929 := by
    simpa [prefixWord, tailWord_6446929, baseEnd_6446929] using wordTrace_append hprefix tailTrace_6446929
  have hstable : (prefixWord ++ tailWord_6446929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446929).length < 2 ^ (prefixWord ++ tailWord_6446929).sum := by decide
  have hdescent : baseEnd_6446929 < baseStart_6446929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446943 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 3, 2, 2]
def baseStart_6446943 : Nat := 118140960795 + 6446943 * 2 ^ 59
def prefixEnd_6446943 : Nat := 4983230072969 + 3 ^ 40 * 6446943 * 2
def baseEnd_6446943 : Nat := 3310380511139075039563555

theorem tailTrace_6446943 : CollatzResearch.WordTrace tailWord_6446943 prefixEnd_6446943 3310380511139075039563555 := by
  unfold tailWord_6446943
  simp only [CollatzResearch.WordTrace]
  refine ⟨235139328682834036050425483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156759552455222690700283655 235139328682834036050425483)
  ·
    refine ⟨352708993024251054075638225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235139328682834036050425483 352708993024251054075638225)
    ·
      refine ⟨264531744768188290556728669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352708993024251054075638225 264531744768188290556728669)
      ·
        refine ⟨99199404288070608958773251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264531744768188290556728669 99199404288070608958773251)
        ·
          refine ⟨148799106432105913438159877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99199404288070608958773251 148799106432105913438159877)
          ·
            refine ⟨27899832456019858769654977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148799106432105913438159877 27899832456019858769654977)
            ·
              refine ⟨20924874342014894077241233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27899832456019858769654977 20924874342014894077241233)
              ·
                refine ⟨15693655756511170557930925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20924874342014894077241233 15693655756511170557930925)
                ·
                  refine ⟨5885120908691688959224097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15693655756511170557930925 5885120908691688959224097)
                  ·
                    refine ⟨4413840681518766719418073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5885120908691688959224097 4413840681518766719418073)
                    ·
                      refine ⟨3310380511139075039563555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413840681518766719418073 3310380511139075039563555)
                      ·
                        rfl

theorem cell23_6446943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_6446943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446943 prefixEnd_6446943 := by exact prefixLift 6446943
  have htrace : WordTrace (prefixWord ++ tailWord_6446943) baseStart_6446943 baseEnd_6446943 := by
    simpa [prefixWord, tailWord_6446943, baseEnd_6446943] using wordTrace_append hprefix tailTrace_6446943
  have hstable : (prefixWord ++ tailWord_6446943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446943).length < 2 ^ (prefixWord ++ tailWord_6446943).sum := by decide
  have hdescent : baseEnd_6446943 < baseStart_6446943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446954 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6446954 : Nat := 118140960795 + 6446954 * 2 ^ 59
def prefixEnd_6446954 : Nat := 4983230072969 + 3 ^ 40 * 6446954 * 2
def baseEnd_6446954 : Nat := 3310386159426274496526005

theorem tailTrace_6446954 : CollatzResearch.WordTrace tailWord_6446954 prefixEnd_6446954 3310386159426274496526005 := by
  unfold tailWord_6446954
  simp only [CollatzResearch.WordTrace]
  refine ⟨58784932471448546232268979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156759819923862789952717277 58784932471448546232268979)
  ·
    refine ⟨88177398707172819348403469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58784932471448546232268979 88177398707172819348403469)
    ·
      refine ⟨33066524515189807255651301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88177398707172819348403469 33066524515189807255651301)
      ·
        refine ⟨6199973346598088860434619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33066524515189807255651301 6199973346598088860434619)
        ·
          refine ⟨9299960019897133290651929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199973346598088860434619 9299960019897133290651929)
          ·
            refine ⟨6974970014922849967988947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9299960019897133290651929 6974970014922849967988947)
            ·
              refine ⟨10462455022384274951983421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6974970014922849967988947 10462455022384274951983421)
              ·
                refine ⟨3923420633394103106993783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10462455022384274951983421 3923420633394103106993783)
                ·
                  refine ⟨5885130950091154660490675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923420633394103106993783 5885130950091154660490675)
                  ·
                    refine ⟨8827696425136731990736013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5885130950091154660490675 8827696425136731990736013)
                    ·
                      refine ⟨3310386159426274496526005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827696425136731990736013 3310386159426274496526005)
                      ·
                        rfl

theorem cell23_6446954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6446954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446954 prefixEnd_6446954 := by exact prefixLift 6446954
  have htrace : WordTrace (prefixWord ++ tailWord_6446954) baseStart_6446954 baseEnd_6446954 := by
    simpa [prefixWord, tailWord_6446954, baseEnd_6446954] using wordTrace_append hprefix tailTrace_6446954
  have hstable : (prefixWord ++ tailWord_6446954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446954).length < 2 ^ (prefixWord ++ tailWord_6446954).sum := by decide
  have hdescent : baseEnd_6446954 < baseStart_6446954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6446976 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 4, 1, 3]
def baseStart_6446976 : Nat := 118140960795 + 6446976 * 2 ^ 59
def prefixEnd_6446976 : Nat := 4983230072969 + 3 ^ 40 * 6446976 * 2
def baseEnd_6446976 : Nat := 3310397456000673410450903

theorem tailTrace_6446976 : CollatzResearch.WordTrace tailWord_6446976 prefixEnd_6446976 3310397456000673410450903 := by
  unfold tailWord_6446976
  simp only [CollatzResearch.WordTrace]
  refine ⟨117570266145857241343188391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156760354861142988457584521 117570266145857241343188391)
  ·
    refine ⟨176355399218785862014782587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117570266145857241343188391 176355399218785862014782587)
    ·
      refine ⟨264533098828178793022173881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176355399218785862014782587 264533098828178793022173881)
      ·
        refine ⟨198399824121134094766630411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264533098828178793022173881 198399824121134094766630411)
        ·
          refine ⟨297599736181701142149945617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198399824121134094766630411 297599736181701142149945617)
          ·
            refine ⟨223199802136275856612459213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297599736181701142149945617 223199802136275856612459213)
            ·
              refine ⟨83699925801103446229672205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223199802136275856612459213 83699925801103446229672205)
              ·
                refine ⟨31387472175413792336127077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83699925801103446229672205 31387472175413792336127077)
                ·
                  refine ⟨5885151032890086063023827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31387472175413792336127077 5885151032890086063023827)
                  ·
                    refine ⟨8827726549335129094535741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5885151032890086063023827 8827726549335129094535741)
                    ·
                      refine ⟨3310397456000673410450903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827726549335129094535741 3310397456000673410450903)
                      ·
                        rfl

theorem cell23_6446976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_6446976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6446976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6446976 prefixEnd_6446976 := by exact prefixLift 6446976
  have htrace : WordTrace (prefixWord ++ tailWord_6446976) baseStart_6446976 baseEnd_6446976 := by
    simpa [prefixWord, tailWord_6446976, baseEnd_6446976] using wordTrace_append hprefix tailTrace_6446976
  have hstable : (prefixWord ++ tailWord_6446976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6446976).length < 2 ^ (prefixWord ++ tailWord_6446976).sum := by decide
  have hdescent : baseEnd_6446976 < baseStart_6446976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6446976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447019 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 3]
def baseStart_6447019 : Nat := 118140960795 + 6447019 * 2 ^ 59
def prefixEnd_6447019 : Nat := 4983230072969 + 3 ^ 40 * 6447019 * 2
def baseEnd_6447019 : Nat := 3310419535668816742213205

theorem tailTrace_6447019 : CollatzResearch.WordTrace tailWord_6447019 prefixEnd_6447019 3310419535668816742213205 := by
  unfold tailWord_6447019
  simp only [CollatzResearch.WordTrace]
  refine ⟨235142100630558701030192111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156761400420372467353461407 235142100630558701030192111)
  ·
    refine ⟨352713150945838051545288167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235142100630558701030192111 352713150945838051545288167)
    ·
      refine ⟨529069726418757077317932251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352713150945838051545288167 529069726418757077317932251)
      ·
        refine ⟨793604589628135615976898377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529069726418757077317932251 793604589628135615976898377)
        ·
          refine ⟨595203442221101711982673783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793604589628135615976898377 595203442221101711982673783)
          ·
            refine ⟨892805163331652567974010675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595203442221101711982673783 892805163331652567974010675)
            ·
              refine ⟨1339207744997478851961016013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892805163331652567974010675 1339207744997478851961016013)
              ·
                refine ⟨502202904374054569485381005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1339207744997478851961016013 502202904374054569485381005)
                ·
                  refine ⟨188326089140270463557017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502202904374054569485381005 188326089140270463557017877)
                  ·
                    refine ⟨8827785428450177979235213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188326089140270463557017877 8827785428450177979235213)
                    ·
                      refine ⟨3310419535668816742213205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827785428450177979235213 3310419535668816742213205)
                      ·
                        rfl

theorem cell23_6447019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 3].length) (baseStart_6447019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447019 prefixEnd_6447019 := by exact prefixLift 6447019
  have htrace : WordTrace (prefixWord ++ tailWord_6447019) baseStart_6447019 baseEnd_6447019 := by
    simpa [prefixWord, tailWord_6447019, baseEnd_6447019] using wordTrace_append hprefix tailTrace_6447019
  have hstable : (prefixWord ++ tailWord_6447019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447019).length < 2 ^ (prefixWord ++ tailWord_6447019).sum := by decide
  have hdescent : baseEnd_6447019 < baseStart_6447019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447028 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6447028 : Nat := 118140960795 + 6447028 * 2 ^ 59
def prefixEnd_6447028 : Nat := 4983230072969 + 3 ^ 40 * 6447028 * 2
def baseEnd_6447028 : Nat := 3310424156994707207000665

theorem tailTrace_6447028 : CollatzResearch.WordTrace tailWord_6447028 prefixEnd_6447028 3310424156994707207000665 := by
  unfold tailWord_6447028
  simp only [CollatzResearch.WordTrace]
  refine ⟨117571214443763047783634869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156761619258350730378179825 117571214443763047783634869)
  ·
    refine ⟨11022301354102785729715769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117571214443763047783634869 11022301354102785729715769)
    ·
      refine ⟨8266726015577089297286827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11022301354102785729715769 8266726015577089297286827)
      ·
        refine ⟨12400089023365633945930241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8266726015577089297286827 12400089023365633945930241)
        ·
          refine ⟨9300066767524225459447681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12400089023365633945930241 9300066767524225459447681)
          ·
            refine ⟨6975050075643169094585761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300066767524225459447681 6975050075643169094585761)
            ·
              refine ⟨5231287556732376820939321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6975050075643169094585761 5231287556732376820939321)
              ·
                refine ⟨3923465667549282615704491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5231287556732376820939321 3923465667549282615704491)
                ·
                  refine ⟨5885198501323923923556737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923465667549282615704491 5885198501323923923556737)
                  ·
                    refine ⟨4413898875992942942667553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5885198501323923923556737 4413898875992942942667553)
                    ·
                      refine ⟨3310424156994707207000665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413898875992942942667553 3310424156994707207000665)
                      ·
                        rfl

theorem cell23_6447028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6447028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447028 prefixEnd_6447028 := by exact prefixLift 6447028
  have htrace : WordTrace (prefixWord ++ tailWord_6447028) baseStart_6447028 baseEnd_6447028 := by
    simpa [prefixWord, tailWord_6447028, baseEnd_6447028] using wordTrace_append hprefix tailTrace_6447028
  have hstable : (prefixWord ++ tailWord_6447028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447028).length < 2 ^ (prefixWord ++ tailWord_6447028).sum := by decide
  have hdescent : baseEnd_6447028 < baseStart_6447028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447039 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 7]
def baseStart_6447039 : Nat := 118140960795 + 6447039 * 2 ^ 59
def prefixEnd_6447039 : Nat := 4983230072969 + 3 ^ 40 * 6447039 * 2
def baseEnd_6447039 : Nat := 367825533920211851551457

theorem tailTrace_6447039 : CollatzResearch.WordTrace tailWord_6447039 prefixEnd_6447039 367825533920211851551457 := by
  unfold tailWord_6447039
  simp only [CollatzResearch.WordTrace]
  refine ⟨235142830090486244445920171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156761886726990829630613447 235142830090486244445920171)
  ·
    refine ⟨352714245135729366668880257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235142830090486244445920171 352714245135729366668880257)
    ·
      refine ⟨264535683851797025001660193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352714245135729366668880257 264535683851797025001660193)
      ·
        refine ⟨198401762888847768751245145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264535683851797025001660193 198401762888847768751245145)
        ·
          refine ⟨148801322166635826563433859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198401762888847768751245145 148801322166635826563433859)
          ·
            refine ⟨223201983249953739845150789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148801322166635826563433859 223201983249953739845150789)
            ·
              refine ⟨41850371859366326220965773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223201983249953739845150789 41850371859366326220965773)
              ·
                refine ⟨15693889447262372332862165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41850371859366326220965773 15693889447262372332862165)
                ·
                  refine ⟨367825533920211851551457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15693889447262372332862165 367825533920211851551457)
                  ·
                    rfl

theorem cell23_6447039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 7].length) (baseStart_6447039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447039 prefixEnd_6447039 := by exact prefixLift 6447039
  have htrace : WordTrace (prefixWord ++ tailWord_6447039) baseStart_6447039 baseEnd_6447039 := by
    simpa [prefixWord, tailWord_6447039, baseEnd_6447039] using wordTrace_append hprefix tailTrace_6447039
  have hstable : (prefixWord ++ tailWord_6447039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447039).length < 2 ^ (prefixWord ++ tailWord_6447039).sum := by decide
  have hdescent : baseEnd_6447039 < baseStart_6447039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447050 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_6447050 : Nat := 118140960795 + 6447050 * 2 ^ 59
def prefixEnd_6447050 : Nat := 4983230072969 + 3 ^ 40 * 6447050 * 2
def baseEnd_6447050 : Nat := 3310435453569106120925563

theorem tailTrace_6447050 : CollatzResearch.WordTrace tailWord_6447050 prefixEnd_6447050 3310435453569106120925563 := by
  unfold tailWord_6447050
  simp only [CollatzResearch.WordTrace]
  refine ⟨58785807823361598331142651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156762154195630928883047069 58785807823361598331142651)
  ·
    refine ⟨88178711735042397496713977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58785807823361598331142651 88178711735042397496713977)
    ·
      refine ⟨66134033801281798122535483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88178711735042397496713977 66134033801281798122535483)
      ·
        refine ⟨99201050701922697183803225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66134033801281798122535483 99201050701922697183803225)
        ·
          refine ⟨74400788026442022887852419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99201050701922697183803225 74400788026442022887852419)
          ·
            refine ⟨111601182039663034331778629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74400788026442022887852419 111601182039663034331778629)
            ·
              refine ⟨20925221632436818937208493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111601182039663034331778629 20925221632436818937208493)
              ·
                refine ⟨7846958112163807101453185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20925221632436818937208493 7846958112163807101453185)
                ·
                  refine ⟨5885218584122855326089889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7846958112163807101453185 5885218584122855326089889)
                  ·
                    refine ⟨4413913938092141494567417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5885218584122855326089889 4413913938092141494567417)
                    ·
                      refine ⟨3310435453569106120925563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4413913938092141494567417 3310435453569106120925563)
                      ·
                        rfl

theorem cell23_6447050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_6447050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447050 prefixEnd_6447050 := by exact prefixLift 6447050
  have htrace : WordTrace (prefixWord ++ tailWord_6447050) baseStart_6447050 baseEnd_6447050 := by
    simpa [prefixWord, tailWord_6447050, baseEnd_6447050] using wordTrace_append hprefix tailTrace_6447050
  have hstable : (prefixWord ++ tailWord_6447050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447050).length < 2 ^ (prefixWord ++ tailWord_6447050).sum := by decide
  have hdescent : baseEnd_6447050 < baseStart_6447050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447124 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 5]
def baseStart_6447124 : Nat := 118140960795 + 6447124 * 2 ^ 59
def prefixEnd_6447124 : Nat := 4983230072969 + 3 ^ 40 * 6447124 * 2
def baseEnd_6447124 : Nat := 367830383459726536822247

theorem tailTrace_6447124 : CollatzResearch.WordTrace tailWord_6447124 prefixEnd_6447124 367830383459726536822247 := by
  unfold tailWord_6447124
  simp only [CollatzResearch.WordTrace]
  refine ⟨117572965147589151981382213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156763953530118869308509617 117572965147589151981382213)
  ·
    refine ⟨22044930965172965996509165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117572965147589151981382213 22044930965172965996509165)
    ·
      refine ⟨8266849111939862248690937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22044930965172965996509165 8266849111939862248690937)
      ·
        refine ⟨6200136833954896686518203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8266849111939862248690937 6200136833954896686518203)
        ·
          refine ⟨9300205250932345029777305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200136833954896686518203 9300205250932345029777305)
          ·
            refine ⟨6975153938199258772332979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300205250932345029777305 6975153938199258772332979)
            ·
              refine ⟨10462730907298888158499469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975153938199258772332979 10462730907298888158499469)
              ·
                refine ⟨3923524090237083059437301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10462730907298888158499469 3923524090237083059437301)
                ·
                  refine ⟨367830383459726536822247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3923524090237083059437301 367830383459726536822247)
                  ·
                    rfl

theorem cell23_6447124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_6447124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447124 prefixEnd_6447124 := by exact prefixLift 6447124
  have htrace : WordTrace (prefixWord ++ tailWord_6447124) baseStart_6447124 baseEnd_6447124 := by
    simpa [prefixWord, tailWord_6447124, baseEnd_6447124] using wordTrace_append hprefix tailTrace_6447124
  have hstable : (prefixWord ++ tailWord_6447124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447124).length < 2 ^ (prefixWord ++ tailWord_6447124).sum := by decide
  have hdescent : baseEnd_6447124 < baseStart_6447124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447140 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6447140 : Nat := 118140960795 + 6447140 * 2 ^ 59
def prefixEnd_6447140 : Nat := 4983230072969 + 3 ^ 40 * 6447140 * 2
def baseEnd_6447140 : Nat := 3310481666828010768800149

theorem tailTrace_6447140 : CollatzResearch.WordTrace tailWord_6447140 prefixEnd_6447140 3310481666828010768800149 := by
  unfold tailWord_6447140
  simp only [CollatzResearch.WordTrace]
  refine ⟨117573256931560169347673437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156764342575413559130231249 117573256931560169347673437)
  ·
    refine ⟨44089971349335063505377539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117573256931560169347673437 44089971349335063505377539)
    ·
      refine ⟨66134957024002595258066309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44089971349335063505377539 66134957024002595258066309)
      ·
        refine ⟨12400304442000486610887433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66134957024002595258066309 12400304442000486610887433)
        ·
          refine ⟨9300228331500364958165575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12400304442000486610887433 9300228331500364958165575)
          ·
            refine ⟨13950342497250547437248363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9300228331500364958165575 13950342497250547437248363)
            ·
              refine ⟨20925513745875821155872545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13950342497250547437248363 20925513745875821155872545)
              ·
                refine ⟨15694135309406865866904409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20925513745875821155872545 15694135309406865866904409)
                ·
                  refine ⟨11770601482055149400178307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15694135309406865866904409 11770601482055149400178307)
                  ·
                    refine ⟨17655902223082724100267461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11770601482055149400178307 17655902223082724100267461)
                    ·
                      refine ⟨3310481666828010768800149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17655902223082724100267461 3310481666828010768800149)
                      ·
                        rfl

theorem cell23_6447140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6447140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447140 prefixEnd_6447140 := by exact prefixLift 6447140
  have htrace : WordTrace (prefixWord ++ tailWord_6447140) baseStart_6447140 baseEnd_6447140 := by
    simpa [prefixWord, tailWord_6447140, baseEnd_6447140] using wordTrace_append hprefix tailTrace_6447140
  have hstable : (prefixWord ++ tailWord_6447140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447140).length < 2 ^ (prefixWord ++ tailWord_6447140).sum := by decide
  have hdescent : baseEnd_6447140 < baseStart_6447140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447150 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6447150 : Nat := 118140960795 + 6447150 * 2 ^ 59
def prefixEnd_6447150 : Nat := 4983230072969 + 3 ^ 40 * 6447150 * 2
def baseEnd_6447150 : Nat := 1103495600544851909891701

theorem tailTrace_6447150 : CollatzResearch.WordTrace tailWord_6447150 prefixEnd_6447150 1103495600544851909891701 := by
  unfold tailWord_6447150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29393359824135513800401363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156764585728722740268807269 29393359824135513800401363)
  ·
    refine ⟨44090039736203270700602045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29393359824135513800401363 44090039736203270700602045)
    ·
      refine ⟨16533764901076226512725767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44090039736203270700602045 16533764901076226512725767)
      ·
        refine ⟨24800647351614339769088651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16533764901076226512725767 24800647351614339769088651)
        ·
          refine ⟨37200971027421509653632977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24800647351614339769088651 37200971027421509653632977)
          ·
            refine ⟨27900728270566132240224733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37200971027421509653632977 27900728270566132240224733)
            ·
              refine ⟨10462773101462299590084275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27900728270566132240224733 10462773101462299590084275)
              ·
                refine ⟨15694159652193449385126413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462773101462299590084275 15694159652193449385126413)
                ·
                  refine ⟨5885309869572543519422405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15694159652193449385126413 5885309869572543519422405)
                  ·
                    refine ⟨1103495600544851909891701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885309869572543519422405 1103495600544851909891701)
                    ·
                      rfl

theorem cell23_6447150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6447150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447150 prefixEnd_6447150 := by exact prefixLift 6447150
  have htrace : WordTrace (prefixWord ++ tailWord_6447150) baseStart_6447150 baseEnd_6447150 := by
    simpa [prefixWord, tailWord_6447150, baseEnd_6447150] using wordTrace_append hprefix tailTrace_6447150
  have hstable : (prefixWord ++ tailWord_6447150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447150).length < 2 ^ (prefixWord ++ tailWord_6447150).sum := by decide
  have hdescent : baseEnd_6447150 < baseStart_6447150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447173 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_6447173 : Nat := 118140960795 + 6447173 * 2 ^ 59
def prefixEnd_6447173 : Nat := 4983230072969 + 3 ^ 40 * 6447173 * 2
def baseEnd_6447173 : Nat := 3310498611689609139687497

theorem tailTrace_6447173 : CollatzResearch.WordTrace tailWord_6447173 prefixEnd_6447173 3310498611689609139687497 := by
  unfold tailWord_6447173
  simp only [CollatzResearch.WordTrace]
  refine ⟨235147717472000785331298173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156765144981333856887532115 235147717472000785331298173)
  ·
    refine ⟨88180394052000294499236815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235147717472000785331298173 88180394052000294499236815)
    ·
      refine ⟨132270591078000441748855223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88180394052000294499236815 132270591078000441748855223)
      ·
        refine ⟨198405886617000662623282835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132270591078000441748855223 198405886617000662623282835)
        ·
          refine ⟨297608829925500993934924253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198405886617000662623282835 297608829925500993934924253)
          ·
            refine ⟨111603311222062872725596595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297608829925500993934924253 111603311222062872725596595)
            ·
              refine ⟨167404966833094309088394893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111603311222062872725596595 167404966833094309088394893)
              ·
                refine ⟨62776862562410365908148085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167404966833094309088394893 62776862562410365908148085)
                ·
                  refine ⟨5885330865225971803888883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62776862562410365908148085 5885330865225971803888883)
                  ·
                    refine ⟨8827996297838957705833325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5885330865225971803888883 8827996297838957705833325)
                    ·
                      refine ⟨3310498611689609139687497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8827996297838957705833325 3310498611689609139687497)
                      ·
                        rfl

theorem cell23_6447173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_6447173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447173 prefixEnd_6447173 := by exact prefixLift 6447173
  have htrace : WordTrace (prefixWord ++ tailWord_6447173) baseStart_6447173 baseEnd_6447173 := by
    simpa [prefixWord, tailWord_6447173, baseEnd_6447173] using wordTrace_append hprefix tailTrace_6447173
  have hstable : (prefixWord ++ tailWord_6447173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447173).length < 2 ^ (prefixWord ++ tailWord_6447173).sum := by decide
  have hdescent : baseEnd_6447173 < baseStart_6447173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447183 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 6, 3, 2]
def baseStart_6447183 : Nat := 118140960795 + 6447183 * 2 ^ 59
def prefixEnd_6447183 : Nat := 4983230072969 + 3 ^ 40 * 6447183 * 2
def baseEnd_6447183 : Nat := 3310503746496154100562451

theorem tailTrace_6447183 : CollatzResearch.WordTrace tailWord_6447183 prefixEnd_6447183 3310503746496154100562451 := by
  unfold tailWord_6447183
  simp only [CollatzResearch.WordTrace]
  refine ⟨235148082201964557039162203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156765388134643038026108135 235148082201964557039162203)
  ·
    refine ⟨352722123302946835558743305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235148082201964557039162203 352722123302946835558743305)
    ·
      refine ⟨264541592477210126669057479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352722123302946835558743305 264541592477210126669057479)
      ·
        refine ⟨396812388715815190003586219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264541592477210126669057479 396812388715815190003586219)
        ·
          refine ⟨595218583073722785005379329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396812388715815190003586219 595218583073722785005379329)
          ·
            refine ⟨446413937305292088754034497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595218583073722785005379329 446413937305292088754034497)
            ·
              refine ⟨334810452978969066565525873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446413937305292088754034497 334810452978969066565525873)
              ·
                refine ⟨251107839734226799924144405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334810452978969066565525873 251107839734226799924144405)
                ·
                  refine ⟨11770679987541881246444269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251107839734226799924144405 11770679987541881246444269)
                  ·
                    refine ⟨4414004995328205467416601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11770679987541881246444269 4414004995328205467416601)
                    ·
                      refine ⟨3310503746496154100562451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414004995328205467416601 3310503746496154100562451)
                      ·
                        rfl

theorem cell23_6447183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3, 2].length) (baseStart_6447183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447183 prefixEnd_6447183 := by exact prefixLift 6447183
  have htrace : WordTrace (prefixWord ++ tailWord_6447183) baseStart_6447183 baseEnd_6447183 := by
    simpa [prefixWord, tailWord_6447183, baseEnd_6447183] using wordTrace_append hprefix tailTrace_6447183
  have hstable : (prefixWord ++ tailWord_6447183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447183).length < 2 ^ (prefixWord ++ tailWord_6447183).sum := by decide
  have hdescent : baseEnd_6447183 < baseStart_6447183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447200 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 2, 3, 2]
def baseStart_6447200 : Nat := 118140960795 + 6447200 * 2 ^ 59
def prefixEnd_6447200 : Nat := 4983230072969 + 3 ^ 40 * 6447200 * 2
def baseEnd_6447200 : Nat := 3310512475667280534049873

theorem tailTrace_6447200 : CollatzResearch.WordTrace tailWord_6447200 prefixEnd_6447200 3310512475667280534049873 := by
  unfold tailWord_6447200
  simp only [CollatzResearch.WordTrace]
  refine ⟨117574351121451484471265527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156765801495268645961687369 117574351121451484471265527)
  ·
    refine ⟨176361526682177226706898291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117574351121451484471265527 176361526682177226706898291)
    ·
      refine ⟨264542290023265840060347437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176361526682177226706898291 264542290023265840060347437)
      ·
        refine ⟨99203358758724690022630289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264542290023265840060347437 99203358758724690022630289)
        ·
          refine ⟨74402519069043517516972717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99203358758724690022630289 74402519069043517516972717)
          ·
            refine ⟨27900944650891319068864769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74402519069043517516972717 27900944650891319068864769)
            ·
              refine ⟨20925708488168489301648577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27900944650891319068864769 20925708488168489301648577)
              ·
                refine ⟨15694281366126366976236433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20925708488168489301648577 15694281366126366976236433)
                ·
                  refine ⟨11770711024594775232177325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15694281366126366976236433 11770711024594775232177325)
                  ·
                    refine ⟨4414016634223040712066497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11770711024594775232177325 4414016634223040712066497)
                    ·
                      refine ⟨3310512475667280534049873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414016634223040712066497 3310512475667280534049873)
                      ·
                        rfl

theorem cell23_6447200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_6447200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447200 prefixEnd_6447200 := by exact prefixLift 6447200
  have htrace : WordTrace (prefixWord ++ tailWord_6447200) baseStart_6447200 baseEnd_6447200 := by
    simpa [prefixWord, tailWord_6447200, baseEnd_6447200] using wordTrace_append hprefix tailTrace_6447200
  have hstable : (prefixWord ++ tailWord_6447200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447200).length < 2 ^ (prefixWord ++ tailWord_6447200).sum := by decide
  have hdescent : baseEnd_6447200 < baseStart_6447200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447207 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_6447207 : Nat := 118140960795 + 6447207 * 2 ^ 59
def prefixEnd_6447207 : Nat := 4983230072969 + 3 ^ 40 * 6447207 * 2
def baseEnd_6447207 : Nat := 3310516070031862006662341

theorem tailTrace_6447207 : CollatzResearch.WordTrace tailWord_6447207 prefixEnd_6447207 3310516070031862006662341 := by
  unfold tailWord_6447207
  simp only [CollatzResearch.WordTrace]
  refine ⟨235148957553877609138035875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156765971702585072758690583 235148957553877609138035875)
  ·
    refine ⟨352723436330816413707053813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235148957553877609138035875 352723436330816413707053813)
    ·
      refine ⟨33067822156014038785036295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352723436330816413707053813 33067822156014038785036295)
      ·
        refine ⟨49601733234021058177554443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33067822156014038785036295 49601733234021058177554443)
        ·
          refine ⟨74402599851031587266331665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49601733234021058177554443 74402599851031587266331665)
          ·
            refine ⟨55801949888273690449748749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74402599851031587266331665 55801949888273690449748749)
            ·
              refine ⟨20925731208102633918655781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55801949888273690449748749 20925731208102633918655781)
              ·
                refine ⟨3923574601519243859747959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20925731208102633918655781 3923574601519243859747959)
                ·
                  refine ⟨5885361902278865789621939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923574601519243859747959 5885361902278865789621939)
                  ·
                    refine ⟨8828042853418298684432909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5885361902278865789621939 8828042853418298684432909)
                    ·
                      refine ⟨3310516070031862006662341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8828042853418298684432909 3310516070031862006662341)
                      ·
                        rfl

theorem cell23_6447207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_6447207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447207 prefixEnd_6447207 := by exact prefixLift 6447207
  have htrace : WordTrace (prefixWord ++ tailWord_6447207) baseStart_6447207 baseEnd_6447207 := by
    simpa [prefixWord, tailWord_6447207, baseEnd_6447207] using wordTrace_append hprefix tailTrace_6447207
  have hstable : (prefixWord ++ tailWord_6447207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447207).length < 2 ^ (prefixWord ++ tailWord_6447207).sum := by decide
  have hdescent : baseEnd_6447207 < baseStart_6447207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447213 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6447213 : Nat := 118140960795 + 6447213 * 2 ^ 59
def prefixEnd_6447213 : Nat := 4983230072969 + 3 ^ 40 * 6447213 * 2
def baseEnd_6447213 : Nat := 3310519150915788983187313

theorem tailTrace_6447213 : CollatzResearch.WordTrace tailWord_6447213 prefixEnd_6447213 3310519150915788983187313 := by
  unfold tailWord_6447213
  simp only [CollatzResearch.WordTrace]
  refine ⟨235149176391855872162754293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156766117594570581441836195 235149176391855872162754293)
  ·
    refine ⟨22045235286736488015258215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235149176391855872162754293 22045235286736488015258215)
    ·
      refine ⟨33067852930104732022887323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22045235286736488015258215 33067852930104732022887323)
      ·
        refine ⟨49601779395157098034330985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33067852930104732022887323 49601779395157098034330985)
        ·
          refine ⟨37201334546367823525748239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49601779395157098034330985 37201334546367823525748239)
          ·
            refine ⟨55802001819551735288622359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37201334546367823525748239 55802001819551735288622359)
            ·
              refine ⟨83703002729327602932933539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55802001819551735288622359 83703002729327602932933539)
              ·
                refine ⟨125554504093991404399400309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83703002729327602932933539 125554504093991404399400309)
                ·
                  refine ⟨11770734758811694162443779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125554504093991404399400309 11770734758811694162443779)
                  ·
                    refine ⟨17656102138217541243665669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11770734758811694162443779 17656102138217541243665669)
                    ·
                      refine ⟨3310519150915788983187313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17656102138217541243665669 3310519150915788983187313)
                      ·
                        rfl

theorem cell23_6447213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6447213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447213 prefixEnd_6447213 := by exact prefixLift 6447213
  have htrace : WordTrace (prefixWord ++ tailWord_6447213) baseStart_6447213 baseEnd_6447213 := by
    simpa [prefixWord, tailWord_6447213, baseEnd_6447213] using wordTrace_append hprefix tailTrace_6447213
  have hstable : (prefixWord ++ tailWord_6447213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447213).length < 2 ^ (prefixWord ++ tailWord_6447213).sum := by decide
  have hdescent : baseEnd_6447213 < baseStart_6447213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447223 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 1, 6]
def baseStart_6447223 : Nat := 118140960795 + 6447223 * 2 ^ 59
def prefixEnd_6447223 : Nat := 4983230072969 + 3 ^ 40 * 6447223 * 2
def baseEnd_6447223 : Nat := 1103508095240777981354089

theorem tailTrace_6447223 : CollatzResearch.WordTrace tailWord_6447223 prefixEnd_6447223 1103508095240777981354089 := by
  unfold tailWord_6447223
  simp only [CollatzResearch.WordTrace]
  refine ⟨235149541121819643870618323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156766360747879762580412215 235149541121819643870618323)
  ·
    refine ⟨352724311682729465805927485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235149541121819643870618323 352724311682729465805927485)
    ·
      refine ⟨132271616881023549677222807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352724311682729465805927485 132271616881023549677222807)
      ·
        refine ⟨198407425321535324515834211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132271616881023549677222807 198407425321535324515834211)
        ·
          refine ⟨297611137982302986773751317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198407425321535324515834211 297611137982302986773751317)
          ·
            refine ⟨13950522092920452505019593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 297611137982302986773751317 13950522092920452505019593)
            ·
              refine ⟨10462891569690339378764695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13950522092920452505019593 10462891569690339378764695)
              ·
                refine ⟨15694337354535509068147043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462891569690339378764695 15694337354535509068147043)
                ·
                  refine ⟨23541506031803263602220565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15694337354535509068147043 23541506031803263602220565)
                  ·
                    refine ⟨1103508095240777981354089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23541506031803263602220565 1103508095240777981354089)
                    ·
                      rfl

theorem cell23_6447223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_6447223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447223 prefixEnd_6447223 := by exact prefixLift 6447223
  have htrace : WordTrace (prefixWord ++ tailWord_6447223) baseStart_6447223 baseEnd_6447223 := by
    simpa [prefixWord, tailWord_6447223, baseEnd_6447223] using wordTrace_append hprefix tailTrace_6447223
  have hstable : (prefixWord ++ tailWord_6447223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447223).length < 2 ^ (prefixWord ++ tailWord_6447223).sum := by decide
  have hdescent : baseEnd_6447223 < baseStart_6447223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447264 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 1, 2, 2]
def baseStart_6447264 : Nat := 118140960795 + 6447264 * 2 ^ 59
def prefixEnd_6447264 : Nat := 4983230072969 + 3 ^ 40 * 6447264 * 2
def baseEnd_6447264 : Nat := 3310545338429168283649579

theorem tailTrace_6447264 : CollatzResearch.WordTrace tailWord_6447264 prefixEnd_6447264 3310545338429168283649579 := by
  unfold tailWord_6447264
  simp only [CollatzResearch.WordTrace]
  refine ⟨117575518257335553936430423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156767357676447405248573897 117575518257335553936430423)
  ·
    refine ⟨176363277386003330904645635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117575518257335553936430423 176363277386003330904645635)
    ·
      refine ⟨264544916079004996356968453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176363277386003330904645635 264544916079004996356968453)
      ·
        refine ⟨49602171764813436816931585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264544916079004996356968453 49602171764813436816931585)
        ·
          refine ⟨37201628823610077612698689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49602171764813436816931585 37201628823610077612698689)
          ·
            refine ⟨27901221617707558209524017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37201628823610077612698689 27901221617707558209524017)
            ·
              refine ⟨20925916213280668657143013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27901221617707558209524017 20925916213280668657143013)
              ·
                refine ⟨3923609289990125373214315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20925916213280668657143013 3923609289990125373214315)
                ·
                  refine ⟨5885413934985188059821473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923609289990125373214315 5885413934985188059821473)
                  ·
                    refine ⟨4414060451238891044866105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5885413934985188059821473 4414060451238891044866105)
                    ·
                      refine ⟨3310545338429168283649579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414060451238891044866105 3310545338429168283649579)
                      ·
                        rfl

theorem cell23_6447264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_6447264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447264 prefixEnd_6447264 := by exact prefixLift 6447264
  have htrace : WordTrace (prefixWord ++ tailWord_6447264) baseStart_6447264 baseEnd_6447264 := by
    simpa [prefixWord, tailWord_6447264, baseEnd_6447264] using wordTrace_append hprefix tailTrace_6447264
  have hstable : (prefixWord ++ tailWord_6447264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447264).length < 2 ^ (prefixWord ++ tailWord_6447264).sum := by decide
  have hdescent : baseEnd_6447264 < baseStart_6447264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447274 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6447274 : Nat := 118140960795 + 6447274 * 2 ^ 59
def prefixEnd_6447274 : Nat := 4983230072969 + 3 ^ 40 * 6447274 * 2
def baseEnd_6447274 : Nat := 1103516824411904414841511

theorem tailTrace_6447274 : CollatzResearch.WordTrace tailWord_6447274 prefixEnd_6447274 1103516824411904414841511 := by
  unfold tailWord_6447274
  simp only [CollatzResearch.WordTrace]
  refine ⟨58787850311158719895181219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156767600829756586387149917 58787850311158719895181219)
  ·
    refine ⟨88181775466738079842771829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58787850311158719895181219 88181775466738079842771829)
    ·
      refine ⟨8267041450006694985259859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88181775466738079842771829 8267041450006694985259859)
      ·
        refine ⟨12400562175010042477889789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267041450006694985259859 12400562175010042477889789)
        ·
          refine ⟨4650210815628765929208671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12400562175010042477889789 4650210815628765929208671)
          ·
            refine ⟨6975316223443148893813007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650210815628765929208671 6975316223443148893813007)
            ·
              refine ⟨10462974335164723340719511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975316223443148893813007 10462974335164723340719511)
              ·
                refine ⟨15694461502747085011079267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462974335164723340719511 15694461502747085011079267)
                ·
                  refine ⟨23541692254120627516618901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15694461502747085011079267 23541692254120627516618901)
                  ·
                    refine ⟨1103516824411904414841511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23541692254120627516618901 1103516824411904414841511)
                    ·
                      rfl

theorem cell23_6447274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6447274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447274 prefixEnd_6447274 := by exact prefixLift 6447274
  have htrace : WordTrace (prefixWord ++ tailWord_6447274) baseStart_6447274 baseEnd_6447274 := by
    simpa [prefixWord, tailWord_6447274, baseEnd_6447274] using wordTrace_append hprefix tailTrace_6447274
  have hstable : (prefixWord ++ tailWord_6447274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447274).length < 2 ^ (prefixWord ++ tailWord_6447274).sum := by decide
  have hdescent : baseEnd_6447274 < baseStart_6447274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447277 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_6447277 : Nat := 118140960795 + 6447277 * 2 ^ 59
def prefixEnd_6447277 : Nat := 4983230072969 + 3 ^ 40 * 6447277 * 2
def baseEnd_6447277 : Nat := 3310552013677676732787019

theorem tailTrace_6447277 : CollatzResearch.WordTrace tailWord_6447277 prefixEnd_6447277 3310552013677676732787019 := by
  unfold tailWord_6447277
  simp only [CollatzResearch.WordTrace]
  refine ⟨235151510663624011093084085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156767673775749340728722723 235151510663624011093084085)
  ·
    refine ⟨22045454124714751039976633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235151510663624011093084085 22045454124714751039976633)
    ·
      refine ⟨16534090593536063279982475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22045454124714751039976633 16534090593536063279982475)
      ·
        refine ⟨24801135890304094919973713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534090593536063279982475 24801135890304094919973713)
        ·
          refine ⟨18600851917728071189980285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24801135890304094919973713 18600851917728071189980285)
          ·
            refine ⟨6975319469148026696242607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18600851917728071189980285 6975319469148026696242607)
            ·
              refine ⟨10462979203722040044363911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975319469148026696242607 10462979203722040044363911)
              ·
                refine ⟨15694468805583060066545867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462979203722040044363911 15694468805583060066545867)
                ·
                  refine ⟨23541703208374590099818801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15694468805583060066545867 23541703208374590099818801)
                  ·
                    refine ⟨17656277406280942574864101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23541703208374590099818801 17656277406280942574864101)
                    ·
                      refine ⟨3310552013677676732787019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17656277406280942574864101 3310552013677676732787019)
                      ·
                        rfl

theorem cell23_6447277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_6447277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447277 prefixEnd_6447277 := by exact prefixLift 6447277
  have htrace : WordTrace (prefixWord ++ tailWord_6447277) baseStart_6447277 baseEnd_6447277 := by
    simpa [prefixWord, tailWord_6447277, baseEnd_6447277] using wordTrace_append hprefix tailTrace_6447277
  have hstable : (prefixWord ++ tailWord_6447277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447277).length < 2 ^ (prefixWord ++ tailWord_6447277).sum := by decide
  have hdescent : baseEnd_6447277 < baseStart_6447277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447290 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2]
def baseStart_6447290 : Nat := 118140960795 + 6447290 * 2 ^ 59
def prefixEnd_6447290 : Nat := 4983230072969 + 3 ^ 40 * 6447290 * 2
def baseEnd_6447290 : Nat := 3310558688926185181924459

theorem tailTrace_6447290 : CollatzResearch.WordTrace tailWord_6447290 prefixEnd_6447290 3310558688926185181924459 := by
  unfold tailWord_6447290
  simp only [CollatzResearch.WordTrace]
  refine ⟨58787996203144228578326831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156767989875051276208871549 58787996203144228578326831)
  ·
    refine ⟨88181994304716342867490247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58787996203144228578326831 88181994304716342867490247)
    ·
      refine ⟨132272991457074514301235371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88181994304716342867490247 132272991457074514301235371)
      ·
        refine ⟨198409487185611771451853057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132272991457074514301235371 198409487185611771451853057)
        ·
          refine ⟨148807115389208828588889793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198409487185611771451853057 148807115389208828588889793)
          ·
            refine ⟨111605336541906621441667345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148807115389208828588889793 111605336541906621441667345)
            ·
              refine ⟨83704002406429966081250509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111605336541906621441667345 83704002406429966081250509)
              ·
                refine ⟨31389000902411237280468941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83704002406429966081250509 31389000902411237280468941)
                ·
                  refine ⟨11770875338404213980175853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31389000902411237280468941 11770875338404213980175853)
                  ·
                    refine ⟨4414078251901580242565945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11770875338404213980175853 4414078251901580242565945)
                    ·
                      refine ⟨3310558688926185181924459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414078251901580242565945 3310558688926185181924459)
                      ·
                        rfl

theorem cell23_6447290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_6447290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447290 prefixEnd_6447290 := by exact prefixLift 6447290
  have htrace : WordTrace (prefixWord ++ tailWord_6447290) baseStart_6447290 baseEnd_6447290 := by
    simpa [prefixWord, tailWord_6447290, baseEnd_6447290] using wordTrace_append hprefix tailTrace_6447290
  have hstable : (prefixWord ++ tailWord_6447290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447290).length < 2 ^ (prefixWord ++ tailWord_6447290).sum := by decide
  have hdescent : baseEnd_6447290 < baseStart_6447290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447337 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 2, 2, 2]
def baseStart_6447337 : Nat := 118140960795 + 6447337 * 2 ^ 59
def prefixEnd_6447337 : Nat := 4983230072969 + 3 ^ 40 * 6447337 * 2
def baseEnd_6447337 : Nat := 3310582822516946498036743

theorem tailTrace_6447337 : CollatzResearch.WordTrace tailWord_6447337 prefixEnd_6447337 3310582822516946498036743 := by
  unfold tailWord_6447337
  simp only [CollatzResearch.WordTrace]
  refine ⟨235153699043406641340268265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156769132695604427560178843 235153699043406641340268265)
  ·
    refine ⟨176365274282554981005201199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235153699043406641340268265 176365274282554981005201199)
    ·
      refine ⟨264547911423832471507801799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176365274282554981005201199 264547911423832471507801799)
      ·
        refine ⟨396821867135748707261702699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264547911423832471507801799 396821867135748707261702699)
        ·
          refine ⟨595232800703623060892554049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396821867135748707261702699 595232800703623060892554049)
          ·
            refine ⟨446424600527717295669415537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595232800703623060892554049 446424600527717295669415537)
            ·
              refine ⟨334818450395787971752061653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446424600527717295669415537 334818450395787971752061653)
              ·
                refine ⟨7847307431151280587938945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 334818450395787971752061653 7847307431151280587938945)
                ·
                  refine ⟨5885480573363460440954209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7847307431151280587938945 5885480573363460440954209)
                  ·
                    refine ⟨4414110430022595330715657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5885480573363460440954209 4414110430022595330715657)
                    ·
                      refine ⟨3310582822516946498036743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414110430022595330715657 3310582822516946498036743)
                      ·
                        rfl

theorem cell23_6447337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 2, 2].length) (baseStart_6447337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447337 prefixEnd_6447337 := by exact prefixLift 6447337
  have htrace : WordTrace (prefixWord ++ tailWord_6447337) baseStart_6447337 baseEnd_6447337 := by
    simpa [prefixWord, tailWord_6447337, baseEnd_6447337] using wordTrace_append hprefix tailTrace_6447337
  have hstable : (prefixWord ++ tailWord_6447337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447337).length < 2 ^ (prefixWord ++ tailWord_6447337).sum := by decide
  have hdescent : baseEnd_6447337 < baseStart_6447337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447341 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6447341 : Nat := 118140960795 + 6447341 * 2 ^ 59
def prefixEnd_6447341 : Nat := 4983230072969 + 3 ^ 40 * 6447341 * 2
def baseEnd_6447341 : Nat := 3310584876439564482386725

theorem tailTrace_6447341 : CollatzResearch.WordTrace tailWord_6447341 prefixEnd_6447341 3310584876439564482386725 := by
  unfold tailWord_6447341
  simp only [CollatzResearch.WordTrace]
  refine ⟨235153844935392150023413877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156769229956928100015609251 235153844935392150023413877)
  ·
    refine ⟨22045672962693014064695051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235153844935392150023413877 22045672962693014064695051)
    ·
      refine ⟨33068509444039521097042577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22045672962693014064695051 33068509444039521097042577)
      ·
        refine ⟨24801382083029640822781933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33068509444039521097042577 24801382083029640822781933)
        ·
          refine ⟨9300518281136115308543225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24801382083029640822781933 9300518281136115308543225)
          ·
            refine ⟨6975388710852086481407419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300518281136115308543225 6975388710852086481407419)
            ·
              refine ⟨10463083066278129722111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975388710852086481407419 10463083066278129722111129)
              ·
                refine ⟨7847312299708597291583347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10463083066278129722111129 7847312299708597291583347)
                ·
                  refine ⟨11770968449562895937375021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7847312299708597291583347 11770968449562895937375021)
                  ·
                    refine ⟨4414113168586085976515633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11770968449562895937375021 4414113168586085976515633)
                    ·
                      refine ⟨3310584876439564482386725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414113168586085976515633 3310584876439564482386725)
                      ·
                        rfl

theorem cell23_6447341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6447341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447341 prefixEnd_6447341 := by exact prefixLift 6447341
  have htrace : WordTrace (prefixWord ++ tailWord_6447341) baseStart_6447341 baseEnd_6447341 := by
    simpa [prefixWord, tailWord_6447341, baseEnd_6447341] using wordTrace_append hprefix tailTrace_6447341
  have hstable : (prefixWord ++ tailWord_6447341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447341).length < 2 ^ (prefixWord ++ tailWord_6447341).sum := by decide
  have hdescent : baseEnd_6447341 < baseStart_6447341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447353 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_6447353 : Nat := 118140960795 + 6447353 * 2 ^ 59
def prefixEnd_6447353 : Nat := 4983230072969 + 3 ^ 40 * 6447353 * 2
def baseEnd_6447353 : Nat := 3310591038207418435436669

theorem tailTrace_6447353 : CollatzResearch.WordTrace tailWord_6447353 prefixEnd_6447353 3310591038207418435436669 := by
  unfold tailWord_6447353
  simp only [CollatzResearch.WordTrace]
  refine ⟨235154282611348676072850713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156769521740899117381900475 235154282611348676072850713)
  ·
    refine ⟨176365711958511507054638035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235154282611348676072850713 176365711958511507054638035)
    ·
      refine ⟨264548567937767260581957053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176365711958511507054638035 264548567937767260581957053)
      ·
        refine ⟨99205712976662722718233895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264548567937767260581957053 99205712976662722718233895)
        ·
          refine ⟨148808569464994084077350843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99205712976662722718233895 148808569464994084077350843)
          ·
            refine ⟨223212854197491126116026265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148808569464994084077350843 223212854197491126116026265)
            ·
              refine ⟨167409640648118344587019699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223212854197491126116026265 167409640648118344587019699)
              ·
                refine ⟨251114460972177516880529549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167409640648118344587019699 251114460972177516880529549)
                ·
                  refine ⟨94167922864566568830198581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251114460972177516880529549 94167922864566568830198581)
                  ·
                    refine ⟨8828242768553115827831117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94167922864566568830198581 8828242768553115827831117)
                    ·
                      refine ⟨3310591038207418435436669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8828242768553115827831117 3310591038207418435436669)
                      ·
                        rfl

theorem cell23_6447353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_6447353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447353 prefixEnd_6447353 := by exact prefixLift 6447353
  have htrace : WordTrace (prefixWord ++ tailWord_6447353) baseStart_6447353 baseEnd_6447353 := by
    simpa [prefixWord, tailWord_6447353, baseEnd_6447353] using wordTrace_append hprefix tailTrace_6447353
  have hstable : (prefixWord ++ tailWord_6447353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447353).length < 2 ^ (prefixWord ++ tailWord_6447353).sum := by decide
  have hdescent : baseEnd_6447353 < baseStart_6447353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447377 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 5]
def baseStart_6447377 : Nat := 118140960795 + 6447377 * 2 ^ 59
def prefixEnd_6447377 : Nat := 4983230072969 + 3 ^ 40 * 6447377 * 2
def baseEnd_6447377 : Nat := 367844817971458482392951

theorem tailTrace_6447377 : CollatzResearch.WordTrace tailWord_6447377 prefixEnd_6447377 367844817971458482392951 := by
  unfold tailWord_6447377
  simp only [CollatzResearch.WordTrace]
  refine ⟨235155157963261728171724385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156770105308841152114482923 235155157963261728171724385)
  ·
    refine ⟨176366368472446296128793289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235155157963261728171724385 176366368472446296128793289)
    ·
      refine ⟨132274776354334722096594967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176366368472446296128793289 132274776354334722096594967)
      ·
        refine ⟨198412164531502083144892451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132274776354334722096594967 198412164531502083144892451)
        ·
          refine ⟨297618246797253124717338677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198412164531502083144892451 297618246797253124717338677)
          ·
            refine ⟨27901710637242480442250501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297618246797253124717338677 27901710637242480442250501)
            ·
              refine ⟨5231570744482965082921969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27901710637242480442250501 5231570744482965082921969)
              ·
                refine ⟨3923678058362223812191477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5231570744482965082921969 3923678058362223812191477)
                ·
                  refine ⟨367844817971458482392951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3923678058362223812191477 367844817971458482392951)
                  ·
                    rfl

theorem cell23_6447377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 5].length) (baseStart_6447377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447377 prefixEnd_6447377 := by exact prefixLift 6447377
  have htrace : WordTrace (prefixWord ++ tailWord_6447377) baseStart_6447377 baseEnd_6447377 := by
    simpa [prefixWord, tailWord_6447377, baseEnd_6447377] using wordTrace_append hprefix tailTrace_6447377
  have hstable : (prefixWord ++ tailWord_6447377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447377).length < 2 ^ (prefixWord ++ tailWord_6447377).sum := by decide
  have hdescent : baseEnd_6447377 < baseStart_6447377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447420 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_6447420 : Nat := 118140960795 + 6447420 * 2 ^ 59
def prefixEnd_6447420 : Nat := 4983230072969 + 3 ^ 40 * 6447420 * 2
def baseEnd_6447420 : Nat := 1103541813803756557766287

theorem tailTrace_6447420 : CollatzResearch.WordTrace tailWord_6447420 prefixEnd_6447420 1103541813803756557766287 := by
  unfold tailWord_6447420
  simp only [CollatzResearch.WordTrace]
  refine ⟨117578363151052973257769857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156771150868070631010359809 117578363151052973257769857)
  ·
    refine ⟨88183772363289729943327393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117578363151052973257769857 88183772363289729943327393)
    ·
      refine ⟨66137829272467297457495545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88183772363289729943327393 66137829272467297457495545)
      ·
        refine ⟨49603371954350473093121659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66137829272467297457495545 49603371954350473093121659)
        ·
          refine ⟨74405057931525709639682489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49603371954350473093121659 74405057931525709639682489)
          ·
            refine ⟨55803793448644282229761867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74405057931525709639682489 55803793448644282229761867)
            ·
              refine ⟨83705690172966423344642801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55803793448644282229761867 83705690172966423344642801)
              ·
                refine ⟨62779267629724817508482101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83705690172966423344642801 62779267629724817508482101)
                ·
                  refine ⟨5885556340286701641420197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62779267629724817508482101 5885556340286701641420197)
                  ·
                    refine ⟨1103541813803756557766287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885556340286701641420197 1103541813803756557766287)
                    ·
                      rfl

theorem cell23_6447420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_6447420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447420 prefixEnd_6447420 := by exact prefixLift 6447420
  have htrace : WordTrace (prefixWord ++ tailWord_6447420) baseStart_6447420 baseEnd_6447420 := by
    simpa [prefixWord, tailWord_6447420, baseEnd_6447420] using wordTrace_append hprefix tailTrace_6447420
  have hstable : (prefixWord ++ tailWord_6447420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447420).length < 2 ^ (prefixWord ++ tailWord_6447420).sum := by decide
  have hdescent : baseEnd_6447420 < baseStart_6447420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447423 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_6447423 : Nat := 118140960795 + 6447423 * 2 ^ 59
def prefixEnd_6447423 : Nat := 4983230072969 + 3 ^ 40 * 6447423 * 2
def baseEnd_6447423 : Nat := 3310626981853233161561347

theorem tailTrace_6447423 : CollatzResearch.WordTrace tailWord_6447423 prefixEnd_6447423 3310626981853233161561347 := by
  unfold tailWord_6447423
  simp only [CollatzResearch.WordTrace]
  refine ⟨235156835721095078027898923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156771223814063385351932615 235156835721095078027898923)
  ·
    refine ⟨352735253581642617041848385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235156835721095078027898923 352735253581642617041848385)
    ·
      refine ⟨264551440186231962781386289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352735253581642617041848385 264551440186231962781386289)
      ·
        refine ⟨198413580139673972086039717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264551440186231962781386289 198413580139673972086039717)
        ·
          refine ⟨37202546276188869766132447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198413580139673972086039717 37202546276188869766132447)
          ·
            refine ⟨55803819414283304649198671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37202546276188869766132447 55803819414283304649198671)
            ·
              refine ⟨83705729121424956973798007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55803819414283304649198671 83705729121424956973798007)
              ·
                refine ⟨125558593682137435460697011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83705729121424956973798007 125558593682137435460697011)
                ·
                  refine ⟨188337890523206153191045517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125558593682137435460697011 188337890523206153191045517)
                  ·
                    refine ⟨70626708946202307446642069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188337890523206153191045517 70626708946202307446642069)
                    ·
                      refine ⟨3310626981853233161561347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70626708946202307446642069 3310626981853233161561347)
                      ·
                        rfl

theorem cell23_6447423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_6447423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447423 prefixEnd_6447423 := by exact prefixLift 6447423
  have htrace : WordTrace (prefixWord ++ tailWord_6447423) baseStart_6447423 baseEnd_6447423 := by
    simpa [prefixWord, tailWord_6447423, baseEnd_6447423] using wordTrace_append hprefix tailTrace_6447423
  have hstable : (prefixWord ++ tailWord_6447423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447423).length < 2 ^ (prefixWord ++ tailWord_6447423).sum := by decide
  have hdescent : baseEnd_6447423 < baseStart_6447423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447460 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_6447460 : Nat := 118140960795 + 6447460 * 2 ^ 59
def prefixEnd_6447460 : Nat := 4983230072969 + 3 ^ 40 * 6447460 * 2
def baseEnd_6447460 : Nat := 3310645980637449516798677

theorem tailTrace_6447460 : CollatzResearch.WordTrace tailWord_6447460 prefixEnd_6447460 3310645980637449516798677 := by
  unfold tailWord_6447460
  simp only [CollatzResearch.WordTrace]
  refine ⟨117579092610980516673497917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156772123481307355564663889 117579092610980516673497917)
  ·
    refine ⟨44092159729117693752561719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117579092610980516673497917 44092159729117693752561719)
    ·
      refine ⟨66138239593676540628842579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44092159729117693752561719 66138239593676540628842579)
      ·
        refine ⟨99207359390514810943263869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66138239593676540628842579 99207359390514810943263869)
        ·
          refine ⟨37202759771443054103723951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99207359390514810943263869 37202759771443054103723951)
          ·
            refine ⟨55804139657164581155585927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37202759771443054103723951 55804139657164581155585927)
            ·
              refine ⟨83706209485746871733378891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55804139657164581155585927 83706209485746871733378891)
              ·
                refine ⟨125559314228620307600068337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83706209485746871733378891 125559314228620307600068337)
                ·
                  refine ⟨94169485671465230700051253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125559314228620307600068337 94169485671465230700051253)
                  ·
                    refine ⟨8828389281699865378129805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94169485671465230700051253 8828389281699865378129805)
                    ·
                      refine ⟨3310645980637449516798677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8828389281699865378129805 3310645980637449516798677)
                      ·
                        rfl

theorem cell23_6447460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_6447460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447460 prefixEnd_6447460 := by exact prefixLift 6447460
  have htrace : WordTrace (prefixWord ++ tailWord_6447460) baseStart_6447460 baseEnd_6447460 := by
    simpa [prefixWord, tailWord_6447460, baseEnd_6447460] using wordTrace_append hprefix tailTrace_6447460
  have hstable : (prefixWord ++ tailWord_6447460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447460).length < 2 ^ (prefixWord ++ tailWord_6447460).sum := by decide
  have hdescent : baseEnd_6447460 < baseStart_6447460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447487 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 2, 3, 2]
def baseStart_6447487 : Nat := 118140960795 + 6447487 * 2 ^ 59
def prefixEnd_6447487 : Nat := 4983230072969 + 3 ^ 40 * 6447487 * 2
def baseEnd_6447487 : Nat := 3310659844615120911161053

theorem tailTrace_6447487 : CollatzResearch.WordTrace tailWord_6447487 prefixEnd_6447487 3310659844615120911161053 := by
  unfold tailWord_6447487
  simp only [CollatzResearch.WordTrace]
  refine ⟨235159169992863216958228715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156772779995242144638819143 235159169992863216958228715)
  ·
    refine ⟨352738754989294825437343073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235159169992863216958228715 352738754989294825437343073)
    ·
      refine ⟨264554066241971119078007305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352738754989294825437343073 264554066241971119078007305)
      ·
        refine ⟨198415549681478339308505479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264554066241971119078007305 198415549681478339308505479)
        ·
          refine ⟨297623324522217508962758219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198415549681478339308505479 297623324522217508962758219)
          ·
            refine ⟨446434986783326263444137329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297623324522217508962758219 446434986783326263444137329)
            ·
              refine ⟨334826240087494697583102997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446434986783326263444137329 334826240087494697583102997)
              ·
                refine ⟨15694980004101313949207953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 334826240087494697583102997 15694980004101313949207953)
                ·
                  refine ⟨11771235003075985461905965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15694980004101313949207953 11771235003075985461905965)
                  ·
                    refine ⟨4414213126153494548214737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11771235003075985461905965 4414213126153494548214737)
                    ·
                      refine ⟨3310659844615120911161053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4414213126153494548214737 3310659844615120911161053)
                      ·
                        rfl

theorem cell23_6447487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_6447487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447487 prefixEnd_6447487 := by exact prefixLift 6447487
  have htrace : WordTrace (prefixWord ++ tailWord_6447487) baseStart_6447487 baseEnd_6447487 := by
    simpa [prefixWord, tailWord_6447487, baseEnd_6447487] using wordTrace_append hprefix tailTrace_6447487
  have hstable : (prefixWord ++ tailWord_6447487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447487).length < 2 ^ (prefixWord ++ tailWord_6447487).sum := by decide
  have hdescent : baseEnd_6447487 < baseStart_6447487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447514 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_6447514 : Nat := 118140960795 + 6447514 * 2 ^ 59
def prefixEnd_6447514 : Nat := 4983230072969 + 3 ^ 40 * 6447514 * 2
def baseEnd_6447514 : Nat := 1103557902864264101841143

theorem tailTrace_6447514 : CollatzResearch.WordTrace tailWord_6447514 prefixEnd_6447514 1103557902864264101841143 := by
  unfold tailWord_6447514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58790038690941350142365399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156773436509176933712974397 58790038690941350142365399)
  ·
    refine ⟨88185058036412025213548099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58790038690941350142365399 88185058036412025213548099)
    ·
      refine ⟨132277587054618037820322149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88185058036412025213548099 132277587054618037820322149)
      ·
        refine ⟨24802047572740882091310403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132277587054618037820322149 24802047572740882091310403)
        ·
          refine ⟨37203071359111323136965605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802047572740882091310403 37203071359111323136965605)
          ·
            refine ⟨6975575879833373088181051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37203071359111323136965605 6975575879833373088181051)
            ·
              refine ⟨10463363819750059632271577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975575879833373088181051 10463363819750059632271577)
              ·
                refine ⟨7847522864812544724203683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10463363819750059632271577 7847522864812544724203683)
                ·
                  refine ⟨11771284297218817086305525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7847522864812544724203683 11771284297218817086305525)
                  ·
                    refine ⟨1103557902864264101841143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11771284297218817086305525 1103557902864264101841143)
                    ·
                      rfl

theorem cell23_6447514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_6447514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447514 prefixEnd_6447514 := by exact prefixLift 6447514
  have htrace : WordTrace (prefixWord ++ tailWord_6447514) baseStart_6447514 baseEnd_6447514 := by
    simpa [prefixWord, tailWord_6447514, baseEnd_6447514] using wordTrace_append hprefix tailTrace_6447514
  have hstable : (prefixWord ++ tailWord_6447514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447514).length < 2 ^ (prefixWord ++ tailWord_6447514).sum := by decide
  have hdescent : baseEnd_6447514 < baseStart_6447514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447527 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6447527 : Nat := 118140960795 + 6447527 * 2 ^ 59
def prefixEnd_6447527 : Nat := 4983230072969 + 3 ^ 40 * 6447527 * 2
def baseEnd_6447527 : Nat := 1103560127947100251553623

theorem tailTrace_6447527 : CollatzResearch.WordTrace tailWord_6447527 prefixEnd_6447527 1103560127947100251553623 := by
  unfold tailWord_6447527
  simp only [CollatzResearch.WordTrace]
  refine ⟨235160628912718303789684835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156773752608478869193123223 235160628912718303789684835)
  ·
    refine ⟨352740943369077455684527253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235160628912718303789684835 352740943369077455684527253)
    ·
      refine ⟨16534731720425505735212215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 352740943369077455684527253 16534731720425505735212215)
      ·
        refine ⟨24802097580638258602818323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534731720425505735212215 24802097580638258602818323)
        ·
          refine ⟨37203146370957387904227485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802097580638258602818323 37203146370957387904227485)
          ·
            refine ⟨13951179889109020464085307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37203146370957387904227485 13951179889109020464085307)
            ·
              refine ⟨20926769833663530696127961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13951179889109020464085307 20926769833663530696127961)
              ·
                refine ⟨15695077375247648022095971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20926769833663530696127961 15695077375247648022095971)
                ·
                  refine ⟨23542616062871472033143957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15695077375247648022095971 23542616062871472033143957)
                  ·
                    refine ⟨1103560127947100251553623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23542616062871472033143957 1103560127947100251553623)
                    ·
                      rfl

theorem cell23_6447527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6447527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447527 prefixEnd_6447527 := by exact prefixLift 6447527
  have htrace : WordTrace (prefixWord ++ tailWord_6447527) baseStart_6447527 baseEnd_6447527 := by
    simpa [prefixWord, tailWord_6447527, baseEnd_6447527] using wordTrace_append hprefix tailTrace_6447527
  have hstable : (prefixWord ++ tailWord_6447527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447527).length < 2 ^ (prefixWord ++ tailWord_6447527).sum := by decide
  have hdescent : baseEnd_6447527 < baseStart_6447527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447537 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_6447537 : Nat := 118140960795 + 6447537 * 2 ^ 59
def prefixEnd_6447537 : Nat := 4983230072969 + 3 ^ 40 * 6447537 * 2
def baseEnd_6447537 : Nat := 3310685518647845715535823

theorem tailTrace_6447537 : CollatzResearch.WordTrace tailWord_6447537 prefixEnd_6447537 3310685518647845715535823 := by
  unfold tailWord_6447537
  simp only [CollatzResearch.WordTrace]
  refine ⟨235160993642682075497548865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156773995761788050331699243 235160993642682075497548865)
  ·
    refine ⟨176370745232011556623161649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235160993642682075497548865 176370745232011556623161649)
    ·
      refine ⟨132278058924008667467371237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176370745232011556623161649 132278058924008667467371237)
      ·
        refine ⟨24802136048251625150132107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132278058924008667467371237 24802136048251625150132107)
        ·
          refine ⟨37203204072377437725198161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802136048251625150132107 37203204072377437725198161)
          ·
            refine ⟨27902403054283078293898621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37203204072377437725198161 27902403054283078293898621)
            ·
              refine ⟨10463401145356154360211983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27902403054283078293898621 10463401145356154360211983)
              ·
                refine ⟨15695101718034231540317975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10463401145356154360211983 15695101718034231540317975)
                ·
                  refine ⟨23542652577051347310476963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15695101718034231540317975 23542652577051347310476963)
                  ·
                    refine ⟨35313978865577020965715445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23542652577051347310476963 35313978865577020965715445)
                    ·
                      refine ⟨3310685518647845715535823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35313978865577020965715445 3310685518647845715535823)
                      ·
                        rfl

theorem cell23_6447537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_6447537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447537 prefixEnd_6447537 := by exact prefixLift 6447537
  have htrace : WordTrace (prefixWord ++ tailWord_6447537) baseStart_6447537 baseEnd_6447537 := by
    simpa [prefixWord, tailWord_6447537, baseEnd_6447537] using wordTrace_append hprefix tailTrace_6447537
  have hstable : (prefixWord ++ tailWord_6447537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447537).length < 2 ^ (prefixWord ++ tailWord_6447537).sum := by decide
  have hdescent : baseEnd_6447537 < baseStart_6447537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447564 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6447564 : Nat := 118140960795 + 6447564 * 2 ^ 59
def prefixEnd_6447564 : Nat := 4983230072969 + 3 ^ 40 * 6447564 * 2
def baseEnd_6447564 : Nat := 3310699382625517109898199

theorem tailTrace_6447564 : CollatzResearch.WordTrace tailWord_6447564 prefixEnd_6447564 3310699382625517109898199 := by
  unfold tailWord_6447564
  simp only [CollatzResearch.WordTrace]
  refine ⟨117580989206792129554390873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156774652275722839405854497 117580989206792129554390873)
  ·
    refine ⟨88185741905094097165793155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117580989206792129554390873 88185741905094097165793155)
    ·
      refine ⟨132278612857641145748689733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88185741905094097165793155 132278612857641145748689733)
      ·
        refine ⟨24802239910807714827879325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132278612857641145748689733 24802239910807714827879325)
        ·
          refine ⟨9300839966552893060454747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24802239910807714827879325 9300839966552893060454747)
          ·
            refine ⟨13951259949829339590682121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9300839966552893060454747 13951259949829339590682121)
            ·
              refine ⟨10463444962372004693011591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13951259949829339590682121 10463444962372004693011591)
              ·
                refine ⟨15695167443558007039517387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10463444962372004693011591 15695167443558007039517387)
                ·
                  refine ⟨23542751165337010559276081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15695167443558007039517387 23542751165337010559276081)
                  ·
                    refine ⟨17657063374002757919457061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23542751165337010559276081 17657063374002757919457061)
                    ·
                      refine ⟨3310699382625517109898199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17657063374002757919457061 3310699382625517109898199)
                      ·
                        rfl

theorem cell23_6447564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6447564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447564 prefixEnd_6447564 := by exact prefixLift 6447564
  have htrace : WordTrace (prefixWord ++ tailWord_6447564) baseStart_6447564 baseEnd_6447564 := by
    simpa [prefixWord, tailWord_6447564, baseEnd_6447564] using wordTrace_append hprefix tailTrace_6447564
  have hstable : (prefixWord ++ tailWord_6447564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447564).length < 2 ^ (prefixWord ++ tailWord_6447564).sum := by decide
  have hdescent : baseEnd_6447564 < baseStart_6447564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447567 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 3]
def baseStart_6447567 : Nat := 118140960795 + 6447567 * 2 ^ 59
def prefixEnd_6447567 : Nat := 4983230072969 + 3 ^ 40 * 6447567 * 2
def baseEnd_6447567 : Nat := 3310700923067480598160685

theorem tailTrace_6447567 : CollatzResearch.WordTrace tailWord_6447567 prefixEnd_6447567 3310700923067480598160685 := by
  unfold tailWord_6447567
  simp only [CollatzResearch.WordTrace]
  refine ⟨235162087832573390621140955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156774725221715593747427303 235162087832573390621140955)
  ·
    refine ⟨352743131748860085931711433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235162087832573390621140955 352743131748860085931711433)
    ·
      refine ⟨264557348811645064448783575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352743131748860085931711433 264557348811645064448783575)
      ·
        refine ⟨396836023217467596673175363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264557348811645064448783575 396836023217467596673175363)
        ·
          refine ⟨595254034826201395009763045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396836023217467596673175363 595254034826201395009763045)
          ·
            refine ⟨111610131529912761564330571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 595254034826201395009763045 111610131529912761564330571)
            ·
              refine ⟨167415197294869142346495857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111610131529912761564330571 167415197294869142346495857)
              ·
                refine ⟨125561397971151856759871893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167415197294869142346495857 125561397971151856759871893)
                ·
                  refine ⟨5885690529897743285618995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125561397971151856759871893 5885690529897743285618995)
                  ·
                    refine ⟨8828535794846614928428493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5885690529897743285618995 8828535794846614928428493)
                    ·
                      refine ⟨3310700923067480598160685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8828535794846614928428493 3310700923067480598160685)
                      ·
                        rfl

theorem cell23_6447567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_6447567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447567 prefixEnd_6447567 := by exact prefixLift 6447567
  have htrace : WordTrace (prefixWord ++ tailWord_6447567) baseStart_6447567 baseEnd_6447567 := by
    simpa [prefixWord, tailWord_6447567, baseEnd_6447567] using wordTrace_append hprefix tailTrace_6447567
  have hstable : (prefixWord ++ tailWord_6447567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447567).length < 2 ^ (prefixWord ++ tailWord_6447567).sum := by decide
  have hdescent : baseEnd_6447567 < baseStart_6447567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447574 : List Nat := [5, 2, 1, 1, 1, 1, 5, 7]
def baseStart_6447574 : Nat := 118140960795 + 6447574 * 2 ^ 59
def prefixEnd_6447574 : Nat := 4983230072969 + 3 ^ 40 * 6447574 * 2
def baseEnd_6447574 : Nat := 122618685830817113732339

theorem tailTrace_6447574 : CollatzResearch.WordTrace tailWord_6447574 prefixEnd_6447574 122618685830817113732339 := by
  unfold tailWord_6447574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697646446471751926040361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156774895429032020544430517 14697646446471751926040361)
  ·
    refine ⟨11023234834853813944530271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14697646446471751926040361 11023234834853813944530271)
    ·
      refine ⟨16534852252280720916795407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023234834853813944530271 16534852252280720916795407)
      ·
        refine ⟨24802278378421081375193111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534852252280720916795407 24802278378421081375193111)
        ·
          refine ⟨37203417567631622062789667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802278378421081375193111 37203417567631622062789667)
          ·
            refine ⟨55805126351447433094184501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37203417567631622062789667 55805126351447433094184501)
            ·
              refine ⟨5231730595448196852579797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55805126351447433094184501 5231730595448196852579797)
              ·
                refine ⟨122618685830817113732339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5231730595448196852579797 122618685830817113732339)
                ·
                  rfl

theorem cell23_6447574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_6447574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447574 prefixEnd_6447574 := by exact prefixLift 6447574
  have htrace : WordTrace (prefixWord ++ tailWord_6447574) baseStart_6447574 baseEnd_6447574 := by
    simpa [prefixWord, tailWord_6447574, baseEnd_6447574] using wordTrace_append hprefix tailTrace_6447574
  have hstable : (prefixWord ++ tailWord_6447574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447574).length < 2 ^ (prefixWord ++ tailWord_6447574).sum := by decide
  have hdescent : baseEnd_6447574 < baseStart_6447574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447600 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_6447600 : Nat := 118140960795 + 6447600 * 2 ^ 59
def prefixEnd_6447600 : Nat := 4983230072969 + 3 ^ 40 * 6447600 * 2
def baseEnd_6447600 : Nat := 1103572622643026323016011

theorem tailTrace_6447600 : CollatzResearch.WordTrace tailWord_6447600 prefixEnd_6447600 1103572622643026323016011 := by
  unfold tailWord_6447600
  simp only [CollatzResearch.WordTrace]
  refine ⟨117581645720726918628546127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156775527627635891504728169 117581645720726918628546127)
  ·
    refine ⟨176372468581090377942819191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117581645720726918628546127 176372468581090377942819191)
    ·
      refine ⟨264558702871635566914228787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176372468581090377942819191 264558702871635566914228787)
      ·
        refine ⟨396838054307453350371343181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264558702871635566914228787 396838054307453350371343181)
        ·
          refine ⟨148814270365295006389253693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396838054307453350371343181 148814270365295006389253693)
          ·
            refine ⟨55805351386985627395970135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148814270365295006389253693 55805351386985627395970135)
            ·
              refine ⟨83708027080478441093955203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55805351386985627395970135 83708027080478441093955203)
              ·
                refine ⟨125562040620717661640932805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83708027080478441093955203 125562040620717661640932805)
                ·
                  refine ⟨23542882616384561557674901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125562040620717661640932805 23542882616384561557674901)
                  ·
                    refine ⟨1103572622643026323016011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23542882616384561557674901 1103572622643026323016011)
                    ·
                      rfl

theorem cell23_6447600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_6447600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447600 prefixEnd_6447600 := by exact prefixLift 6447600
  have htrace : WordTrace (prefixWord ++ tailWord_6447600) baseStart_6447600 baseEnd_6447600 := by
    simpa [prefixWord, tailWord_6447600, baseEnd_6447600] using wordTrace_append hprefix tailTrace_6447600
  have hstable : (prefixWord ++ tailWord_6447600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447600).length < 2 ^ (prefixWord ++ tailWord_6447600).sum := by decide
  have hdescent : baseEnd_6447600 < baseStart_6447600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6447610 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_6447610 : Nat := 118140960795 + 6447610 * 2 ^ 59
def prefixEnd_6447610 : Nat := 4983230072969 + 3 ^ 40 * 6447610 * 2
def baseEnd_6447610 : Nat := 3310723002735623929922987

theorem tailTrace_6447610 : CollatzResearch.WordTrace tailWord_6447610 prefixEnd_6447610 3310723002735623929922987 := by
  unfold tailWord_6447610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58790914042854402241239071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156775770780945072643304189 58790914042854402241239071)
  ·
    refine ⟨88186371064281603361858607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58790914042854402241239071 88186371064281603361858607)
    ·
      refine ⟨132279556596422405042787911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88186371064281603361858607 132279556596422405042787911)
      ·
        refine ⟨198419334894633607564181867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132279556596422405042787911 198419334894633607564181867)
        ·
          refine ⟨297629002341950411346272801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198419334894633607564181867 297629002341950411346272801)
          ·
            refine ⟨223221751756462808509704601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297629002341950411346272801 223221751756462808509704601)
            ·
              refine ⟨167416313817347106382278451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223221751756462808509704601 167416313817347106382278451)
              ·
                refine ⟨251124470726020659573417677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167416313817347106382278451 251124470726020659573417677)
                ·
                  refine ⟨94171676522257747340031629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251124470726020659573417677 94171676522257747340031629)
                  ·
                    refine ⟨35314378695846655252511861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94171676522257747340031629 35314378695846655252511861)
                    ·
                      refine ⟨3310723002735623929922987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35314378695846655252511861 3310723002735623929922987)
                      ·
                        rfl

theorem cell23_6447610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_6447610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6447610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6447610 prefixEnd_6447610 := by exact prefixLift 6447610
  have htrace : WordTrace (prefixWord ++ tailWord_6447610) baseStart_6447610 baseEnd_6447610 := by
    simpa [prefixWord, tailWord_6447610, baseEnd_6447610] using wordTrace_append hprefix tailTrace_6447610
  have hstable : (prefixWord ++ tailWord_6447610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6447610).length < 2 ^ (prefixWord ++ tailWord_6447610).sum := by decide
  have hdescent : baseEnd_6447610 < baseStart_6447610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6447610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
