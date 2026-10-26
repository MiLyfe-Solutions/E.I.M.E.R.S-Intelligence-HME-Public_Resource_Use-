import V185TrunkScan23Chunk0642

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3802346 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_3802346 : Nat := 118140960795 + 3802346 * 2 ^ 59
def prefixEnd_3802346 : Nat := 4983230072969 + 3 ^ 40 * 3802346 * 2
def baseEnd_3802346 : Nat := 1952431112700685537488335

theorem tailTrace_3802346 : CollatzResearch.WordTrace tailWord_3802346 prefixEnd_3802346 1952431112700685537488335 := by
  unfold tailWord_3802346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34670737970689326460352723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92455301255171537227607261 34670737970689326460352723)
  ·
    refine ⟨52006106956033989690529085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34670737970689326460352723 52006106956033989690529085)
    ·
      refine ⟨19502290108512746133948407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52006106956033989690529085 19502290108512746133948407)
      ·
        refine ⟨29253435162769119200922611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19502290108512746133948407 29253435162769119200922611)
        ·
          refine ⟨43880152744153678801383917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29253435162769119200922611 43880152744153678801383917)
          ·
            refine ⟨16455057279057629550518969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43880152744153678801383917 16455057279057629550518969)
            ·
              refine ⟨12341292959293222162889227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16455057279057629550518969 12341292959293222162889227)
              ·
                refine ⟨18511939438939833244333841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12341292959293222162889227 18511939438939833244333841)
                ·
                  refine ⟨13883954579204874933250381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18511939438939833244333841 13883954579204874933250381)
                  ·
                    refine ⟨5206482967201828099968893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13883954579204874933250381 5206482967201828099968893)
                    ·
                      refine ⟨1952431112700685537488335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206482967201828099968893 1952431112700685537488335)
                      ·
                        rfl

theorem cell23_3802346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_3802346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802346 prefixEnd_3802346 := by exact prefixLift 3802346
  have htrace : WordTrace (prefixWord ++ tailWord_3802346) baseStart_3802346 baseEnd_3802346 := by
    simpa [prefixWord, tailWord_3802346, baseEnd_3802346] using wordTrace_append hprefix tailTrace_3802346
  have hstable : (prefixWord ++ tailWord_3802346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802346).length < 2 ^ (prefixWord ++ tailWord_3802346).sum := by decide
  have hdescent : baseEnd_3802346 < baseStart_3802346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802366 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3802366 : Nat := 118140960795 + 3802366 * 2 ^ 59
def prefixEnd_3802366 : Nat := 4983230072969 + 3 ^ 40 * 3802366 * 2
def baseEnd_3802366 : Nat := 650813794104591819746081

theorem tailTrace_3802366 : CollatzResearch.WordTrace tailWord_3802366 prefixEnd_3802366 650813794104591819746081 := by
  unfold tailWord_3802366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335460167835606157142369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92455787561789899504759301 17335460167835606157142369)
  ·
    refine ⟨13001595125876704617856777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17335460167835606157142369 13001595125876704617856777)
    ·
      refine ⟨9751196344407528463392583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13001595125876704617856777 9751196344407528463392583)
      ·
        refine ⟨14626794516611292695088875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751196344407528463392583 14626794516611292695088875)
        ·
          refine ⟨21940191774916939042633313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14626794516611292695088875 21940191774916939042633313)
          ·
            refine ⟨16455143831187704281974985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21940191774916939042633313 16455143831187704281974985)
            ·
              refine ⟨12341357873390778211481239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16455143831187704281974985 12341357873390778211481239)
              ·
                refine ⟨18512036810086167317221859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12341357873390778211481239 18512036810086167317221859)
                ·
                  refine ⟨27768055215129250975832789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18512036810086167317221859 27768055215129250975832789)
                  ·
                    refine ⟨650813794104591819746081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27768055215129250975832789 650813794104591819746081)
                    ·
                      rfl

theorem cell23_3802366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3802366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802366 prefixEnd_3802366 := by exact prefixLift 3802366
  have htrace : WordTrace (prefixWord ++ tailWord_3802366) baseStart_3802366 baseEnd_3802366 := by
    simpa [prefixWord, tailWord_3802366, baseEnd_3802366] using wordTrace_append hprefix tailTrace_3802366
  have hstable : (prefixWord ++ tailWord_3802366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802366).length < 2 ^ (prefixWord ++ tailWord_3802366).sum := by decide
  have hdescent : baseEnd_3802366 < baseStart_3802366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802398 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3802398 : Nat := 118140960795 + 3802398 * 2 ^ 59
def prefixEnd_3802398 : Nat := 4983230072969 + 3 ^ 40 * 3802398 * 2
def baseEnd_3802398 : Nat := 1952457813694719334038097

theorem tailTrace_3802398 : CollatzResearch.WordTrace tailWord_3802398 prefixEnd_3802398 1952457813694719334038097 := by
  unfold tailWord_3802398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335606059821114840287981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92456565652379279148202565 17335606059821114840287981)
  ·
    refine ⟨6500852272432918065107993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17335606059821114840287981 6500852272432918065107993)
    ·
      refine ⟨4875639204324688548830995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6500852272432918065107993 4875639204324688548830995)
      ·
        refine ⟨7313458806487032823246493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875639204324688548830995 7313458806487032823246493)
        ·
          refine ⟨2742547052432637308717435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7313458806487032823246493 2742547052432637308717435)
          ·
            refine ⟨4113820578648955963076153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742547052432637308717435 4113820578648955963076153)
            ·
              refine ⟨3085365433986716972307115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113820578648955963076153 3085365433986716972307115)
              ·
                refine ⟨4628048150980075458460673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085365433986716972307115 4628048150980075458460673)
                ·
                  refine ⟨3471036113235056593845505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4628048150980075458460673 3471036113235056593845505)
                  ·
                    refine ⟨2603277084926292445384129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3471036113235056593845505 2603277084926292445384129)
                    ·
                      refine ⟨1952457813694719334038097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603277084926292445384129 1952457813694719334038097)
                      ·
                        rfl

theorem cell23_3802398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3802398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802398 prefixEnd_3802398 := by exact prefixLift 3802398
  have htrace : WordTrace (prefixWord ++ tailWord_3802398) baseStart_3802398 baseEnd_3802398 := by
    simpa [prefixWord, tailWord_3802398, baseEnd_3802398] using wordTrace_append hprefix tailTrace_3802398
  have hstable : (prefixWord ++ tailWord_3802398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802398).length < 2 ^ (prefixWord ++ tailWord_3802398).sum := by decide
  have hdescent : baseEnd_3802398 < baseStart_3802398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802430 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3802430 : Nat := 118140960795 + 3802430 * 2 ^ 59
def prefixEnd_3802430 : Nat := 4983230072969 + 3 ^ 40 * 3802430 * 2
def baseEnd_3802430 : Nat := 650824748358554402945983

theorem tailTrace_3802430 : CollatzResearch.WordTrace tailWord_3802430 prefixEnd_3802430 650824748358554402945983 := by
  unfold tailWord_3802430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335751951806623523433593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92457343742968658791645829 17335751951806623523433593)
  ·
    refine ⟨13001813963854967642575195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17335751951806623523433593 13001813963854967642575195)
    ·
      refine ⟨19502720945782451463862793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001813963854967642575195 19502720945782451463862793)
      ·
        refine ⟨14627040709336838597897095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19502720945782451463862793 14627040709336838597897095)
        ·
          refine ⟨21940561064005257896845643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14627040709336838597897095 21940561064005257896845643)
          ·
            refine ⟨32910841596007886845268465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21940561064005257896845643 32910841596007886845268465)
            ·
              refine ⟨24683131197005915133951349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32910841596007886845268465 24683131197005915133951349)
              ·
                refine ⟨2314043549719304543807939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24683131197005915133951349 2314043549719304543807939)
                ·
                  refine ⟨3471065324578956815711909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314043549719304543807939 3471065324578956815711909)
                  ·
                    refine ⟨650824748358554402945983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471065324578956815711909 650824748358554402945983)
                    ·
                      rfl

theorem cell23_3802430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3802430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802430 prefixEnd_3802430 := by exact prefixLift 3802430
  have htrace : WordTrace (prefixWord ++ tailWord_3802430) baseStart_3802430 baseEnd_3802430 := by
    simpa [prefixWord, tailWord_3802430, baseEnd_3802430] using wordTrace_append hprefix tailTrace_3802430
  have hstable : (prefixWord ++ tailWord_3802430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802430).length < 2 ^ (prefixWord ++ tailWord_3802430).sum := by decide
  have hdescent : baseEnd_3802430 < baseStart_3802430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802466 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3802466 : Nat := 118140960795 + 3802466 * 2 ^ 59
def prefixEnd_3802466 : Nat := 4983230072969 + 3 ^ 40 * 3802466 * 2
def baseEnd_3802466 : Nat := 1952492730379225067987783

theorem tailTrace_3802466 : CollatzResearch.WordTrace tailWord_3802466 prefixEnd_3802466 1952492730379225067987783 := by
  unfold tailWord_3802466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34671832160580641583944813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92458219094881710890519501 34671832160580641583944813)
  ·
    refine ⟨13001937060217740593979305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34671832160580641583944813 13001937060217740593979305)
    ·
      refine ⟨9751452795163305445484479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13001937060217740593979305 9751452795163305445484479)
      ·
        refine ⟨14627179192744958168226719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751452795163305445484479 14627179192744958168226719)
        ·
          refine ⟨21940768789117437252340079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14627179192744958168226719 21940768789117437252340079)
          ·
            refine ⟨32911153183676155878510119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21940768789117437252340079 32911153183676155878510119)
            ·
              refine ⟨49366729775514233817765179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32911153183676155878510119 49366729775514233817765179)
              ·
                refine ⟨74050094663271350726647769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49366729775514233817765179 74050094663271350726647769)
                ·
                  refine ⟨55537570997453513044985827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74050094663271350726647769 55537570997453513044985827)
                  ·
                    refine ⟨83306356496180269567478741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55537570997453513044985827 83306356496180269567478741)
                    ·
                      refine ⟨1952492730379225067987783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83306356496180269567478741 1952492730379225067987783)
                      ·
                        rfl

theorem cell23_3802466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3802466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802466 prefixEnd_3802466 := by exact prefixLift 3802466
  have htrace : WordTrace (prefixWord ++ tailWord_3802466) baseStart_3802466 baseEnd_3802466 := by
    simpa [prefixWord, tailWord_3802466, baseEnd_3802466] using wordTrace_append hprefix tailTrace_3802466
  have hstable : (prefixWord ++ tailWord_3802466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802466).length < 2 ^ (prefixWord ++ tailWord_3802466).sum := by decide
  have hdescent : baseEnd_3802466 < baseStart_3802466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802493 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_3802493 : Nat := 118140960795 + 3802493 * 2 ^ 59
def prefixEnd_3802493 : Nat := 4983230072969 + 3 ^ 40 * 3802493 * 2
def baseEnd_3802493 : Nat := 1952506594356896462350159

theorem tailTrace_3802493 : CollatzResearch.WordTrace tailWord_3802493 prefixEnd_3802493 1952506594356896462350159 := by
  unfold tailWord_3802493
  simp only [CollatzResearch.WordTrace]
  refine ⟨138688313413224749947012133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92458875608816499964674755 138688313413224749947012133)
  ·
    refine ⟨26004058764979640615064775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138688313413224749947012133 26004058764979640615064775)
    ·
      refine ⟨39006088147469460922597163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26004058764979640615064775 39006088147469460922597163)
      ·
        refine ⟨58509132221204191383895745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39006088147469460922597163 58509132221204191383895745)
        ·
          refine ⟨43881849165903143537921809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58509132221204191383895745 43881849165903143537921809)
          ·
            refine ⟨32911386874427357653441357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43881849165903143537921809 32911386874427357653441357)
            ·
              refine ⟨12341770077910259120040509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32911386874427357653441357 12341770077910259120040509)
              ·
                refine ⟨4628163779216347170015191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12341770077910259120040509 4628163779216347170015191)
                ·
                  refine ⟨6942245668824520755022787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628163779216347170015191 6942245668824520755022787)
                  ·
                    refine ⟨10413368503236781132534181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6942245668824520755022787 10413368503236781132534181)
                    ·
                      refine ⟨1952506594356896462350159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10413368503236781132534181 1952506594356896462350159)
                      ·
                        rfl

theorem cell23_3802493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_3802493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802493 prefixEnd_3802493 := by exact prefixLift 3802493
  have htrace : WordTrace (prefixWord ++ tailWord_3802493) baseStart_3802493 baseEnd_3802493 := by
    simpa [prefixWord, tailWord_3802493, baseEnd_3802493] using wordTrace_append hprefix tailTrace_3802493
  have hstable : (prefixWord ++ tailWord_3802493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802493).length < 2 ^ (prefixWord ++ tailWord_3802493).sum := by decide
  have hdescent : baseEnd_3802493 < baseStart_3802493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802494 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3802494 : Nat := 118140960795 + 3802494 * 2 ^ 59
def prefixEnd_3802494 : Nat := 4983230072969 + 3 ^ 40 * 3802494 * 2
def baseEnd_3802494 : Nat := 216945234204172328715295

theorem tailTrace_3802494 : CollatzResearch.WordTrace tailWord_3802494 prefixEnd_3802494 216945234204172328715295 := by
  unfold tailWord_3802494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336043735777640889724817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92458899924147418078532357 17336043735777640889724817)
  ·
    refine ⟨13002032801833230667293613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17336043735777640889724817 13002032801833230667293613)
    ·
      refine ⟨4875762300687461500235105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13002032801833230667293613 4875762300687461500235105)
      ·
        refine ⟨3656821725515596125176329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4875762300687461500235105 3656821725515596125176329)
        ·
          refine ⟨2742616294136697093882247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656821725515596125176329 2742616294136697093882247)
          ·
            refine ⟨4113924441205045640823371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742616294136697093882247 4113924441205045640823371)
            ·
              refine ⟨6170886661807568461235057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113924441205045640823371 6170886661807568461235057)
              ·
                refine ⟨4628164996355676345926293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170886661807568461235057 4628164996355676345926293)
                ·
                  refine ⟨216945234204172328715295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4628164996355676345926293 216945234204172328715295)
                  ·
                    rfl

theorem cell23_3802494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3802494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802494 prefixEnd_3802494 := by exact prefixLift 3802494
  have htrace : WordTrace (prefixWord ++ tailWord_3802494) baseStart_3802494 baseEnd_3802494 := by
    simpa [prefixWord, tailWord_3802494, baseEnd_3802494] using wordTrace_append hprefix tailTrace_3802494
  have hstable : (prefixWord ++ tailWord_3802494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802494).length < 2 ^ (prefixWord ++ tailWord_3802494).sum := by decide
  have hdescent : baseEnd_3802494 < baseStart_3802494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802503 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 4, 4]
def baseStart_3802503 : Nat := 118140960795 + 3802503 * 2 ^ 59
def prefixEnd_3802503 : Nat := 4983230072969 + 3 ^ 40 * 3802503 * 2
def baseEnd_3802503 : Nat := 650837243054480474408371

theorem tailTrace_3802503 : CollatzResearch.WordTrace tailWord_3802503 prefixEnd_3802503 650837243054480474408371 := by
  unfold tailWord_3802503
  simp only [CollatzResearch.WordTrace]
  refine ⟨138688678143188521654876163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92459118762125681103250775 138688678143188521654876163)
  ·
    refine ⟨208033017214782782482314245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138688678143188521654876163 208033017214782782482314245)
    ·
      refine ⟨39006190727771771715433921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208033017214782782482314245 39006190727771771715433921)
      ·
        refine ⟨29254643045828828786575441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39006190727771771715433921 29254643045828828786575441)
        ·
          refine ⟨21940982284371621589931581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29254643045828828786575441 21940982284371621589931581)
          ·
            refine ⟨8227868356639358096224343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21940982284371621589931581 8227868356639358096224343)
            ·
              refine ⟨12341802534959037144336515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227868356639358096224343 12341802534959037144336515)
              ·
                refine ⟨18512703802438555716504773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12341802534959037144336515 18512703802438555716504773)
                ·
                  refine ⟨3471131962957229196844645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18512703802438555716504773 3471131962957229196844645)
                  ·
                    refine ⟨650837243054480474408371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471131962957229196844645 650837243054480474408371)
                    ·
                      rfl

theorem cell23_3802503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_3802503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802503 prefixEnd_3802503 := by exact prefixLift 3802503
  have htrace : WordTrace (prefixWord ++ tailWord_3802503) baseStart_3802503 baseEnd_3802503 := by
    simpa [prefixWord, tailWord_3802503, baseEnd_3802503] using wordTrace_append hprefix tailTrace_3802503
  have hstable : (prefixWord ++ tailWord_3802503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802503).length < 2 ^ (prefixWord ++ tailWord_3802503).sum := by decide
  have hdescent : baseEnd_3802503 < baseStart_3802503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802520 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 1, 6]
def baseStart_3802520 : Nat := 118140960795 + 3802520 * 2 ^ 59
def prefixEnd_3802520 : Nat := 4983230072969 + 3 ^ 40 * 3802520 * 2
def baseEnd_3802520 : Nat := 650840152778189285570845

theorem tailTrace_3802520 : CollatzResearch.WordTrace tailWord_3802520 prefixEnd_3802520 650840152778189285570845 := by
  unfold tailWord_3802520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69344649092063466779122507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92459532122751289038830009 69344649092063466779122507)
  ·
    refine ⟨104016973638095200168683761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69344649092063466779122507 104016973638095200168683761)
    ·
      refine ⟨78012730228571400126512821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104016973638095200168683761 78012730228571400126512821)
      ·
        refine ⟨7313693458928568761860577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78012730228571400126512821 7313693458928568761860577)
        ·
          refine ⟨5485270094196426571395433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313693458928568761860577 5485270094196426571395433)
          ·
            refine ⟨4113952570647319928546575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5485270094196426571395433 4113952570647319928546575)
            ·
              refine ⟨6170928855970979892819863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113952570647319928546575 6170928855970979892819863)
              ·
                refine ⟨9256393283956469839229795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170928855970979892819863 9256393283956469839229795)
                ·
                  refine ⟨13884589925934704758844693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256393283956469839229795 13884589925934704758844693)
                  ·
                    refine ⟨650840152778189285570845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13884589925934704758844693 650840152778189285570845)
                    ·
                      rfl

theorem cell23_3802520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_3802520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802520 prefixEnd_3802520 := by exact prefixLift 3802520
  have htrace : WordTrace (prefixWord ++ tailWord_3802520) baseStart_3802520 baseEnd_3802520 := by
    simpa [prefixWord, tailWord_3802520, baseEnd_3802520] using wordTrace_append hprefix tailTrace_3802520
  have hstable : (prefixWord ++ tailWord_3802520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802520).length < 2 ^ (prefixWord ++ tailWord_3802520).sum := by decide
  have hdescent : baseEnd_3802520 < baseStart_3802520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802530 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3802530 : Nat := 118140960795 + 3802530 * 2 ^ 59
def prefixEnd_3802530 : Nat := 4983230072969 + 3 ^ 40 * 3802530 * 2
def baseEnd_3802530 : Nat := 1952525593141112817587489

theorem tailTrace_3802530 : CollatzResearch.WordTrace tailWord_3802530 prefixEnd_3802530 1952525593141112817587489 := by
  unfold tailWord_3802530
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672415728522676316527261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92459775276060470177406029 34672415728522676316527261)
  ·
    refine ⟨13002155898196003618697723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34672415728522676316527261 13002155898196003618697723)
    ·
      refine ⟨19503233847294005428046585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13002155898196003618697723 19503233847294005428046585)
      ·
        refine ⟨14627425385470504071034939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19503233847294005428046585 14627425385470504071034939)
        ·
          refine ⟨21941138078205756106552409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14627425385470504071034939 21941138078205756106552409)
          ·
            refine ⟨16455853558654317079914307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21941138078205756106552409 16455853558654317079914307)
            ·
              refine ⟨24683780337981475619871461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16455853558654317079914307 24683780337981475619871461)
              ·
                refine ⟨4628208813371526678725899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24683780337981475619871461 4628208813371526678725899)
                ·
                  refine ⟨6942313220057290018088849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628208813371526678725899 6942313220057290018088849)
                  ·
                    refine ⟨5206734915042967513566637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942313220057290018088849 5206734915042967513566637)
                    ·
                      refine ⟨1952525593141112817587489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206734915042967513566637 1952525593141112817587489)
                      ·
                        rfl

theorem cell23_3802530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3802530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802530 prefixEnd_3802530 := by exact prefixLift 3802530
  have htrace : WordTrace (prefixWord ++ tailWord_3802530) baseStart_3802530 baseEnd_3802530 := by
    simpa [prefixWord, tailWord_3802530, baseEnd_3802530] using wordTrace_append hprefix tailTrace_3802530
  have hstable : (prefixWord ++ tailWord_3802530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802530).length < 2 ^ (prefixWord ++ tailWord_3802530).sum := by decide
  have hdescent : baseEnd_3802530 < baseStart_3802530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802583 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 5, 4, 2]
def baseStart_3802583 : Nat := 118140960795 + 3802583 * 2 ^ 59
def prefixEnd_3802583 : Nat := 4983230072969 + 3 ^ 40 * 3802583 * 2
def baseEnd_3802583 : Nat := 1952552807615801110224745

theorem tailTrace_3802583 : CollatzResearch.WordTrace tailWord_3802583 prefixEnd_3802583 1952552807615801110224745 := by
  unfold tailWord_3802583
  simp only [CollatzResearch.WordTrace]
  refine ⟨138691595982898695317788403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92461063988599130211858935 138691595982898695317788403)
  ·
    refine ⟨208037393974348042976682605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138691595982898695317788403 208037393974348042976682605)
    ·
      refine ⟨78014022740380516116255977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208037393974348042976682605 78014022740380516116255977)
      ·
        refine ⟨58510517055285387087191983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78014022740380516116255977 58510517055285387087191983)
        ·
          refine ⟨87765775582928080630787975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58510517055285387087191983 87765775582928080630787975)
          ·
            refine ⟨131648663374392120946181963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87765775582928080630787975 131648663374392120946181963)
            ·
              refine ⟨197472995061588181419272945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131648663374392120946181963 197472995061588181419272945)
              ·
                refine ⟨148104746296191136064454709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197472995061588181419272945 148104746296191136064454709)
                ·
                  refine ⟨13884819965267919006042629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148104746296191136064454709 13884819965267919006042629)
                  ·
                    refine ⟨2603403743487734813632993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13884819965267919006042629 2603403743487734813632993)
                    ·
                      refine ⟨1952552807615801110224745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603403743487734813632993 1952552807615801110224745)
                      ·
                        rfl

theorem cell23_3802583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_3802583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802583 prefixEnd_3802583 := by exact prefixLift 3802583
  have htrace : WordTrace (prefixWord ++ tailWord_3802583) baseStart_3802583 baseEnd_3802583 := by
    simpa [prefixWord, tailWord_3802583, baseEnd_3802583] using wordTrace_append hprefix tailTrace_3802583
  have hstable : (prefixWord ++ tailWord_3802583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802583).length < 2 ^ (prefixWord ++ tailWord_3802583).sum := by decide
  have hdescent : baseEnd_3802583 < baseStart_3802583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802600 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3802600 : Nat := 118140960795 + 3802600 * 2 ^ 59
def prefixEnd_3802600 : Nat := 4983230072969 + 3 ^ 40 * 3802600 * 2
def baseEnd_3802600 : Nat := 1952561536786927543712167

theorem tailTrace_3802600 : CollatzResearch.WordTrace tailWord_3802600 prefixEnd_3802600 1952561536786927543712167 := by
  unfold tailWord_3802600
  simp only [CollatzResearch.WordTrace]
  refine ⟨69346108011918553610578627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92461477349224738147438169 69346108011918553610578627)
  ·
    refine ⟨104019162017877830415867941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69346108011918553610578627 104019162017877830415867941)
    ·
      refine ⟨19503592878352093202975239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104019162017877830415867941 19503592878352093202975239)
      ·
        refine ⟨29255389317528139804462859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503592878352093202975239 29255389317528139804462859)
        ·
          refine ⟨43883083976292209706694289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29255389317528139804462859 43883083976292209706694289)
          ·
            refine ⟨32912312982219157280020717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43883083976292209706694289 32912312982219157280020717)
            ·
              refine ⟨12342117368332183980007769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32912312982219157280020717 12342117368332183980007769)
              ·
                refine ⟨9256588026249137985005827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12342117368332183980007769 9256588026249137985005827)
                ·
                  refine ⟨13884882039373706977508741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256588026249137985005827 13884882039373706977508741)
                  ·
                    refine ⟨2603415382382570058282889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13884882039373706977508741 2603415382382570058282889)
                    ·
                      refine ⟨1952561536786927543712167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603415382382570058282889 1952561536786927543712167)
                      ·
                        rfl

theorem cell23_3802600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3802600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802600 prefixEnd_3802600 := by exact prefixLift 3802600
  have htrace : WordTrace (prefixWord ++ tailWord_3802600) baseStart_3802600 baseEnd_3802600 := by
    simpa [prefixWord, tailWord_3802600, baseEnd_3802600] using wordTrace_append hprefix tailTrace_3802600
  have hstable : (prefixWord ++ tailWord_3802600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802600).length < 2 ^ (prefixWord ++ tailWord_3802600).sum := by decide
  have hdescent : baseEnd_3802600 < baseStart_3802600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802633 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_3802633 : Nat := 118140960795 + 3802633 * 2 ^ 59
def prefixEnd_3802633 : Nat := 4983230072969 + 3 ^ 40 * 3802633 * 2
def baseEnd_3802633 : Nat := 1952578481648525914599515

theorem tailTrace_3802633 : CollatzResearch.WordTrace tailWord_3802633 prefixEnd_3802633 1952578481648525914599515 := by
  unfold tailWord_3802633
  simp only [CollatzResearch.WordTrace]
  refine ⟨138693419632717553857108553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92462279755145035904739035 138693419632717553857108553)
  ·
    refine ⟨104020064724538165392831415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138693419632717553857108553 104020064724538165392831415)
    ·
      refine ⟨156030097086807248089247123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104020064724538165392831415 156030097086807248089247123)
      ·
        refine ⟨234045145630210872133870685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156030097086807248089247123 234045145630210872133870685)
        ·
          refine ⟨87766929611329077050201507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234045145630210872133870685 87766929611329077050201507)
          ·
            refine ⟨131650394416993615575302261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87766929611329077050201507 131650394416993615575302261)
            ·
              refine ⟨12342224476593151460184587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131650394416993615575302261 12342224476593151460184587)
              ·
                refine ⟨18513336714889727190276881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12342224476593151460184587 18513336714889727190276881)
                ·
                  refine ⟨13885002536167295392707661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18513336714889727190276881 13885002536167295392707661)
                  ·
                    refine ⟨5206875951062735772265373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13885002536167295392707661 5206875951062735772265373)
                    ·
                      refine ⟨1952578481648525914599515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206875951062735772265373 1952578481648525914599515)
                      ·
                        rfl

theorem cell23_3802633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_3802633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802633 prefixEnd_3802633 := by exact prefixLift 3802633
  have htrace : WordTrace (prefixWord ++ tailWord_3802633) baseStart_3802633 baseEnd_3802633 := by
    simpa [prefixWord, tailWord_3802633, baseEnd_3802633] using wordTrace_append hprefix tailTrace_3802633
  have hstable : (prefixWord ++ tailWord_3802633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802633).length < 2 ^ (prefixWord ++ tailWord_3802633).sum := by decide
  have hdescent : baseEnd_3802633 < baseStart_3802633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802653 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3802653 : Nat := 118140960795 + 3802653 * 2 ^ 59
def prefixEnd_3802653 : Nat := 4983230072969 + 3 ^ 40 * 3802653 * 2
def baseEnd_3802653 : Nat := 650862917087205278783141

theorem tailTrace_3802653 : CollatzResearch.WordTrace tailWord_3802653 prefixEnd_3802653 650862917087205278783141 := by
  unfold tailWord_3802653
  simp only [CollatzResearch.WordTrace]
  refine ⟨138694149092645097272836613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92462766061763398181891075 138694149092645097272836613)
  ·
    refine ⟨26005152954870955738656865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138694149092645097272836613 26005152954870955738656865)
    ·
      refine ⟨19503864716153216803992649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26005152954870955738656865 19503864716153216803992649)
      ·
        refine ⟨14627898537114912602994487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19503864716153216803992649 14627898537114912602994487)
        ·
          refine ⟨21941847805672368904491731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14627898537114912602994487 21941847805672368904491731)
          ·
            refine ⟨32912771708508553356737597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21941847805672368904491731 32912771708508553356737597)
            ·
              refine ⟨12342289390690707508776599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32912771708508553356737597 12342289390690707508776599)
              ·
                refine ⟨18513434086036061263164899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12342289390690707508776599 18513434086036061263164899)
                ·
                  refine ⟨27770151129054091894747349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18513434086036061263164899 27770151129054091894747349)
                  ·
                    refine ⟨650862917087205278783141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27770151129054091894747349 650862917087205278783141)
                    ·
                      rfl

theorem cell23_3802653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3802653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802653 prefixEnd_3802653 := by exact prefixLift 3802653
  have htrace : WordTrace (prefixWord ++ tailWord_3802653) baseStart_3802653 baseEnd_3802653 := by
    simpa [prefixWord, tailWord_3802653, baseEnd_3802653] using wordTrace_append hprefix tailTrace_3802653
  have hstable : (prefixWord ++ tailWord_3802653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802653).length < 2 ^ (prefixWord ++ tailWord_3802653).sum := by decide
  have hdescent : baseEnd_3802653 < baseStart_3802653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802673 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3802673 : Nat := 118140960795 + 3802673 * 2 ^ 59
def prefixEnd_3802673 : Nat := 4983230072969 + 3 ^ 40 * 3802673 * 2
def baseEnd_3802673 : Nat := 1952599020874705758099331

theorem tailTrace_3802673 : CollatzResearch.WordTrace tailWord_3802673 prefixEnd_3802673 1952599020874705758099331 := by
  unfold tailWord_3802673
  simp only [CollatzResearch.WordTrace]
  refine ⟨138694878552572640688564673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92463252368381760459043115 138694878552572640688564673)
  ·
    refine ⟨104021158914429480516423505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138694878552572640688564673 104021158914429480516423505)
    ·
      refine ⟨78015869185822110387317629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104021158914429480516423505 78015869185822110387317629)
      ·
        refine ⟨29255950944683291395244111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78015869185822110387317629 29255950944683291395244111)
        ·
          refine ⟨43883926417024937092866167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29255950944683291395244111 43883926417024937092866167)
          ·
            refine ⟨65825889625537405639299251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43883926417024937092866167 65825889625537405639299251)
            ·
              refine ⟨98738834438306108458948877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65825889625537405639299251 98738834438306108458948877)
              ·
                refine ⟨37027062914364790672105829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98738834438306108458948877 37027062914364790672105829)
                ·
                  refine ⟨6942574296443398251019843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37027062914364790672105829 6942574296443398251019843)
                  ·
                    refine ⟨10413861444665097376529765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6942574296443398251019843 10413861444665097376529765)
                    ·
                      refine ⟨1952599020874705758099331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10413861444665097376529765 1952599020874705758099331)
                      ·
                        rfl

theorem cell23_3802673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3802673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802673 prefixEnd_3802673 := by exact prefixLift 3802673
  have htrace : WordTrace (prefixWord ++ tailWord_3802673) baseStart_3802673 baseEnd_3802673 := by
    simpa [prefixWord, tailWord_3802673, baseEnd_3802673] using wordTrace_append hprefix tailTrace_3802673
  have hstable : (prefixWord ++ tailWord_3802673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802673).length < 2 ^ (prefixWord ++ tailWord_3802673).sum := by decide
  have hdescent : baseEnd_3802673 < baseStart_3802673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802693 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_3802693 : Nat := 118140960795 + 3802693 * 2 ^ 59
def prefixEnd_3802693 : Nat := 4983230072969 + 3 ^ 40 * 3802693 * 2
def baseEnd_3802693 : Nat := 1952609290487795679849239

theorem tailTrace_3802693 : CollatzResearch.WordTrace tailWord_3802693 prefixEnd_3802693 1952609290487795679849239 := by
  unfold tailWord_3802693
  simp only [CollatzResearch.WordTrace]
  refine ⟨138695608012500184104292733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92463738675000122736195155 138695608012500184104292733)
  ·
    refine ⟨52010853004687569039109775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138695608012500184104292733 52010853004687569039109775)
    ·
      refine ⟨78016279507031353558664663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52010853004687569039109775 78016279507031353558664663)
      ·
        refine ⟨117024419260547030337996995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78016279507031353558664663 117024419260547030337996995)
        ·
          refine ⟨175536628890820545506995493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117024419260547030337996995 175536628890820545506995493)
          ·
            refine ⟨32913117917028852282561655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175536628890820545506995493 32913117917028852282561655)
            ·
              refine ⟨49369676875543278423842483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32913117917028852282561655 49369676875543278423842483)
              ·
                refine ⟨74054515313314917635763725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49369676875543278423842483 74054515313314917635763725)
                ·
                  refine ⟨27770443242493094113411397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74054515313314917635763725 27770443242493094113411397)
                  ·
                    refine ⟨5206958107967455146264637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27770443242493094113411397 5206958107967455146264637)
                    ·
                      refine ⟨1952609290487795679849239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206958107967455146264637 1952609290487795679849239)
                      ·
                        rfl

theorem cell23_3802693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_3802693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802693 prefixEnd_3802693 := by exact prefixLift 3802693
  have htrace : WordTrace (prefixWord ++ tailWord_3802693) baseStart_3802693 baseEnd_3802693 := by
    simpa [prefixWord, tailWord_3802693, baseEnd_3802693] using wordTrace_append hprefix tailTrace_3802693
  have hstable : (prefixWord ++ tailWord_3802693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802693).length < 2 ^ (prefixWord ++ tailWord_3802693).sum := by decide
  have hdescent : baseEnd_3802693 < baseStart_3802693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802700 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_3802700 : Nat := 118140960795 + 3802700 * 2 ^ 59
def prefixEnd_3802700 : Nat := 4983230072969 + 3 ^ 40 * 3802700 * 2
def baseEnd_3802700 : Nat := 650870961617459050820569

theorem tailTrace_3802700 : CollatzResearch.WordTrace tailWord_3802700 prefixEnd_3802700 650870961617459050820569 := by
  unfold tailWord_3802700
  simp only [CollatzResearch.WordTrace]
  refine ⟨69347931661737412149898777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92463908882316549533198369 69347931661737412149898777)
  ·
    refine ⟨52010948746303059112424083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69347931661737412149898777 52010948746303059112424083)
    ·
      refine ⟨78016423119454588668636125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52010948746303059112424083 78016423119454588668636125)
      ·
        refine ⟨29256158669795470750738547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78016423119454588668636125 29256158669795470750738547)
        ·
          refine ⟨43884238004693206126107821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29256158669795470750738547 43884238004693206126107821)
          ·
            refine ⟨16456589251759952297290433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43884238004693206126107821 16456589251759952297290433)
            ·
              refine ⟨12342441938819964222967825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16456589251759952297290433 12342441938819964222967825)
              ·
                refine ⟨9256831454114973167225869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12342441938819964222967825 9256831454114973167225869)
                ·
                  refine ⟨3471311795293114937709701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9256831454114973167225869 3471311795293114937709701)
                  ·
                    refine ⟨650870961617459050820569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471311795293114937709701 650870961617459050820569)
                    ·
                      rfl

theorem cell23_3802700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_3802700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802700 prefixEnd_3802700 := by exact prefixLift 3802700
  have htrace : WordTrace (prefixWord ++ tailWord_3802700) baseStart_3802700 baseEnd_3802700 := by
    simpa [prefixWord, tailWord_3802700, baseEnd_3802700] using wordTrace_append hprefix tailTrace_3802700
  have hstable : (prefixWord ++ tailWord_3802700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802700).length < 2 ^ (prefixWord ++ tailWord_3802700).sum := by decide
  have hdescent : baseEnd_3802700 < baseStart_3802700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802734 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3802734 : Nat := 118140960795 + 3802734 * 2 ^ 59
def prefixEnd_3802734 : Nat := 4983230072969 + 3 ^ 40 * 3802734 * 2
def baseEnd_3802734 : Nat := 650876781064876673145517

theorem tailTrace_3802734 : CollatzResearch.WordTrace tailWord_3802734 prefixEnd_3802734 650876781064876673145517 := by
  unfold tailWord_3802734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337137925668956013316907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92464735603567765404356837 17337137925668956013316907)
  ·
    refine ⟨26005706888503434019975361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17337137925668956013316907 26005706888503434019975361)
    ·
      refine ⟨19504280166377575514981521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26005706888503434019975361 19504280166377575514981521)
      ·
        refine ⟨14628210124783181636236141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19504280166377575514981521 14628210124783181636236141)
        ·
          refine ⟨5485578796793693113588553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14628210124783181636236141 5485578796793693113588553)
          ·
            refine ⟨4114184097595269835191415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5485578796793693113588553 4114184097595269835191415)
            ·
              refine ⟨6171276146392904752787123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114184097595269835191415 6171276146392904752787123)
              ·
                refine ⟨9256914219589357129180685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171276146392904752787123 9256914219589357129180685)
                ·
                  refine ⟨3471342832346008923442757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9256914219589357129180685 3471342832346008923442757)
                  ·
                    refine ⟨650876781064876673145517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471342832346008923442757 650876781064876673145517)
                    ·
                      rfl

theorem cell23_3802734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3802734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802734 prefixEnd_3802734 := by exact prefixLift 3802734
  have htrace : WordTrace (prefixWord ++ tailWord_3802734) baseStart_3802734 baseEnd_3802734 := by
    simpa [prefixWord, tailWord_3802734, baseEnd_3802734] using wordTrace_append hprefix tailTrace_3802734
  have hstable : (prefixWord ++ tailWord_3802734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802734).length < 2 ^ (prefixWord ++ tailWord_3802734).sum := by decide
  have hdescent : baseEnd_3802734 < baseStart_3802734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802743 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 3, 5]
def baseStart_3802743 : Nat := 118140960795 + 3802743 * 2 ^ 59
def prefixEnd_3802743 : Nat := 4983230072969 + 3 ^ 40 * 3802743 * 2
def baseEnd_3802743 : Nat := 650878321506840161408003

theorem tailTrace_3802743 : CollatzResearch.WordTrace tailWord_3802743 prefixEnd_3802743 650878321506840161408003 := by
  unfold tailWord_3802743
  simp only [CollatzResearch.WordTrace]
  refine ⟨138697431662319042643612883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92464954441546028429075255 138697431662319042643612883)
  ·
    refine ⟨208046147493478563965419325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138697431662319042643612883 208046147493478563965419325)
    ·
      refine ⟨78017305310054461487032247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208046147493478563965419325 78017305310054461487032247)
      ·
        refine ⟨117025957965081692230548371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78017305310054461487032247 117025957965081692230548371)
        ·
          refine ⟨175538936947622538345822557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117025957965081692230548371 175538936947622538345822557)
          ·
            refine ⟨65827101355358451879683459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175538936947622538345822557 65827101355358451879683459)
            ·
              refine ⟨98740652033037677819525189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65827101355358451879683459 98740652033037677819525189)
              ·
                refine ⟨18513872256194564591160973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98740652033037677819525189 18513872256194564591160973)
                ·
                  refine ⟨6942702096072961721685365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18513872256194564591160973 6942702096072961721685365)
                  ·
                    refine ⟨650878321506840161408003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6942702096072961721685365 650878321506840161408003)
                    ·
                      rfl

theorem cell23_3802743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_3802743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802743 prefixEnd_3802743 := by exact prefixLift 3802743
  have htrace : WordTrace (prefixWord ++ tailWord_3802743) baseStart_3802743 baseEnd_3802743 := by
    simpa [prefixWord, tailWord_3802743, baseEnd_3802743] using wordTrace_append hprefix tailTrace_3802743
  have hstable : (prefixWord ++ tailWord_3802743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802743).length < 2 ^ (prefixWord ++ tailWord_3802743).sum := by decide
  have hdescent : baseEnd_3802743 < baseStart_3802743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802800 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_3802800 : Nat := 118140960795 + 3802800 * 2 ^ 59
def prefixEnd_3802800 : Nat := 4983230072969 + 3 ^ 40 * 3802800 * 2
def baseEnd_3802800 : Nat := 1952664232917826761211247

theorem tailTrace_3802800 : CollatzResearch.WordTrace tailWord_3802800 prefixEnd_3802800 1952664232917826761211247 := by
  unfold tailWord_3802800
  simp only [CollatzResearch.WordTrace]
  refine ⟨69349755311556270689218927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92466340415408360918958569 69349755311556270689218927)
  ·
    refine ⟨104024632967334406033828391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69349755311556270689218927 104024632967334406033828391)
    ·
      refine ⟨156036949451001609050742587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104024632967334406033828391 156036949451001609050742587)
      ·
        refine ⟨234055424176502413576113881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156036949451001609050742587 234055424176502413576113881)
        ·
          refine ⟨175541568132376810182085411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234055424176502413576113881 175541568132376810182085411)
          ·
            refine ⟨263312352198565215273128117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175541568132376810182085411 263312352198565215273128117)
            ·
              refine ⟨24685533018615488931855761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263312352198565215273128117 24685533018615488931855761)
              ·
                refine ⟨18514149763961616698891821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24685533018615488931855761 18514149763961616698891821)
                ·
                  refine ⟨6942806161485606262084433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18514149763961616698891821 6942806161485606262084433)
                  ·
                    refine ⟨5207104621114204696563325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942806161485606262084433 5207104621114204696563325)
                    ·
                      refine ⟨1952664232917826761211247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207104621114204696563325 1952664232917826761211247)
                      ·
                        rfl

theorem cell23_3802800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_3802800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802800 prefixEnd_3802800 := by exact prefixLift 3802800
  have htrace : WordTrace (prefixWord ++ tailWord_3802800) baseStart_3802800 baseEnd_3802800 := by
    simpa [prefixWord, tailWord_3802800, baseEnd_3802800] using wordTrace_append hprefix tailTrace_3802800
  have hstable : (prefixWord ++ tailWord_3802800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802800).length < 2 ^ (prefixWord ++ tailWord_3802800).sum := by decide
  have hdescent : baseEnd_3802800 < baseStart_3802800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802807 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 2, 4]
def baseStart_3802807 : Nat := 118140960795 + 3802807 * 2 ^ 59
def prefixEnd_3802807 : Nat := 4983230072969 + 3 ^ 40 * 3802807 * 2
def baseEnd_3802807 : Nat := 650889275760802744607905

theorem tailTrace_3802807 : CollatzResearch.WordTrace tailWord_3802807 prefixEnd_3802807 650889275760802744607905 := by
  unfold tailWord_3802807
  simp only [CollatzResearch.WordTrace]
  refine ⟨138699765934087181573942675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92466510622724787715961783 138699765934087181573942675)
  ·
    refine ⟨208049648901130772360914013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138699765934087181573942675 208049648901130772360914013)
    ·
      refine ⟨78018618337924039635342755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208049648901130772360914013 78018618337924039635342755)
      ·
        refine ⟨117027927506886059453014133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78018618337924039635342755 117027927506886059453014133)
        ·
          refine ⟨10971368203770568073720075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117027927506886059453014133 10971368203770568073720075)
          ·
            refine ⟨16457052305655852110580113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10971368203770568073720075 16457052305655852110580113)
            ·
              refine ⟨12342789229241889082935085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16457052305655852110580113 12342789229241889082935085)
              ·
                refine ⟨4628545960965708406100657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12342789229241889082935085 4628545960965708406100657)
                ·
                  refine ⟨3471409470724281304575493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4628545960965708406100657 3471409470724281304575493)
                  ·
                    refine ⟨650889275760802744607905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3471409470724281304575493 650889275760802744607905)
                    ·
                      rfl

theorem cell23_3802807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_3802807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802807 prefixEnd_3802807 := by exact prefixLift 3802807
  have htrace : WordTrace (prefixWord ++ tailWord_3802807) baseStart_3802807 baseEnd_3802807 := by
    simpa [prefixWord, tailWord_3802807, baseEnd_3802807] using wordTrace_append hprefix tailTrace_3802807
  have hstable : (prefixWord ++ tailWord_3802807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802807).length < 2 ^ (prefixWord ++ tailWord_3802807).sum := by decide
  have hdescent : baseEnd_3802807 < baseStart_3802807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802810 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_3802810 : Nat := 118140960795 + 3802810 * 2 ^ 59
def prefixEnd_3802810 : Nat := 4983230072969 + 3 ^ 40 * 3802810 * 2
def baseEnd_3802810 : Nat := 1952669367724371722086201

theorem tailTrace_3802810 : CollatzResearch.WordTrace tailWord_3802810 prefixEnd_3802810 1952669367724371722086201 := by
  unfold tailWord_3802810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34674968838269078271575471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92466583568717542057534589 34674968838269078271575471)
  ·
    refine ⟨52012453257403617407363207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34674968838269078271575471 52012453257403617407363207)
    ·
      refine ⟨78018679886105426111044811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52012453257403617407363207 78018679886105426111044811)
      ·
        refine ⟨117028019829158139166567217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78018679886105426111044811 117028019829158139166567217)
        ·
          refine ⟨87771014871868604374925413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117028019829158139166567217 87771014871868604374925413)
          ·
            refine ⟨16457065288475363320298515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87771014871868604374925413 16457065288475363320298515)
            ·
              refine ⟨24685597932713044980447773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16457065288475363320298515 24685597932713044980447773)
              ·
                refine ⟨9257099224767391867667915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24685597932713044980447773 9257099224767391867667915)
                ·
                  refine ⟨13885648837151087801501873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257099224767391867667915 13885648837151087801501873)
                  ·
                    refine ⟨10414236627863315851126405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13885648837151087801501873 10414236627863315851126405)
                    ·
                      refine ⟨1952669367724371722086201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10414236627863315851126405 1952669367724371722086201)
                      ·
                        rfl

theorem cell23_3802810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_3802810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802810 prefixEnd_3802810 := by exact prefixLift 3802810
  have htrace : WordTrace (prefixWord ++ tailWord_3802810) baseStart_3802810 baseEnd_3802810 := by
    simpa [prefixWord, tailWord_3802810, baseEnd_3802810] using wordTrace_append hprefix tailTrace_3802810
  have hstable : (prefixWord ++ tailWord_3802810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802810).length < 2 ^ (prefixWord ++ tailWord_3802810).sum := by decide
  have hdescent : baseEnd_3802810 < baseStart_3802810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802814 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_3802814 : Nat := 118140960795 + 3802814 * 2 ^ 59
def prefixEnd_3802814 : Nat := 4983230072969 + 3 ^ 40 * 3802814 * 2
def baseEnd_3802814 : Nat := 1952671421646989706436183

theorem tailTrace_3802814 : CollatzResearch.WordTrace tailWord_3802814 prefixEnd_3802814 1952671421646989706436183 := by
  unfold tailWord_3802814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337502655632727721180937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92466680830041214512964997 17337502655632727721180937)
  ·
    refine ⟨13003126991724545790885703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17337502655632727721180937 13003126991724545790885703)
    ·
      refine ⟨19504690487586818686328555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13003126991724545790885703 19504690487586818686328555)
      ·
        refine ⟨29257035731380228029492833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19504690487586818686328555 29257035731380228029492833)
        ·
          refine ⟨21942776798535171022119625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29257035731380228029492833 21942776798535171022119625)
          ·
            refine ⟨16457082598901378266589719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21942776798535171022119625 16457082598901378266589719)
            ·
              refine ⟨24685623898352067399884579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16457082598901378266589719 24685623898352067399884579)
              ·
                refine ⟨37028435847528101099826869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24685623898352067399884579 37028435847528101099826869)
                ·
                  refine ⟨3471415860705759478108769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37028435847528101099826869 3471415860705759478108769)
                  ·
                    refine ⟨2603561895529319608581577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3471415860705759478108769 2603561895529319608581577)
                    ·
                      refine ⟨1952671421646989706436183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603561895529319608581577 1952671421646989706436183)
                      ·
                        rfl

theorem cell23_3802814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_3802814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802814 prefixEnd_3802814 := by exact prefixLift 3802814
  have htrace : WordTrace (prefixWord ++ tailWord_3802814) baseStart_3802814 baseEnd_3802814 := by
    simpa [prefixWord, tailWord_3802814, baseEnd_3802814] using wordTrace_append hprefix tailTrace_3802814
  have hstable : (prefixWord ++ tailWord_3802814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802814).length < 2 ^ (prefixWord ++ tailWord_3802814).sum := by decide
  have hdescent : baseEnd_3802814 < baseStart_3802814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802818 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3802818 : Nat := 118140960795 + 3802818 * 2 ^ 59
def prefixEnd_3802818 : Nat := 4983230072969 + 3 ^ 40 * 3802818 * 2
def baseEnd_3802818 : Nat := 1952673475569607690786165

theorem tailTrace_3802818 : CollatzResearch.WordTrace tailWord_3802818 prefixEnd_3802818 1952673475569607690786165 := by
  unfold tailWord_3802818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34675041784261832613148277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92466778091364886968395405 34675041784261832613148277)
  ·
    refine ⟨3250785167274546807482651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34675041784261832613148277 3250785167274546807482651)
    ·
      refine ⟨4876177750911820211223977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3250785167274546807482651 4876177750911820211223977)
      ·
        refine ⟨3657133313183865158417983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4876177750911820211223977 3657133313183865158417983)
        ·
          refine ⟨5485699969775797737626975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657133313183865158417983 5485699969775797737626975)
          ·
            refine ⟨8228549954663696606440463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485699969775797737626975 8228549954663696606440463)
            ·
              refine ⟨12342824931995544909660695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8228549954663696606440463 12342824931995544909660695)
              ·
                refine ⟨18514237397993317364491043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12342824931995544909660695 18514237397993317364491043)
                ·
                  refine ⟨27771356096989976046736565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18514237397993317364491043 27771356096989976046736565)
                  ·
                    refine ⟨2603564634092810254381553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27771356096989976046736565 2603564634092810254381553)
                    ·
                      refine ⟨1952673475569607690786165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603564634092810254381553 1952673475569607690786165)
                      ·
                        rfl

theorem cell23_3802818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3802818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802818 prefixEnd_3802818 := by exact prefixLift 3802818
  have htrace : WordTrace (prefixWord ++ tailWord_3802818) baseStart_3802818 baseEnd_3802818 := by
    simpa [prefixWord, tailWord_3802818, baseEnd_3802818] using wordTrace_append hprefix tailTrace_3802818
  have hstable : (prefixWord ++ tailWord_3802818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802818).length < 2 ^ (prefixWord ++ tailWord_3802818).sum := by decide
  have hdescent : baseEnd_3802818 < baseStart_3802818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802834 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3802834 : Nat := 118140960795 + 3802834 * 2 ^ 59
def prefixEnd_3802834 : Nat := 4983230072969 + 3 ^ 40 * 3802834 * 2
def baseEnd_3802834 : Nat := 1952681691260079628186091

theorem tailTrace_3802834 : CollatzResearch.WordTrace tailWord_3802834 prefixEnd_3802834 1952681691260079628186091 := by
  unfold tailWord_3802834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34675187676247341296293889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92467167136659576790117037 34675187676247341296293889)
  ·
    refine ⟨26006390757185505972220417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34675187676247341296293889 26006390757185505972220417)
    ·
      refine ⟨19504793067889129479165313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26006390757185505972220417 19504793067889129479165313)
      ·
        refine ⟨14628594800916847109373985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19504793067889129479165313 14628594800916847109373985)
        ·
          refine ⟨10971446100687635332030489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14628594800916847109373985 10971446100687635332030489)
          ·
            refine ⟨8228584575515726499022867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10971446100687635332030489 8228584575515726499022867)
            ·
              refine ⟨12342876863273589748534301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8228584575515726499022867 12342876863273589748534301)
              ·
                refine ⟨4628578823727596155700363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12342876863273589748534301 4628578823727596155700363)
                ·
                  refine ⟨6942868235591394233550545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628578823727596155700363 6942868235591394233550545)
                  ·
                    refine ⟨5207151176693545675162909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942868235591394233550545 5207151176693545675162909)
                    ·
                      refine ⟨1952681691260079628186091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207151176693545675162909 1952681691260079628186091)
                      ·
                        rfl

theorem cell23_3802834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3802834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802834 prefixEnd_3802834 := by exact prefixLift 3802834
  have htrace : WordTrace (prefixWord ++ tailWord_3802834) baseStart_3802834 baseEnd_3802834 := by
    simpa [prefixWord, tailWord_3802834, baseEnd_3802834] using wordTrace_append hprefix tailTrace_3802834
  have hstable : (prefixWord ++ tailWord_3802834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802834).length < 2 ^ (prefixWord ++ tailWord_3802834).sum := by decide
  have hdescent : baseEnd_3802834 < baseStart_3802834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802847 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 3]
def baseStart_3802847 : Nat := 118140960795 + 3802847 * 2 ^ 59
def prefixEnd_3802847 : Nat := 4983230072969 + 3 ^ 40 * 3802847 * 2
def baseEnd_3802847 : Nat := 1952688366508588077323531

theorem tailTrace_3802847 : CollatzResearch.WordTrace tailWord_3802847 prefixEnd_3802847 1952688366508588077323531 := by
  unfold tailWord_3802847
  simp only [CollatzResearch.WordTrace]
  refine ⟨138701224853942268405398795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92467483235961512270265863 138701224853942268405398795)
  ·
    refine ⟨208051837280913402608098193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138701224853942268405398795 208051837280913402608098193)
    ·
      refine ⟨156038877960685051956073645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208051837280913402608098193 156038877960685051956073645)
      ·
        refine ⟨58514579235256894483527617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156038877960685051956073645 58514579235256894483527617)
        ·
          refine ⟨43885934426442670862645713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58514579235256894483527617 43885934426442670862645713)
          ·
            refine ⟨32914450819832003146984285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43885934426442670862645713 32914450819832003146984285)
            ·
              refine ⟨12342919057437001180119107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32914450819832003146984285 12342919057437001180119107)
              ·
                refine ⟨18514378586155501770178661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12342919057437001180119107 18514378586155501770178661)
                ·
                  refine ⟨3471445984904156581908499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18514378586155501770178661 3471445984904156581908499)
                  ·
                    refine ⟨5207168977356234872862749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3471445984904156581908499 5207168977356234872862749)
                    ·
                      refine ⟨1952688366508588077323531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207168977356234872862749 1952688366508588077323531)
                      ·
                        rfl

theorem cell23_3802847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_3802847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802847 prefixEnd_3802847 := by exact prefixLift 3802847
  have htrace : WordTrace (prefixWord ++ tailWord_3802847) baseStart_3802847 baseEnd_3802847 := by
    simpa [prefixWord, tailWord_3802847, baseEnd_3802847] using wordTrace_append hprefix tailTrace_3802847
  have hstable : (prefixWord ++ tailWord_3802847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802847).length < 2 ^ (prefixWord ++ tailWord_3802847).sum := by decide
  have hdescent : baseEnd_3802847 < baseStart_3802847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802868 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3802868 : Nat := 118140960795 + 3802868 * 2 ^ 59
def prefixEnd_3802868 : Nat := 4983230072969 + 3 ^ 40 * 3802868 * 2
def baseEnd_3802868 : Nat := 1952699149602332495160935

theorem tailTrace_3802868 : CollatzResearch.WordTrace tailWord_3802868 prefixEnd_3802868 1952699149602332495160935 := by
  unfold tailWord_3802868
  simp only [CollatzResearch.WordTrace]
  refine ⟨69350995393433094495956629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92467993857910792661275505 69350995393433094495956629)
  ·
    refine ⟨3250827909067176304497967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69350995393433094495956629 3250827909067176304497967)
    ·
      refine ⟨4876241863600764456746951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3250827909067176304497967 4876241863600764456746951)
      ·
        refine ⟨7314362795401146685120427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876241863600764456746951 7314362795401146685120427)
        ·
          refine ⟨10971544193101720027680641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314362795401146685120427 10971544193101720027680641)
          ·
            refine ⟨8228658144826290020760481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10971544193101720027680641 8228658144826290020760481)
            ·
              refine ⟨6171493608619717515570361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228658144826290020760481 6171493608619717515570361)
              ·
                refine ⟨4628620206464788136677771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171493608619717515570361 4628620206464788136677771)
                ·
                  refine ⟨6942930309697182205016657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628620206464788136677771 6942930309697182205016657)
                  ·
                    refine ⟨5207197732272886653762493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942930309697182205016657 5207197732272886653762493)
                    ·
                      refine ⟨1952699149602332495160935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207197732272886653762493 1952699149602332495160935)
                      ·
                        rfl

theorem cell23_3802868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3802868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802868 prefixEnd_3802868 := by exact prefixLift 3802868
  have htrace : WordTrace (prefixWord ++ tailWord_3802868) baseStart_3802868 baseEnd_3802868 := by
    simpa [prefixWord, tailWord_3802868, baseEnd_3802868] using wordTrace_append hprefix tailTrace_3802868
  have hstable : (prefixWord ++ tailWord_3802868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802868).length < 2 ^ (prefixWord ++ tailWord_3802868).sum := by decide
  have hdescent : baseEnd_3802868 < baseStart_3802868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802890 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3802890 : Nat := 118140960795 + 3802890 * 2 ^ 59
def prefixEnd_3802890 : Nat := 4983230072969 + 3 ^ 40 * 3802890 * 2
def baseEnd_3802890 : Nat := 1952710446176731409085833

theorem tailTrace_3802890 : CollatzResearch.WordTrace tailWord_3802890 prefixEnd_3802890 1952710446176731409085833 := by
  unfold tailWord_3802890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34675698298196621687303531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92468528795190991166142749 34675698298196621687303531)
  ·
    refine ⟨52013547447294932530955297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34675698298196621687303531 52013547447294932530955297)
    ·
      refine ⟨39010160585471199398216473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52013547447294932530955297 39010160585471199398216473)
      ·
        refine ⟨29257620439103399548662355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39010160585471199398216473 29257620439103399548662355)
        ·
          refine ⟨43886430658655099322993533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29257620439103399548662355 43886430658655099322993533)
          ·
            refine ⟨16457411496995662246122575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43886430658655099322993533 16457411496995662246122575)
            ·
              refine ⟨24686117245493493369183863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16457411496995662246122575 24686117245493493369183863)
              ·
                refine ⟨37029175868240240053775795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24686117245493493369183863 37029175868240240053775795)
                ·
                  refine ⟨55543763802360360080663693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37029175868240240053775795 55543763802360360080663693)
                  ·
                    refine ⟨20828911425885135030248885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55543763802360360080663693 20828911425885135030248885)
                    ·
                      refine ⟨1952710446176731409085833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20828911425885135030248885 1952710446176731409085833)
                      ·
                        rfl

theorem cell23_3802890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3802890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802890 prefixEnd_3802890 := by exact prefixLift 3802890
  have htrace : WordTrace (prefixWord ++ tailWord_3802890) baseStart_3802890 baseEnd_3802890 := by
    simpa [prefixWord, tailWord_3802890, baseEnd_3802890] using wordTrace_append hprefix tailTrace_3802890
  have hstable : (prefixWord ++ tailWord_3802890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802890).length < 2 ^ (prefixWord ++ tailWord_3802890).sum := by decide
  have hdescent : baseEnd_3802890 < baseStart_3802890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802904 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 4, 2, 2]
def baseStart_3802904 : Nat := 118140960795 + 3802904 * 2 ^ 59
def prefixEnd_3802904 : Nat := 4983230072969 + 3 ^ 40 * 3802904 * 2
def baseEnd_3802904 : Nat := 1952717634905894354310769

theorem tailTrace_3802904 : CollatzResearch.WordTrace tailWord_3802904 prefixEnd_3802904 1952717634905894354310769 := by
  unfold tailWord_3802904
  simp only [CollatzResearch.WordTrace]
  refine ⟨69351651907367883570111883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92468869209823844760149177 69351651907367883570111883)
  ·
    refine ⟨104027477861051825355167825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69351651907367883570111883 104027477861051825355167825)
    ·
      refine ⟨78020608395788869016375869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104027477861051825355167825 78020608395788869016375869)
      ·
        refine ⟨29257728148420825881140951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78020608395788869016375869 29257728148420825881140951)
        ·
          refine ⟨43886592222631238821711427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29257728148420825881140951 43886592222631238821711427)
          ·
            refine ⟨65829888333946858232567141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43886592222631238821711427 65829888333946858232567141)
            ·
              refine ⟨12343104062615035918606339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65829888333946858232567141 12343104062615035918606339)
              ·
                refine ⟨18514656093922553877909509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12343104062615035918606339 18514656093922553877909509)
                ·
                  refine ⟨3471498017610478852108033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18514656093922553877909509 3471498017610478852108033)
                  ·
                    refine ⟨2603623513207859139081025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3471498017610478852108033 2603623513207859139081025)
                    ·
                      refine ⟨1952717634905894354310769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603623513207859139081025 1952717634905894354310769)
                      ·
                        rfl

theorem cell23_3802904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_3802904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802904 prefixEnd_3802904 := by exact prefixLift 3802904
  have htrace : WordTrace (prefixWord ++ tailWord_3802904) baseStart_3802904 baseEnd_3802904 := by
    simpa [prefixWord, tailWord_3802904, baseEnd_3802904] using wordTrace_append hprefix tailTrace_3802904
  have hstable : (prefixWord ++ tailWord_3802904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802904).length < 2 ^ (prefixWord ++ tailWord_3802904).sum := by decide
  have hdescent : baseEnd_3802904 < baseStart_3802904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802940 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_3802940 : Nat := 118140960795 + 3802940 * 2 ^ 59
def prefixEnd_3802940 : Nat := 4983230072969 + 3 ^ 40 * 3802940 * 2
def baseEnd_3802940 : Nat := 650912040069818737820201

theorem tailTrace_3802940 : CollatzResearch.WordTrace tailWord_3802940 prefixEnd_3802940 650912040069818737820201 := by
  unfold tailWord_3802940
  simp only [CollatzResearch.WordTrace]
  refine ⟨69352308421302672644267137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92469744561736896859022849 69352308421302672644267137)
  ·
    refine ⟨52014231315977004483200353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69352308421302672644267137 52014231315977004483200353)
    ·
      refine ⟨39010673486982753362400265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52014231315977004483200353 39010673486982753362400265)
      ·
        refine ⟨29258005115237065021800199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39010673486982753362400265 29258005115237065021800199)
        ·
          refine ⟨43887007672855597532700299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29258005115237065021800199 43887007672855597532700299)
          ·
            refine ⟨65830511509283396299050449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43887007672855597532700299 65830511509283396299050449)
            ·
              refine ⟨49372883631962547224287837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65830511509283396299050449 49372883631962547224287837)
              ·
                refine ⟨18514831361985955209107939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49372883631962547224287837 18514831361985955209107939)
                ·
                  refine ⟨27772247042978932813661909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18514831361985955209107939 27772247042978932813661909)
                  ·
                    refine ⟨650912040069818737820201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27772247042978932813661909 650912040069818737820201)
                    ·
                      rfl

theorem cell23_3802940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_3802940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802940 prefixEnd_3802940 := by exact prefixLift 3802940
  have htrace : WordTrace (prefixWord ++ tailWord_3802940) baseStart_3802940 baseEnd_3802940 := by
    simpa [prefixWord, tailWord_3802940, baseEnd_3802940] using wordTrace_append hprefix tailTrace_3802940
  have hstable : (prefixWord ++ tailWord_3802940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802940).length < 2 ^ (prefixWord ++ tailWord_3802940).sum := by decide
  have hdescent : baseEnd_3802940 < baseStart_3802940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802960 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_3802960 : Nat := 118140960795 + 3802960 * 2 ^ 59
def prefixEnd_3802960 : Nat := 4983230072969 + 3 ^ 40 * 3802960 * 2
def baseEnd_3802960 : Nat := 1952746389822546135210511

theorem tailTrace_3802960 : CollatzResearch.WordTrace tailWord_3802960 prefixEnd_3802960 1952746389822546135210511 := by
  unfold tailWord_3802960
  simp only [CollatzResearch.WordTrace]
  refine ⟨69352673151266444352131167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92470230868355259136174889 69352673151266444352131167)
  ·
    refine ⟨104029009726899666528196751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69352673151266444352131167 104029009726899666528196751)
    ·
      refine ⟨156043514590349499792295127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104029009726899666528196751 156043514590349499792295127)
      ·
        refine ⟨234065271885524249688442691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156043514590349499792295127 234065271885524249688442691)
        ·
          refine ⟨351097907828286374532664037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234065271885524249688442691 351097907828286374532664037)
          ·
            refine ⟨65830857717803695224874507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351097907828286374532664037 65830857717803695224874507)
            ·
              refine ⟨98746286576705542837311761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65830857717803695224874507 98746286576705542837311761)
              ·
                refine ⟨74059714932529157127983821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98746286576705542837311761 74059714932529157127983821)
                ·
                  refine ⟨27772393099698433922993933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74059714932529157127983821 27772393099698433922993933)
                  ·
                    refine ⟨10414647412386912721122725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27772393099698433922993933 10414647412386912721122725)
                    ·
                      refine ⟨1952746389822546135210511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10414647412386912721122725 1952746389822546135210511)
                      ·
                        rfl

theorem cell23_3802960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_3802960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802960 prefixEnd_3802960 := by exact prefixLift 3802960
  have htrace : WordTrace (prefixWord ++ tailWord_3802960) baseStart_3802960 baseEnd_3802960 := by
    simpa [prefixWord, tailWord_3802960, baseEnd_3802960] using wordTrace_append hprefix tailTrace_3802960
  have hstable : (prefixWord ++ tailWord_3802960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802960).length < 2 ^ (prefixWord ++ tailWord_3802960).sum := by decide
  have hdescent : baseEnd_3802960 < baseStart_3802960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802961 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 5]
def baseStart_3802961 : Nat := 118140960795 + 3802961 * 2 ^ 59
def prefixEnd_3802961 : Nat := 4983230072969 + 3 ^ 40 * 3802961 * 2
def baseEnd_3802961 : Nat := 216971878144800070144223

theorem tailTrace_3802961 : CollatzResearch.WordTrace tailWord_3802961 prefixEnd_3802961 216971878144800070144223 := by
  unfold tailWord_3802961
  simp only [CollatzResearch.WordTrace]
  refine ⟨138705382775529265875048737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92470255183686177250032491 138705382775529265875048737)
  ·
    refine ⟨104029037081646949406286553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138705382775529265875048737 104029037081646949406286553)
    ·
      refine ⟨78021777811235212054714915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104029037081646949406286553 78021777811235212054714915)
      ·
        refine ⟨117032666716852818082072373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78021777811235212054714915 117032666716852818082072373)
        ·
          refine ⟨10971812504704951695194285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117032666716852818082072373 10971812504704951695194285)
          ·
            refine ⟨4114429689264356885697857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10971812504704951695194285 4114429689264356885697857)
            ·
              refine ⟨3085822266948267664273393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4114429689264356885697857 3085822266948267664273393)
              ·
                refine ⟨2314366700211200748205045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085822266948267664273393 2314366700211200748205045)
                ·
                  refine ⟨216971878144800070144223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2314366700211200748205045 216971878144800070144223)
                  ·
                    rfl

theorem cell23_3802961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 5].length) (baseStart_3802961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802961 prefixEnd_3802961 := by exact prefixLift 3802961
  have htrace : WordTrace (prefixWord ++ tailWord_3802961) baseStart_3802961 baseEnd_3802961 := by
    simpa [prefixWord, tailWord_3802961, baseEnd_3802961] using wordTrace_append hprefix tailTrace_3802961
  have hstable : (prefixWord ++ tailWord_3802961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802961).length < 2 ^ (prefixWord ++ tailWord_3802961).sum := by decide
  have hdescent : baseEnd_3802961 < baseStart_3802961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802964 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_3802964 : Nat := 118140960795 + 3802964 * 2 ^ 59
def prefixEnd_3802964 : Nat := 4983230072969 + 3 ^ 40 * 3802964 * 2
def baseEnd_3802964 : Nat := 1952748443745164119560493

theorem tailTrace_3802964 : CollatzResearch.WordTrace tailWord_3802964 prefixEnd_3802964 1952748443745164119560493 := by
  unfold tailWord_3802964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69352746097259198693703973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92470328129678931591605297 69352746097259198693703973)
  ·
    refine ⟨13003639893236099755069495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69352746097259198693703973 13003639893236099755069495)
    ·
      refine ⟨19505459839854149632604243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13003639893236099755069495 19505459839854149632604243)
      ·
        refine ⟨29258189759781224448906365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19505459839854149632604243 29258189759781224448906365)
        ·
          refine ⟨10971821159917959168339887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29258189759781224448906365 10971821159917959168339887)
          ·
            refine ⟨16457731739876938752509831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10971821159917959168339887 16457731739876938752509831)
            ·
              refine ⟨24686597609815408128764747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16457731739876938752509831 24686597609815408128764747)
              ·
                refine ⟨37029896414723112193147121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24686597609815408128764747 37029896414723112193147121)
                ·
                  refine ⟨27772422311042334144860341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37029896414723112193147121 27772422311042334144860341)
                  ·
                    refine ⟨2603664591660218826080657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27772422311042334144860341 2603664591660218826080657)
                    ·
                      refine ⟨1952748443745164119560493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603664591660218826080657 1952748443745164119560493)
                      ·
                        rfl

theorem cell23_3802964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_3802964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802964 prefixEnd_3802964 := by exact prefixLift 3802964
  have htrace : WordTrace (prefixWord ++ tailWord_3802964) baseStart_3802964 baseEnd_3802964 := by
    simpa [prefixWord, tailWord_3802964, baseEnd_3802964] using wordTrace_append hprefix tailTrace_3802964
  have hstable : (prefixWord ++ tailWord_3802964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802964).length < 2 ^ (prefixWord ++ tailWord_3802964).sum := by decide
  have hdescent : baseEnd_3802964 < baseStart_3802964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803087 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_3803087 : Nat := 118140960795 + 3803087 * 2 ^ 59
def prefixEnd_3803087 : Nat := 4983230072969 + 3 ^ 40 * 3803087 * 2
def baseEnd_3803087 : Nat := 1952811601865667138322427

theorem tailTrace_3803087 : CollatzResearch.WordTrace tailWord_3803087 prefixEnd_3803087 1952811601865667138322427 := by
  unfold tailWord_3803087
  simp only [CollatzResearch.WordTrace]
  refine ⟨138709978373072789394135515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92473318915381859596090343 138709978373072789394135515)
  ·
    refine ⟨208064967559609184091203273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138709978373072789394135515 208064967559609184091203273)
    ·
      refine ⟨156048725669706888068402455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208064967559609184091203273 156048725669706888068402455)
      ·
        refine ⟨234073088504560332102603683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156048725669706888068402455 234073088504560332102603683)
        ·
          refine ⟨351109632756840498153905525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234073088504560332102603683 351109632756840498153905525)
          ·
            refine ⟨32916528070953796701928643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351109632756840498153905525 32916528070953796701928643)
            ·
              refine ⟨49374792106430695052892965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32916528070953796701928643 49374792106430695052892965)
              ·
                refine ⟨9257773519955755322417431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49374792106430695052892965 9257773519955755322417431)
                ·
                  refine ⟨13886660279933632983626147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257773519955755322417431 13886660279933632983626147)
                  ·
                    refine ⟨20829990419900449475439221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13886660279933632983626147 20829990419900449475439221)
                    ·
                      refine ⟨1952811601865667138322427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20829990419900449475439221 1952811601865667138322427)
                      ·
                        rfl

theorem cell23_3803087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_3803087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803087 prefixEnd_3803087 := by exact prefixLift 3803087
  have htrace : WordTrace (prefixWord ++ tailWord_3803087) baseStart_3803087 baseEnd_3803087 := by
    simpa [prefixWord, tailWord_3803087, baseEnd_3803087] using wordTrace_append hprefix tailTrace_3803087
  have hstable : (prefixWord ++ tailWord_3803087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803087).length < 2 ^ (prefixWord ++ tailWord_3803087).sum := by decide
  have hdescent : baseEnd_3803087 < baseStart_3803087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803098 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_3803098 : Nat := 118140960795 + 3803098 * 2 ^ 59
def prefixEnd_3803098 : Nat := 4983230072969 + 3 ^ 40 * 3803098 * 2
def baseEnd_3803098 : Nat := 650939083384288865094959

theorem tailTrace_3803098 : CollatzResearch.WordTrace tailWord_3803098 prefixEnd_3803098 650939083384288865094959 := by
  unfold tailWord_3803098
  simp only [CollatzResearch.WordTrace]
  refine ⟨34677594894008234568196487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92473586384021958848523965 34677594894008234568196487)
  ·
    refine ⟨52016392341012351852294731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34677594894008234568196487 52016392341012351852294731)
    ·
      refine ⟨78024588511518527778442097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52016392341012351852294731 78024588511518527778442097)
      ·
        refine ⟨58518441383638895833831573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78024588511518527778442097 58518441383638895833831573)
        ·
          refine ⟨2743051939858073242210855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58518441383638895833831573 2743051939858073242210855)
          ·
            refine ⟨4114577909787109863316283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743051939858073242210855 4114577909787109863316283)
            ·
              refine ⟨6171866864680664794974425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114577909787109863316283 6171866864680664794974425)
              ·
                refine ⟨4628900148510498596230819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171866864680664794974425 4628900148510498596230819)
                ·
                  refine ⟨6943350222765747894346229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628900148510498596230819 6943350222765747894346229)
                  ·
                    refine ⟨650939083384288865094959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6943350222765747894346229 650939083384288865094959)
                    ·
                      rfl

theorem cell23_3803098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_3803098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803098 prefixEnd_3803098 := by exact prefixLift 3803098
  have htrace : WordTrace (prefixWord ++ tailWord_3803098) baseStart_3803098 baseEnd_3803098 := by
    simpa [prefixWord, tailWord_3803098, baseEnd_3803098] using wordTrace_append hprefix tailTrace_3803098
  have hstable : (prefixWord ++ tailWord_3803098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803098).length < 2 ^ (prefixWord ++ tailWord_3803098).sum := by decide
  have hdescent : baseEnd_3803098 < baseStart_3803098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803101 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3803101 : Nat := 118140960795 + 3803101 * 2 ^ 59
def prefixEnd_3803101 : Nat := 4983230072969 + 3 ^ 40 * 3803101 * 2
def baseEnd_3803101 : Nat := 1952818790594830083547363

theorem tailTrace_3803101 : CollatzResearch.WordTrace tailWord_3803101 prefixEnd_3803101 1952818790594830083547363 := by
  unfold tailWord_3803101
  simp only [CollatzResearch.WordTrace]
  refine ⟨138710488995022069785145157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92473659330014713190096771 138710488995022069785145157)
  ·
    refine ⟨26008216686566638084714717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138710488995022069785145157 26008216686566638084714717)
    ·
      refine ⟨9753081257462489281768019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26008216686566638084714717 9753081257462489281768019)
      ·
        refine ⟨14629621886193733922652029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9753081257462489281768019 14629621886193733922652029)
        ·
          refine ⟨5486108207322650220994511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14629621886193733922652029 5486108207322650220994511)
          ·
            refine ⟨8229162310983975331491767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486108207322650220994511 8229162310983975331491767)
            ·
              refine ⟨12343743466475962997237651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229162310983975331491767 12343743466475962997237651)
              ·
                refine ⟨18515615199713944495856477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12343743466475962997237651 18515615199713944495856477)
                ·
                  refine ⟨6943355699892729185946179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18515615199713944495856477 6943355699892729185946179)
                  ·
                    refine ⟨10415033549839093778919269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943355699892729185946179 10415033549839093778919269)
                    ·
                      refine ⟨1952818790594830083547363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10415033549839093778919269 1952818790594830083547363)
                      ·
                        rfl

theorem cell23_3803101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3803101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803101 prefixEnd_3803101 := by exact prefixLift 3803101
  have htrace : WordTrace (prefixWord ++ tailWord_3803101) baseStart_3803101 baseEnd_3803101 := by
    simpa [prefixWord, tailWord_3803101, baseEnd_3803101] using wordTrace_append hprefix tailTrace_3803101
  have hstable : (prefixWord ++ tailWord_3803101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803101).length < 2 ^ (prefixWord ++ tailWord_3803101).sum := by decide
  have hdescent : baseEnd_3803101 < baseStart_3803101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803107 : List Nat := [1, 1, 1, 6, 1, 2, 2, 9]
def baseStart_3803107 : Nat := 118140960795 + 3803107 * 2 ^ 59
def prefixEnd_3803107 : Nat := 4983230072969 + 3 ^ 40 * 3803107 * 2
def baseEnd_3803107 : Nat := 72326735980694705928605

theorem tailTrace_3803107 : CollatzResearch.WordTrace tailWord_3803107 prefixEnd_3803107 72326735980694705928605 := by
  unfold tailWord_3803107
  simp only [CollatzResearch.WordTrace]
  refine ⟨138710707833000332809863575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92473805222000221873242383 138710707833000332809863575)
  ·
    refine ⟨208066061749500499214795363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138710707833000332809863575 208066061749500499214795363)
    ·
      refine ⟨312099092624250748822193045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208066061749500499214795363 312099092624250748822193045)
      ·
        refine ⟨14629644966761753851040299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312099092624250748822193045 14629644966761753851040299)
        ·
          refine ⟨21944467450142630776560449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14629644966761753851040299 21944467450142630776560449)
          ·
            refine ⟨16458350587606973082420337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21944467450142630776560449 16458350587606973082420337)
            ·
              refine ⟨12343762940705229811815253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16458350587606973082420337 12343762940705229811815253)
              ·
                refine ⟨72326735980694705928605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12343762940705229811815253 72326735980694705928605)
                ·
                  rfl

theorem cell23_3803107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 9].length) (baseStart_3803107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803107 prefixEnd_3803107 := by exact prefixLift 3803107
  have htrace : WordTrace (prefixWord ++ tailWord_3803107) baseStart_3803107 baseEnd_3803107 := by
    simpa [prefixWord, tailWord_3803107, baseEnd_3803107] using wordTrace_append hprefix tailTrace_3803107
  have hstable : (prefixWord ++ tailWord_3803107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803107).length < 2 ^ (prefixWord ++ tailWord_3803107).sum := by decide
  have hdescent : baseEnd_3803107 < baseStart_3803107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803114 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_3803114 : Nat := 118140960795 + 3803114 * 2 ^ 59
def prefixEnd_3803114 : Nat := 4983230072969 + 3 ^ 40 * 3803114 * 2
def baseEnd_3803114 : Nat := 1952825465843338532684803

theorem tailTrace_3803114 : CollatzResearch.WordTrace tailWord_3803114 prefixEnd_3803114 1952825465843338532684803 := by
  unfold tailWord_3803114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34677740785993743251342099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92473975429316648670245597 34677740785993743251342099)
  ·
    refine ⟨52016611178990614877013149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34677740785993743251342099 52016611178990614877013149)
    ·
      refine ⟨19506229192121480578879931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52016611178990614877013149 19506229192121480578879931)
      ·
        refine ⟨29259343788182220868319897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19506229192121480578879931 29259343788182220868319897)
        ·
          refine ⟨21944507841136665651239923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29259343788182220868319897 21944507841136665651239923)
          ·
            refine ⟨32916761761704998476859885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21944507841136665651239923 32916761761704998476859885)
            ·
              refine ⟨12343785660639374428822457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32916761761704998476859885 12343785660639374428822457)
              ·
                refine ⟨9257839245479530821616843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12343785660639374428822457 9257839245479530821616843)
                ·
                  refine ⟨13886758868219296232425265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257839245479530821616843 13886758868219296232425265)
                  ·
                    refine ⟨10415069151164472174318949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13886758868219296232425265 10415069151164472174318949)
                    ·
                      refine ⟨1952825465843338532684803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10415069151164472174318949 1952825465843338532684803)
                      ·
                        rfl

theorem cell23_3803114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_3803114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803114 prefixEnd_3803114 := by exact prefixLift 3803114
  have htrace : WordTrace (prefixWord ++ tailWord_3803114) baseStart_3803114 baseEnd_3803114 := by
    simpa [prefixWord, tailWord_3803114, baseEnd_3803114] using wordTrace_append hprefix tailTrace_3803114
  have hstable : (prefixWord ++ tailWord_3803114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803114).length < 2 ^ (prefixWord ++ tailWord_3803114).sum := by decide
  have hdescent : baseEnd_3803114 < baseStart_3803114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803118 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_3803118 : Nat := 118140960795 + 3803118 * 2 ^ 59
def prefixEnd_3803118 : Nat := 4983230072969 + 3 ^ 40 * 3803118 * 2
def baseEnd_3803118 : Nat := 1952827519765956517034785

theorem tailTrace_3803118 : CollatzResearch.WordTrace tailWord_3803118 prefixEnd_3803118 1952827519765956517034785 := by
  unfold tailWord_3803118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17338888629495060211064251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92474072690640321125676005 17338888629495060211064251)
  ·
    refine ⟨26008332944242590316596377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17338888629495060211064251 26008332944242590316596377)
    ·
      refine ⟨19506249708181942737447283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26008332944242590316596377 19506249708181942737447283)
      ·
        refine ⟨29259374562272914106170925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19506249708181942737447283 29259374562272914106170925)
        ·
          refine ⟨10972265460852342789814097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29259374562272914106170925 10972265460852342789814097)
          ·
            refine ⟨8229199095639257092360573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10972265460852342789814097 8229199095639257092360573)
            ·
              refine ⟨3085949660864721409635215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8229199095639257092360573 3085949660864721409635215)
              ·
                refine ⟨4628924491297082114452823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085949660864721409635215 4628924491297082114452823)
                ·
                  refine ⟨6943386736945623171679235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628924491297082114452823 6943386736945623171679235)
                  ·
                    refine ⟨10415080105418434757518853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943386736945623171679235 10415080105418434757518853)
                    ·
                      refine ⟨1952827519765956517034785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10415080105418434757518853 1952827519765956517034785)
                      ·
                        rfl

theorem cell23_3803118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_3803118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803118 prefixEnd_3803118 := by exact prefixLift 3803118
  have htrace : WordTrace (prefixWord ++ tailWord_3803118) baseStart_3803118 baseEnd_3803118 := by
    simpa [prefixWord, tailWord_3803118, baseEnd_3803118] using wordTrace_append hprefix tailTrace_3803118
  have hstable : (prefixWord ++ tailWord_3803118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803118).length < 2 ^ (prefixWord ++ tailWord_3803118).sum := by decide
  have hdescent : baseEnd_3803118 < baseStart_3803118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803121 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_3803121 : Nat := 118140960795 + 3803121 * 2 ^ 59
def prefixEnd_3803121 : Nat := 4983230072969 + 3 ^ 40 * 3803121 * 2
def baseEnd_3803121 : Nat := 1952829060207920005297271

theorem tailTrace_3803121 : CollatzResearch.WordTrace tailWord_3803121 prefixEnd_3803121 1952829060207920005297271 := by
  unfold tailWord_3803121
  simp only [CollatzResearch.WordTrace]
  refine ⟨138711218454949613200873217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92474145636633075467248811 138711218454949613200873217)
  ·
    refine ⟨104033413841212209900654913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138711218454949613200873217 104033413841212209900654913)
    ·
      refine ⟨78025060380909157425491185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104033413841212209900654913 78025060380909157425491185)
      ·
        refine ⟨58518795285681868069118389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78025060380909157425491185 58518795285681868069118389)
        ·
          refine ⟨5486137058032675131479849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58518795285681868069118389 5486137058032675131479849)
          ·
            refine ⟨4114602793524506348609887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5486137058032675131479849 4114602793524506348609887)
            ·
              refine ⟨6171904190286759522914831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114602793524506348609887 6171904190286759522914831)
              ·
                refine ⟨9257856285430139284372247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171904190286759522914831 9257856285430139284372247)
                ·
                  refine ⟨13886784428145208926558371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257856285430139284372247 13886784428145208926558371)
                  ·
                    refine ⟨20830176642217813389837557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13886784428145208926558371 20830176642217813389837557)
                    ·
                      refine ⟨1952829060207920005297271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20830176642217813389837557 1952829060207920005297271)
                      ·
                        rfl

theorem cell23_3803121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_3803121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803121 prefixEnd_3803121 := by exact prefixLift 3803121
  have htrace : WordTrace (prefixWord ++ tailWord_3803121) baseStart_3803121 baseEnd_3803121 := by
    simpa [prefixWord, tailWord_3803121, baseEnd_3803121] using wordTrace_append hprefix tailTrace_3803121
  have hstable : (prefixWord ++ tailWord_3803121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803121).length < 2 ^ (prefixWord ++ tailWord_3803121).sum := by decide
  have hdescent : baseEnd_3803121 < baseStart_3803121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803137 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3803137 : Nat := 118140960795 + 3803137 * 2 ^ 59
def prefixEnd_3803137 : Nat := 4983230072969 + 3 ^ 40 * 3803137 * 2
def baseEnd_3803137 : Nat := 650945758632797314232399

theorem tailTrace_3803137 : CollatzResearch.WordTrace tailWord_3803137 prefixEnd_3803137 650945758632797314232399 := by
  unfold tailWord_3803137
  simp only [CollatzResearch.WordTrace]
  refine ⟨138711802022891647933455665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92474534681927765288970443 138711802022891647933455665)
  ·
    refine ⟨104033851517168735950091749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138711802022891647933455665 104033851517168735950091749)
    ·
      refine ⟨19506347159469137990642203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104033851517168735950091749 19506347159469137990642203)
      ·
        refine ⟨29259520739203706985963305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19506347159469137990642203 29259520739203706985963305)
        ·
          refine ⟨21944640554402780239472479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29259520739203706985963305 21944640554402780239472479)
          ·
            refine ⟨32916960831604170359208719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21944640554402780239472479 32916960831604170359208719)
            ·
              refine ⟨49375441247406255538813079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32916960831604170359208719 49375441247406255538813079)
              ·
                refine ⟨74063161871109383308219619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49375441247406255538813079 74063161871109383308219619)
                ·
                  refine ⟨111094742806664074962329429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74063161871109383308219619 111094742806664074962329429)
                  ·
                    refine ⟨650945758632797314232399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111094742806664074962329429 650945758632797314232399)
                    ·
                      rfl

theorem cell23_3803137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3803137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803137 prefixEnd_3803137 := by exact prefixLift 3803137
  have htrace : WordTrace (prefixWord ++ tailWord_3803137) baseStart_3803137 baseEnd_3803137 := by
    simpa [prefixWord, tailWord_3803137, baseEnd_3803137] using wordTrace_append hprefix tailTrace_3803137
  have hstable : (prefixWord ++ tailWord_3803137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803137).length < 2 ^ (prefixWord ++ tailWord_3803137).sum := by decide
  have hdescent : baseEnd_3803137 < baseStart_3803137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803161 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 1, 3, 2]
def baseStart_3803161 : Nat := 118140960795 + 3803161 * 2 ^ 59
def prefixEnd_3803161 : Nat := 4983230072969 + 3 ^ 40 * 3803161 * 2
def baseEnd_3803161 : Nat := 1952849599434099848797087

theorem tailTrace_3803161 : CollatzResearch.WordTrace tailWord_3803161 prefixEnd_3803161 1952849599434099848797087 := by
  unfold tailWord_3803161
  simp only [CollatzResearch.WordTrace]
  refine ⟨138712677374804700032329337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92475118249869800021552891 138712677374804700032329337)
  ·
    refine ⟨104034508031103525024247003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138712677374804700032329337 104034508031103525024247003)
    ·
      refine ⟨156051762046655287536370505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104034508031103525024247003 156051762046655287536370505)
      ·
        refine ⟨117038821534991465652277879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156051762046655287536370505 117038821534991465652277879)
        ·
          refine ⟨175558232302487198478416819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117038821534991465652277879 175558232302487198478416819)
          ·
            refine ⟨263337348453730797717625229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175558232302487198478416819 263337348453730797717625229)
            ·
              refine ⟨98751505670149049144109461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263337348453730797717625229 98751505670149049144109461)
              ·
                refine ⟨4628976828288236678630131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98751505670149049144109461 4628976828288236678630131)
                ·
                  refine ⟨6943465242432355017945197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628976828288236678630131 6943465242432355017945197)
                  ·
                    refine ⟨2603799465912133131729449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6943465242432355017945197 2603799465912133131729449)
                    ·
                      refine ⟨1952849599434099848797087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2603799465912133131729449 1952849599434099848797087)
                      ·
                        rfl

theorem cell23_3803161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_3803161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803161 prefixEnd_3803161 := by exact prefixLift 3803161
  have htrace : WordTrace (prefixWord ++ tailWord_3803161) baseStart_3803161 baseEnd_3803161 := by
    simpa [prefixWord, tailWord_3803161, baseEnd_3803161] using wordTrace_append hprefix tailTrace_3803161
  have hstable : (prefixWord ++ tailWord_3803161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803161).length < 2 ^ (prefixWord ++ tailWord_3803161).sum := by decide
  have hdescent : baseEnd_3803161 < baseStart_3803161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803167 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 8]
def baseStart_3803167 : Nat := 118140960795 + 3803167 * 2 ^ 59
def prefixEnd_3803167 : Nat := 4983230072969 + 3 ^ 40 * 3803167 * 2
def baseEnd_3803167 : Nat := 650950893439342275107353

theorem tailTrace_3803167 : CollatzResearch.WordTrace tailWord_3803167 prefixEnd_3803167 650950893439342275107353 := by
  unfold tailWord_3803167
  simp only [CollatzResearch.WordTrace]
  refine ⟨138712896212782963057047755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92475264141855308704698503 138712896212782963057047755)
  ·
    refine ⟨208069344319174444585571633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138712896212782963057047755 208069344319174444585571633)
    ·
      refine ⟨156052008239380833439178725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208069344319174444585571633 156052008239380833439178725)
      ·
        refine ⟨29259751544883906269846011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156052008239380833439178725 29259751544883906269846011)
        ·
          refine ⟨43889627317325859404769017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29259751544883906269846011 43889627317325859404769017)
          ·
            refine ⟨32917220487994394553576763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43889627317325859404769017 32917220487994394553576763)
            ·
              refine ⟨49375830731991591830365145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32917220487994394553576763 49375830731991591830365145)
              ·
                refine ⟨37031873048993693872773859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49375830731991591830365145 37031873048993693872773859)
                ·
                  refine ⟨55547809573490540809160789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37031873048993693872773859 55547809573490540809160789)
                  ·
                    refine ⟨650950893439342275107353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55547809573490540809160789 650950893439342275107353)
                    ·
                      rfl

theorem cell23_3803167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_3803167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803167 prefixEnd_3803167 := by exact prefixLift 3803167
  have htrace : WordTrace (prefixWord ++ tailWord_3803167) baseStart_3803167 baseEnd_3803167 := by
    simpa [prefixWord, tailWord_3803167, baseEnd_3803167] using wordTrace_append hprefix tailTrace_3803167
  have hstable : (prefixWord ++ tailWord_3803167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803167).length < 2 ^ (prefixWord ++ tailWord_3803167).sum := by decide
  have hdescent : baseEnd_3803167 < baseStart_3803167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803172 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3803172 : Nat := 118140960795 + 3803172 * 2 ^ 59
def prefixEnd_3803172 : Nat := 4983230072969 + 3 ^ 40 * 3803172 * 2
def baseEnd_3803172 : Nat := 1952855247721299305759537

theorem tailTrace_3803172 : CollatzResearch.WordTrace tailWord_3803172 prefixEnd_3803172 1952855247721299305759537 := by
  unfold tailWord_3803172
  simp only [CollatzResearch.WordTrace]
  refine ⟨69356539288882424455489885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92475385718509899273986513 69356539288882424455489885)
  ·
    refine ⟨26008702233330909170808707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69356539288882424455489885 26008702233330909170808707)
    ·
      refine ⟨39013053349996363756213061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26008702233330909170808707 39013053349996363756213061)
      ·
        refine ⟨7314947503124318204289949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39013053349996363756213061 7314947503124318204289949)
        ·
          refine ⟨2743105313671619326608731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7314947503124318204289949 2743105313671619326608731)
          ·
            refine ⟨4114657970507428989913097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743105313671619326608731 4114657970507428989913097)
            ·
              refine ⟨3085993477880571742434823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4114657970507428989913097 3085993477880571742434823)
              ·
                refine ⟨4628990216820857613652235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085993477880571742434823 4628990216820857613652235)
                ·
                  refine ⟨6943485325231286420478353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628990216820857613652235 6943485325231286420478353)
                  ·
                    refine ⟨5207613993923464815358765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943485325231286420478353 5207613993923464815358765)
                    ·
                      refine ⟨1952855247721299305759537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207613993923464815358765 1952855247721299305759537)
                      ·
                        rfl

theorem cell23_3803172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3803172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803172 prefixEnd_3803172 := by exact prefixLift 3803172
  have htrace : WordTrace (prefixWord ++ tailWord_3803172) baseStart_3803172 baseEnd_3803172 := by
    simpa [prefixWord, tailWord_3803172, baseEnd_3803172] using wordTrace_append hprefix tailTrace_3803172
  have hstable : (prefixWord ++ tailWord_3803172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803172).length < 2 ^ (prefixWord ++ tailWord_3803172).sum := by decide
  have hdescent : baseEnd_3803172 < baseStart_3803172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803177 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_3803177 : Nat := 118140960795 + 3803177 * 2 ^ 59
def prefixEnd_3803177 : Nat := 4983230072969 + 3 ^ 40 * 3803177 * 2
def baseEnd_3803177 : Nat := 1952857815124571786197013

theorem tailTrace_3803177 : CollatzResearch.WordTrace tailWord_3803177 prefixEnd_3803177 1952857815124571786197013 := by
  unfold tailWord_3803177
  simp only [CollatzResearch.WordTrace]
  refine ⟨138713260942746734764911785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92475507295164489843274523 138713260942746734764911785)
  ·
    refine ⟨104034945707060051073683839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138713260942746734764911785 104034945707060051073683839)
    ·
      refine ⟨156052418560590076610525759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104034945707060051073683839 156052418560590076610525759)
      ·
        refine ⟨234078627840885114915788639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156052418560590076610525759 234078627840885114915788639)
        ·
          refine ⟨351117941761327672373682959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234078627840885114915788639 351117941761327672373682959)
          ·
            refine ⟨526676912641991508560524439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351117941761327672373682959 526676912641991508560524439)
            ·
              refine ⟨790015368962987262840786659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526676912641991508560524439 790015368962987262840786659)
              ·
                refine ⟨1185023053444480894261179989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790015368962987262840786659 1185023053444480894261179989)
                ·
                  refine ⟨13886988907552510479623203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1185023053444480894261179989 13886988907552510479623203)
                  ·
                    refine ⟨20830483361328765719434805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13886988907552510479623203 20830483361328765719434805)
                    ·
                      refine ⟨1952857815124571786197013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20830483361328765719434805 1952857815124571786197013)
                      ·
                        rfl

theorem cell23_3803177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_3803177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803177 prefixEnd_3803177 := by exact prefixLift 3803177
  have htrace : WordTrace (prefixWord ++ tailWord_3803177) baseStart_3803177 baseEnd_3803177 := by
    simpa [prefixWord, tailWord_3803177, baseEnd_3803177] using wordTrace_append hprefix tailTrace_3803177
  have hstable : (prefixWord ++ tailWord_3803177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803177).length < 2 ^ (prefixWord ++ tailWord_3803177).sum := by decide
  have hdescent : baseEnd_3803177 < baseStart_3803177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803214 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_3803214 : Nat := 118140960795 + 3803214 * 2 ^ 59
def prefixEnd_3803214 : Nat := 4983230072969 + 3 ^ 40 * 3803214 * 2
def baseEnd_3803214 : Nat := 216986312656532015714927

theorem tailTrace_3803214 : CollatzResearch.WordTrace tailWord_3803214 prefixEnd_3803214 216986312656532015714927 := by
  unfold tailWord_3803214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17339326305451586260501087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92476406962408460056005797 17339326305451586260501087)
  ·
    refine ⟨26008989458177379390751631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17339326305451586260501087 26008989458177379390751631)
    ·
      refine ⟨39013484187266069086127447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26008989458177379390751631 39013484187266069086127447)
      ·
        refine ⟨58520226280899103629191171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39013484187266069086127447 58520226280899103629191171)
        ·
          refine ⟨87780339421348655443786757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58520226280899103629191171 87780339421348655443786757)
          ·
            refine ⟨16458813641502872895710017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87780339421348655443786757 16458813641502872895710017)
            ·
              refine ⟨12344110231127154671782513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16458813641502872895710017 12344110231127154671782513)
              ·
                refine ⟨9258082673345366003836885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12344110231127154671782513 9258082673345366003836885)
                ·
                  refine ⟨216986312656532015714927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9258082673345366003836885 216986312656532015714927)
                  ·
                    rfl

theorem cell23_3803214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_3803214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803214 prefixEnd_3803214 := by exact prefixLift 3803214
  have htrace : WordTrace (prefixWord ++ tailWord_3803214) baseStart_3803214 baseEnd_3803214 := by
    simpa [prefixWord, tailWord_3803214, baseEnd_3803214] using wordTrace_append hprefix tailTrace_3803214
  have hstable : (prefixWord ++ tailWord_3803214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803214).length < 2 ^ (prefixWord ++ tailWord_3803214).sum := by decide
  have hdescent : baseEnd_3803214 < baseStart_3803214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803244 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_3803244 : Nat := 118140960795 + 3803244 * 2 ^ 59
def prefixEnd_3803244 : Nat := 4983230072969 + 3 ^ 40 * 3803244 * 2
def baseEnd_3803244 : Nat := 650964072776141008019735

theorem tailTrace_3803244 : CollatzResearch.WordTrace tailWord_3803244 prefixEnd_3803244 650964072776141008019735 := by
  unfold tailWord_3803244
  simp only [CollatzResearch.WordTrace]
  refine ⟨69357852316752002603800393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92477136422336003471733857 69357852316752002603800393)
  ·
    refine ⟨52018389237564001952850295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69357852316752002603800393 52018389237564001952850295)
    ·
      refine ⟨78027583856346002929275443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52018389237564001952850295 78027583856346002929275443)
      ·
        refine ⟨117041375784519004393913165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78027583856346002929275443 117041375784519004393913165)
        ·
          refine ⟨43890515919194626647717437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117041375784519004393913165 43890515919194626647717437)
          ·
            refine ⟨16458943469697984992894039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43890515919194626647717437 16458943469697984992894039)
            ·
              refine ⟨24688415204546977489341059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16458943469697984992894039 24688415204546977489341059)
              ·
                refine ⟨37032622806820466234011589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24688415204546977489341059 37032622806820466234011589)
                ·
                  refine ⟨6943616776278837418877173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37032622806820466234011589 6943616776278837418877173)
                  ·
                    refine ⟨650964072776141008019735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6943616776278837418877173 650964072776141008019735)
                    ·
                      rfl

theorem cell23_3803244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_3803244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803244 prefixEnd_3803244 := by exact prefixLift 3803244
  have htrace : WordTrace (prefixWord ++ tailWord_3803244) baseStart_3803244 baseEnd_3803244 := by
    simpa [prefixWord, tailWord_3803244, baseEnd_3803244] using wordTrace_append hprefix tailTrace_3803244
  have hstable : (prefixWord ++ tailWord_3803244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803244).length < 2 ^ (prefixWord ++ tailWord_3803244).sum := by decide
  have hdescent : baseEnd_3803244 < baseStart_3803244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803248 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 5]
def baseStart_3803248 : Nat := 118140960795 + 3803248 * 2 ^ 59
def prefixEnd_3803248 : Nat := 4983230072969 + 3 ^ 40 * 3803248 * 2
def baseEnd_3803248 : Nat := 216988252472337889823243

theorem tailTrace_3803248 : CollatzResearch.WordTrace tailWord_3803248 prefixEnd_3803248 216988252472337889823243 := by
  unfold tailWord_3803248
  simp only [CollatzResearch.WordTrace]
  refine ⟨69357925262744756945373199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92477233683659675927164265 69357925262744756945373199)
  ·
    refine ⟨104036887894117135418059799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69357925262744756945373199 104036887894117135418059799)
    ·
      refine ⟨156055331841175703127089699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104036887894117135418059799 156055331841175703127089699)
      ·
        refine ⟨234082997761763554690634549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156055331841175703127089699 234082997761763554690634549)
        ·
          refine ⟨21945281040165333252246989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234082997761763554690634549 21945281040165333252246989)
          ·
            refine ⟨8229480390061999969592621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21945281040165333252246989 8229480390061999969592621)
            ·
              refine ⟨3086055146273249988597233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8229480390061999969592621 3086055146273249988597233)
              ·
                refine ⟨2314541359704937491447925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086055146273249988597233 2314541359704937491447925)
                ·
                  refine ⟨216988252472337889823243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2314541359704937491447925 216988252472337889823243)
                  ·
                    rfl

theorem cell23_3803248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 5].length) (baseStart_3803248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803248 prefixEnd_3803248 := by exact prefixLift 3803248
  have htrace : WordTrace (prefixWord ++ tailWord_3803248) baseStart_3803248 baseEnd_3803248 := by
    simpa [prefixWord, tailWord_3803248, baseEnd_3803248] using wordTrace_append hprefix tailTrace_3803248
  have hstable : (prefixWord ++ tailWord_3803248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803248).length < 2 ^ (prefixWord ++ tailWord_3803248).sum := by decide
  have hdescent : baseEnd_3803248 < baseStart_3803248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803264 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_3803264 : Nat := 118140960795 + 3803264 * 2 ^ 59
def prefixEnd_3803264 : Nat := 4983230072969 + 3 ^ 40 * 3803264 * 2
def baseEnd_3803264 : Nat := 1952902487941512945809113

theorem tailTrace_3803264 : CollatzResearch.WordTrace tailWord_3803264 prefixEnd_3803264 1952902487941512945809113 := by
  unfold tailWord_3803264
  simp only [CollatzResearch.WordTrace]
  refine ⟨69358217046715774311664423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92477622728954365748885897 69358217046715774311664423)
  ·
    refine ⟨104037325570073661467496635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69358217046715774311664423 104037325570073661467496635)
    ·
      refine ⟨156055988355110492201244953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104037325570073661467496635 156055988355110492201244953)
      ·
        refine ⟨117041991266332869150933715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156055988355110492201244953 117041991266332869150933715)
        ·
          refine ⟨175562986899499303726400573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117041991266332869150933715 175562986899499303726400573)
          ·
            refine ⟨65836120087312238897400215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175562986899499303726400573 65836120087312238897400215)
            ·
              refine ⟨98754180130968358346100323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65836120087312238897400215 98754180130968358346100323)
              ·
                refine ⟨148131270196452537519150485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98754180130968358346100323 148131270196452537519150485)
                ·
                  refine ⟨6943653290458712696210179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148131270196452537519150485 6943653290458712696210179)
                  ·
                    refine ⟨10415479935688069044315269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943653290458712696210179 10415479935688069044315269)
                    ·
                      refine ⟨1952902487941512945809113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10415479935688069044315269 1952902487941512945809113)
                      ·
                        rfl

theorem cell23_3803264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_3803264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803264 prefixEnd_3803264 := by exact prefixLift 3803264
  have htrace : WordTrace (prefixWord ++ tailWord_3803264) baseStart_3803264 baseEnd_3803264 := by
    simpa [prefixWord, tailWord_3803264, baseEnd_3803264] using wordTrace_append hprefix tailTrace_3803264
  have hstable : (prefixWord ++ tailWord_3803264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803264).length < 2 ^ (prefixWord ++ tailWord_3803264).sum := by decide
  have hdescent : baseEnd_3803264 < baseStart_3803264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803278 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3803278 : Nat := 118140960795 + 3803278 * 2 ^ 59
def prefixEnd_3803278 : Nat := 4983230072969 + 3 ^ 40 * 3803278 * 2
def baseEnd_3803278 : Nat := 650969892223558630344683

theorem tailTrace_3803278 : CollatzResearch.WordTrace tailWord_3803278 prefixEnd_3803278 650969892223558630344683 := by
  unfold tailWord_3803278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17339618089422603626792311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92477963143587219342892325 17339618089422603626792311)
  ·
    refine ⟨26009427134133905440188467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17339618089422603626792311 26009427134133905440188467)
    ·
      refine ⟨39014140701200858160282701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26009427134133905440188467 39014140701200858160282701)
      ·
        refine ⟨14630302762950321810106013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39014140701200858160282701 14630302762950321810106013)
        ·
          refine ⟨5486363536106370678789755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14630302762950321810106013 5486363536106370678789755)
          ·
            refine ⟨8229545304159556018184633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486363536106370678789755 8229545304159556018184633)
            ·
              refine ⟨6172158978119667013638475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8229545304159556018184633 6172158978119667013638475)
              ·
                refine ⟨9258238467179500520457713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172158978119667013638475 9258238467179500520457713)
                ·
                  refine ⟨6943678850384625390343285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9258238467179500520457713 6943678850384625390343285)
                  ·
                    refine ⟨650969892223558630344683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6943678850384625390343285 650969892223558630344683)
                    ·
                      rfl

theorem cell23_3803278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3803278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803278 prefixEnd_3803278 := by exact prefixLift 3803278
  have htrace : WordTrace (prefixWord ++ tailWord_3803278) baseStart_3803278 baseEnd_3803278 := by
    simpa [prefixWord, tailWord_3803278, baseEnd_3803278] using wordTrace_append hprefix tailTrace_3803278
  have hstable : (prefixWord ++ tailWord_3803278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803278).length < 2 ^ (prefixWord ++ tailWord_3803278).sum := by decide
  have hdescent : baseEnd_3803278 < baseStart_3803278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803298 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3803298 : Nat := 118140960795 + 3803298 * 2 ^ 59
def prefixEnd_3803298 : Nat := 4983230072969 + 3 ^ 40 * 3803298 * 2
def baseEnd_3803298 : Nat := 1952919946283765812783957

theorem tailTrace_3803298 : CollatzResearch.WordTrace tailWord_3803298 prefixEnd_3803298 1952919946283765812783957 := by
  unfold tailWord_3803298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34679418543827093107516637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92478449450205581620044365 34679418543827093107516637)
  ·
    refine ⟨13004781953935159915318739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34679418543827093107516637 13004781953935159915318739)
    ·
      refine ⟨19507172930902739872978109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13004781953935159915318739 19507172930902739872978109)
      ·
        refine ⟨7315189849088527452366791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19507172930902739872978109 7315189849088527452366791)
        ·
          refine ⟨10972784773632791178550187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7315189849088527452366791 10972784773632791178550187)
          ·
            refine ⟨16459177160449186767825281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10972784773632791178550187 16459177160449186767825281)
            ·
              refine ⟨12344382870336890075868961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16459177160449186767825281 12344382870336890075868961)
              ·
                refine ⟨9258287152752667556901721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12344382870336890075868961 9258287152752667556901721)
                ·
                  refine ⟨6943715364564500667676291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9258287152752667556901721 6943715364564500667676291)
                  ·
                    refine ⟨10415573046846751001514437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943715364564500667676291 10415573046846751001514437)
                    ·
                      refine ⟨1952919946283765812783957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10415573046846751001514437 1952919946283765812783957)
                      ·
                        rfl

theorem cell23_3803298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3803298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803298 prefixEnd_3803298 := by exact prefixLift 3803298
  have htrace : WordTrace (prefixWord ++ tailWord_3803298) baseStart_3803298 baseEnd_3803298 := by
    simpa [prefixWord, tailWord_3803298, baseEnd_3803298] using wordTrace_append hprefix tailTrace_3803298
  have hstable : (prefixWord ++ tailWord_3803298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803298).length < 2 ^ (prefixWord ++ tailWord_3803298).sum := by decide
  have hdescent : baseEnd_3803298 < baseStart_3803298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803301 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_3803301 : Nat := 118140960795 + 3803301 * 2 ^ 59
def prefixEnd_3803301 : Nat := 4983230072969 + 3 ^ 40 * 3803301 * 2
def baseEnd_3803301 : Nat := 1952921486725729301046443

theorem tailTrace_3803301 : CollatzResearch.WordTrace tailWord_3803301 prefixEnd_3803301 1952921486725729301046443 := by
  unfold tailWord_3803301
  simp only [CollatzResearch.WordTrace]
  refine ⟨138717783594297503942425757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92478522396198335961617171 138717783594297503942425757)
  ·
    refine ⟨52019168847861563978409659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138717783594297503942425757 52019168847861563978409659)
    ·
      refine ⟨78028753271792345967614489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52019168847861563978409659 78028753271792345967614489)
      ·
        refine ⟨58521564953844259475710867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78028753271792345967614489 58521564953844259475710867)
        ·
          refine ⟨87782347430766389213566301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58521564953844259475710867 87782347430766389213566301)
          ·
            refine ⟨32918380286537395955087363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87782347430766389213566301 32918380286537395955087363)
            ·
              refine ⟨49377570429806093932631045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32918380286537395955087363 49377570429806093932631045)
              ·
                refine ⟨9258294455588642612368321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49377570429806093932631045 9258294455588642612368321)
                ·
                  refine ⟨6943720841691481959276241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9258294455588642612368321 6943720841691481959276241)
                  ·
                    refine ⟨5207790631268611469457181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943720841691481959276241 5207790631268611469457181)
                    ·
                      refine ⟨1952921486725729301046443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207790631268611469457181 1952921486725729301046443)
                      ·
                        rfl

theorem cell23_3803301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_3803301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803301 prefixEnd_3803301 := by exact prefixLift 3803301
  have htrace : WordTrace (prefixWord ++ tailWord_3803301) baseStart_3803301 baseEnd_3803301 := by
    simpa [prefixWord, tailWord_3803301, baseEnd_3803301] using wordTrace_append hprefix tailTrace_3803301
  have hstable : (prefixWord ++ tailWord_3803301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803301).length < 2 ^ (prefixWord ++ tailWord_3803301).sum := by decide
  have hdescent : baseEnd_3803301 < baseStart_3803301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803365 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3803365 : Nat := 118140960795 + 3803365 * 2 ^ 59
def prefixEnd_3803365 : Nat := 4983230072969 + 3 ^ 40 * 3803365 * 2
def baseEnd_3803365 : Nat := 1952954349487617050646149

theorem tailTrace_3803365 : CollatzResearch.WordTrace tailWord_3803365 prefixEnd_3803365 1952954349487617050646149 := by
  unfold tailWord_3803365
  simp only [CollatzResearch.WordTrace]
  refine ⟨138720117866065642872755549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92480078577377095248503699 138720117866065642872755549)
  ·
    refine ⟨52020044199774616077283331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138720117866065642872755549 52020044199774616077283331)
    ·
      refine ⟨78030066299661924115924997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52020044199774616077283331 78030066299661924115924997)
      ·
        refine ⟨14630637431186610771735937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78030066299661924115924997 14630637431186610771735937)
        ·
          refine ⟨10972978073389958078801953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14630637431186610771735937 10972978073389958078801953)
          ·
            refine ⟨8229733555042468559101465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10972978073389958078801953 8229733555042468559101465)
            ·
              refine ⟨6172300166281851419326099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8229733555042468559101465 6172300166281851419326099)
              ·
                refine ⟨9258450249422777128989149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172300166281851419326099 9258450249422777128989149)
                ·
                  refine ⟨3471918843533541423370931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9258450249422777128989149 3471918843533541423370931)
                  ·
                    refine ⟨5207878265300312135056397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3471918843533541423370931 5207878265300312135056397)
                    ·
                      refine ⟨1952954349487617050646149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207878265300312135056397 1952954349487617050646149)
                      ·
                        rfl

theorem cell23_3803365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3803365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803365 prefixEnd_3803365 := by exact prefixLift 3803365
  have htrace : WordTrace (prefixWord ++ tailWord_3803365) baseStart_3803365 baseEnd_3803365 := by
    simpa [prefixWord, tailWord_3803365, baseEnd_3803365] using wordTrace_append hprefix tailTrace_3803365
  have hstable : (prefixWord ++ tailWord_3803365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803365).length < 2 ^ (prefixWord ++ tailWord_3803365).sum := by decide
  have hdescent : baseEnd_3803365 < baseStart_3803365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803388 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_3803388 : Nat := 118140960795 + 3803388 * 2 ^ 59
def prefixEnd_3803388 : Nat := 4983230072969 + 3 ^ 40 * 3803388 * 2
def baseEnd_3803388 : Nat := 1952966159542670460658543

theorem tailTrace_3803388 : CollatzResearch.WordTrace tailWord_3803388 prefixEnd_3803388 1952966159542670460658543 := by
  unfold tailWord_3803388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69360478372491158900421409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92480637829988211867228545 69360478372491158900421409)
  ·
    refine ⟨52020358779368369175316057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69360478372491158900421409 52020358779368369175316057)
    ·
      refine ⟨39015269084526276881487043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52020358779368369175316057 39015269084526276881487043)
      ·
        refine ⟨58522903626789415322230565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39015269084526276881487043 58522903626789415322230565)
        ·
          refine ⟨10973044430023015372918231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58522903626789415322230565 10973044430023015372918231)
          ·
            refine ⟨16459566645034523059377347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973044430023015372918231 16459566645034523059377347)
            ·
              refine ⟨24689349967551784589066021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16459566645034523059377347 24689349967551784589066021)
              ·
                refine ⟨4629253118915959610449879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24689349967551784589066021 4629253118915959610449879)
                ·
                  refine ⟨6943879678373939415674819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629253118915959610449879 6943879678373939415674819)
                  ·
                    refine ⟨10415819517560909123512229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943879678373939415674819 10415819517560909123512229)
                    ·
                      refine ⟨1952966159542670460658543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10415819517560909123512229 1952966159542670460658543)
                      ·
                        rfl

theorem cell23_3803388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_3803388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803388 prefixEnd_3803388 := by exact prefixLift 3803388
  have htrace : WordTrace (prefixWord ++ tailWord_3803388) baseStart_3803388 baseEnd_3803388 := by
    simpa [prefixWord, tailWord_3803388, baseEnd_3803388] using wordTrace_append hprefix tailTrace_3803388
  have hstable : (prefixWord ++ tailWord_3803388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803388).length < 2 ^ (prefixWord ++ tailWord_3803388).sum := by decide
  have hdescent : baseEnd_3803388 < baseStart_3803388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803442 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_3803442 : Nat := 118140960795 + 3803442 * 2 ^ 59
def prefixEnd_3803442 : Nat := 4983230072969 + 3 ^ 40 * 3803442 * 2
def baseEnd_3803442 : Nat := 1952993887498013249383295

theorem tailTrace_3803442 : CollatzResearch.WordTrace tailWord_3803442 prefixEnd_3803442 1952993887498013249383295 := by
  unfold tailWord_3803442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34680731571696671255827145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92481950857857790015539053 34680731571696671255827145)
  ·
    refine ⟨26010548678772503441870359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34680731571696671255827145 26010548678772503441870359)
    ·
      refine ⟨39015823018158755162805539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26010548678772503441870359 39015823018158755162805539)
      ·
        refine ⟨58523734527238132744208309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39015823018158755162805539 58523734527238132744208309)
        ·
          refine ⟨5486600111928574944769529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58523734527238132744208309 5486600111928574944769529)
          ·
            refine ⟨4114950083946431208577147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5486600111928574944769529 4114950083946431208577147)
            ·
              refine ⟨6172425125919646812865721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114950083946431208577147 6172425125919646812865721)
              ·
                refine ⟨4629318844439735109649291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172425125919646812865721 4629318844439735109649291)
                ·
                  refine ⟨6943978266659602664473937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629318844439735109649291 6943978266659602664473937)
                  ·
                    refine ⟨5207983699994701998355453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943978266659602664473937 5207983699994701998355453)
                    ·
                      refine ⟨1952993887498013249383295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5207983699994701998355453 1952993887498013249383295)
                      ·
                        rfl

theorem cell23_3803442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_3803442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803442 prefixEnd_3803442 := by exact prefixLift 3803442
  have htrace : WordTrace (prefixWord ++ tailWord_3803442) baseStart_3803442 baseEnd_3803442 := by
    simpa [prefixWord, tailWord_3803442, baseEnd_3803442] using wordTrace_append hprefix tailTrace_3803442
  have hstable : (prefixWord ++ tailWord_3803442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803442).length < 2 ^ (prefixWord ++ tailWord_3803442).sum := by decide
  have hdescent : baseEnd_3803442 < baseStart_3803442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803486 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3803486 : Nat := 118140960795 + 3803486 * 2 ^ 59
def prefixEnd_3803486 : Nat := 4983230072969 + 3 ^ 40 * 3803486 * 2
def baseEnd_3803486 : Nat := 1953016480646811077233093

theorem tailTrace_3803486 : CollatzResearch.WordTrace tailWord_3803486 prefixEnd_3803486 1953016480646811077233093 := by
  unfold tailWord_3803486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340566387328410067238789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92483020732418187025273541 17340566387328410067238789)
  ·
    refine ⟨3251356197624076887607273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17340566387328410067238789 3251356197624076887607273)
    ·
      refine ⟨2438517148218057665705455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3251356197624076887607273 2438517148218057665705455)
      ·
        refine ⟨3657775722327086498558183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438517148218057665705455 3657775722327086498558183)
        ·
          refine ⟨5486663583490629747837275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657775722327086498558183 5486663583490629747837275)
          ·
            refine ⟨8229995375235944621755913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486663583490629747837275 8229995375235944621755913)
            ·
              refine ⟨6172496531426958466316935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8229995375235944621755913 6172496531426958466316935)
              ·
                refine ⟨9258744797140437699475403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172496531426958466316935 9258744797140437699475403)
                ·
                  refine ⟨13888117195710656549213105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258744797140437699475403 13888117195710656549213105)
                  ·
                    refine ⟨10416087896782992411909829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13888117195710656549213105 10416087896782992411909829)
                    ·
                      refine ⟨1953016480646811077233093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10416087896782992411909829 1953016480646811077233093)
                      ·
                        rfl

theorem cell23_3803486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3803486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803486 prefixEnd_3803486 := by exact prefixLift 3803486
  have htrace : WordTrace (prefixWord ++ tailWord_3803486) baseStart_3803486 baseEnd_3803486 := by
    simpa [prefixWord, tailWord_3803486, baseEnd_3803486] using wordTrace_append hprefix tailTrace_3803486
  have hstable : (prefixWord ++ tailWord_3803486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803486).length < 2 ^ (prefixWord ++ tailWord_3803486).sum := by decide
  have hdescent : baseEnd_3803486 < baseStart_3803486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803488 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 2, 6]
def baseStart_3803488 : Nat := 118140960795 + 3803488 * 2 ^ 59
def prefixEnd_3803488 : Nat := 4983230072969 + 3 ^ 40 * 3803488 * 2
def baseEnd_3803488 : Nat := 651005835869373356469361

theorem tailTrace_3803488 : CollatzResearch.WordTrace tailWord_3803488 prefixEnd_3803488 651005835869373356469361 := by
  unfold tailWord_3803488
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362302022310017439741559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92483069363080023252988745 69362302022310017439741559)
  ·
    refine ⟨104043453033465026159612339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69362302022310017439741559 104043453033465026159612339)
    ·
      refine ⟨156065179550197539239418509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104043453033465026159612339 156065179550197539239418509)
      ·
        refine ⟨58524442331324077214781941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156065179550197539239418509 58524442331324077214781941)
        ·
          refine ⟨5486666468561632238885807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58524442331324077214781941 5486666468561632238885807)
          ·
            refine ⟨8229999702842448358328711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486666468561632238885807 8229999702842448358328711)
            ·
              refine ⟨12344999554263672537493067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229999702842448358328711 12344999554263672537493067)
              ·
                refine ⟨18517499331395508806239601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12344999554263672537493067 18517499331395508806239601)
                ·
                  refine ⟨13888124498546631604679701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18517499331395508806239601 13888124498546631604679701)
                  ·
                    refine ⟨651005835869373356469361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13888124498546631604679701 651005835869373356469361)
                    ·
                      rfl

theorem cell23_3803488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_3803488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803488 prefixEnd_3803488 := by exact prefixLift 3803488
  have htrace : WordTrace (prefixWord ++ tailWord_3803488) baseStart_3803488 baseEnd_3803488 := by
    simpa [prefixWord, tailWord_3803488, baseEnd_3803488] using wordTrace_append hprefix tailTrace_3803488
  have hstable : (prefixWord ++ tailWord_3803488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803488).length < 2 ^ (prefixWord ++ tailWord_3803488).sum := by decide
  have hdescent : baseEnd_3803488 < baseStart_3803488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803495 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_3803495 : Nat := 118140960795 + 3803495 * 2 ^ 59
def prefixEnd_3803495 : Nat := 4983230072969 + 3 ^ 40 * 3803495 * 2
def baseEnd_3803495 : Nat := 1953021101972701542020551

theorem tailTrace_3803495 : CollatzResearch.WordTrace tailWord_3803495 prefixEnd_3803495 1953021101972701542020551 := by
  unfold tailWord_3803495
  simp only [CollatzResearch.WordTrace]
  refine ⟨138724859355594675074987939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92483239570396450049991959 138724859355594675074987939)
  ·
    refine ⟨208087289033392012612481909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138724859355594675074987939 208087289033392012612481909)
    ·
      refine ⟨19508183346880501182420179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208087289033392012612481909 19508183346880501182420179)
      ·
        refine ⟨29262275020320751773630269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508183346880501182420179 29262275020320751773630269)
        ·
          refine ⟨10973353132620281915111351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29262275020320751773630269 10973353132620281915111351)
          ·
            refine ⟨16460029698930422872667027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973353132620281915111351 16460029698930422872667027)
            ·
              refine ⟨24690044548395634309000541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16460029698930422872667027 24690044548395634309000541)
              ·
                refine ⟨9258766705648362865875203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24690044548395634309000541 9258766705648362865875203)
                ·
                  refine ⟨13888150058472544298812805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258766705648362865875203 13888150058472544298812805)
                  ·
                    refine ⟨2604028135963602056027401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13888150058472544298812805 2604028135963602056027401)
                    ·
                      refine ⟨1953021101972701542020551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604028135963602056027401 1953021101972701542020551)
                      ·
                        rfl

theorem cell23_3803495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_3803495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803495 prefixEnd_3803495 := by exact prefixLift 3803495
  have htrace : WordTrace (prefixWord ++ tailWord_3803495) baseStart_3803495 baseEnd_3803495 := by
    simpa [prefixWord, tailWord_3803495, baseEnd_3803495] using wordTrace_append hprefix tailTrace_3803495
  have hstable : (prefixWord ++ tailWord_3803495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803495).length < 2 ^ (prefixWord ++ tailWord_3803495).sum := by decide
  have hdescent : baseEnd_3803495 < baseStart_3803495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803528 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3803528 : Nat := 118140960795 + 3803528 * 2 ^ 59
def prefixEnd_3803528 : Nat := 4983230072969 + 3 ^ 40 * 3803528 * 2
def baseEnd_3803528 : Nat := 1953038046834299912907899

theorem tailTrace_3803528 : CollatzResearch.WordTrace tailWord_3803528 prefixEnd_3803528 1953038046834299912907899 := by
  unfold tailWord_3803528
  simp only [CollatzResearch.WordTrace]
  refine ⟨69363031482237560855469619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92484041976316747807292825 69363031482237560855469619)
  ·
    refine ⟨104044547223356341283204429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69363031482237560855469619 104044547223356341283204429)
    ·
      refine ⟨39016705208758627981201661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104044547223356341283204429 39016705208758627981201661)
      ·
        refine ⟨14631264453284485492950623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39016705208758627981201661 14631264453284485492950623)
        ·
          refine ⟨21946896679926728239425935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14631264453284485492950623 21946896679926728239425935)
          ·
            refine ⟨32920345019890092359138903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21946896679926728239425935 32920345019890092359138903)
            ·
              refine ⟨49380517529835138538708355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32920345019890092359138903 49380517529835138538708355)
              ·
                refine ⟨74070776294752707808062533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49380517529835138538708355 74070776294752707808062533)
                ·
                  refine ⟨13888270555266132714011725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74070776294752707808062533 13888270555266132714011725)
                  ·
                    refine ⟨5208101458224799767754397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13888270555266132714011725 5208101458224799767754397)
                    ·
                      refine ⟨1953038046834299912907899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5208101458224799767754397 1953038046834299912907899)
                      ·
                        rfl

theorem cell23_3803528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3803528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803528 prefixEnd_3803528 := by exact prefixLift 3803528
  have htrace : WordTrace (prefixWord ++ tailWord_3803528) baseStart_3803528 baseEnd_3803528 := by
    simpa [prefixWord, tailWord_3803528, baseEnd_3803528] using wordTrace_append hprefix tailTrace_3803528
  have hstable : (prefixWord ++ tailWord_3803528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803528).length < 2 ^ (prefixWord ++ tailWord_3803528).sum := by decide
  have hdescent : baseEnd_3803528 < baseStart_3803528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803529 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 2, 2, 2]
def baseStart_3803529 : Nat := 118140960795 + 3803529 * 2 ^ 59
def prefixEnd_3803529 : Nat := 4983230072969 + 3 ^ 40 * 3803529 * 2
def baseEnd_3803529 : Nat := 1953038560314954408995395

theorem tailTrace_3803529 : CollatzResearch.WordTrace tailWord_3803529 prefixEnd_3803529 1953038560314954408995395 := by
  unfold tailWord_3803529
  simp only [CollatzResearch.WordTrace]
  refine ⟨138726099437471498881725641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92484066291647665921150427 138726099437471498881725641)
  ·
    refine ⟨104044574578103624161294231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138726099437471498881725641 104044574578103624161294231)
    ·
      refine ⟨156066861867155436241941347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104044574578103624161294231 156066861867155436241941347)
      ·
        refine ⟨234100292800733154362912021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156066861867155436241941347 234100292800733154362912021)
        ·
          refine ⟨10973451225034366610761501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234100292800733154362912021 10973451225034366610761501)
          ·
            refine ⟨4115044209387887479035563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10973451225034366610761501 4115044209387887479035563)
            ·
              refine ⟨6172566314081831218553345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115044209387887479035563 6172566314081831218553345)
              ·
                refine ⟨4629424735561373413915009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172566314081831218553345 4629424735561373413915009)
                ·
                  refine ⟨3472068551671030060436257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629424735561373413915009 3472068551671030060436257)
                  ·
                    refine ⟨2604051413753272545327193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3472068551671030060436257 2604051413753272545327193)
                    ·
                      refine ⟨1953038560314954408995395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604051413753272545327193 1953038560314954408995395)
                      ·
                        rfl

theorem cell23_3803529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 2, 2].length) (baseStart_3803529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803529 prefixEnd_3803529 := by exact prefixLift 3803529
  have htrace : WordTrace (prefixWord ++ tailWord_3803529) baseStart_3803529 baseEnd_3803529 := by
    simpa [prefixWord, tailWord_3803529, baseEnd_3803529] using wordTrace_append hprefix tailTrace_3803529
  have hstable : (prefixWord ++ tailWord_3803529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803529).length < 2 ^ (prefixWord ++ tailWord_3803529).sum := by decide
  have hdescent : baseEnd_3803529 < baseStart_3803529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803541 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3803541 : Nat := 118140960795 + 3803541 * 2 ^ 59
def prefixEnd_3803541 : Nat := 4983230072969 + 3 ^ 40 * 3803541 * 2
def baseEnd_3803541 : Nat := 1953044722082808362045339

theorem tailTrace_3803541 : CollatzResearch.WordTrace tailWord_3803541 prefixEnd_3803541 1953044722082808362045339 := by
  unfold tailWord_3803541
  simp only [CollatzResearch.WordTrace]
  refine ⟨138726537113428024931162477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92484358075618683287441651 138726537113428024931162477)
  ·
    refine ⟨52022451417535509349185929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138726537113428024931162477 52022451417535509349185929)
    ·
      refine ⟨39016838563151632011889447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52022451417535509349185929 39016838563151632011889447)
      ·
        refine ⟨58525257844727448017834171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39016838563151632011889447 58525257844727448017834171)
        ·
          refine ⟨87787886767091172026751257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58525257844727448017834171 87787886767091172026751257)
          ·
            refine ⟨65840915075318379020063443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87787886767091172026751257 65840915075318379020063443)
            ·
              refine ⟨98761372612977568530095165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65840915075318379020063443 98761372612977568530095165)
              ·
                refine ⟨37035514729866588198785687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98761372612977568530095165 37035514729866588198785687)
                ·
                  refine ⟨55553272094799882298178531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37035514729866588198785687 55553272094799882298178531)
                  ·
                    refine ⟨83329908142199823447267797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55553272094799882298178531 83329908142199823447267797)
                    ·
                      refine ⟨1953044722082808362045339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83329908142199823447267797 1953044722082808362045339)
                      ·
                        rfl

theorem cell23_3803541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3803541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803541 prefixEnd_3803541 := by exact prefixLift 3803541
  have htrace : WordTrace (prefixWord ++ tailWord_3803541) baseStart_3803541 baseEnd_3803541 := by
    simpa [prefixWord, tailWord_3803541, baseEnd_3803541] using wordTrace_append hprefix tailTrace_3803541
  have hstable : (prefixWord ++ tailWord_3803541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803541).length < 2 ^ (prefixWord ++ tailWord_3803541).sum := by decide
  have hdescent : baseEnd_3803541 < baseStart_3803541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803571 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_3803571 : Nat := 118140960795 + 3803571 * 2 ^ 59
def prefixEnd_3803571 : Nat := 4983230072969 + 3 ^ 40 * 3803571 * 2
def baseEnd_3803571 : Nat := 1953060126502443244670201

theorem tailTrace_3803571 : CollatzResearch.WordTrace tailWord_3803571 prefixEnd_3803571 1953060126502443244670201 := by
  unfold tailWord_3803571
  simp only [CollatzResearch.WordTrace]
  refine ⟨138727631303319340054754567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92485087535546226703169711 138727631303319340054754567)
  ·
    refine ⟨208091446954979010082131851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138727631303319340054754567 208091446954979010082131851)
    ·
      refine ⟨312137170432468515123197777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208091446954979010082131851 312137170432468515123197777)
      ·
        refine ⟨234102877824351386342398333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312137170432468515123197777 234102877824351386342398333)
        ·
          refine ⟨87788579184131769878399375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234102877824351386342398333 87788579184131769878399375)
          ·
            refine ⟨131682868776197654817599063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87788579184131769878399375 131682868776197654817599063)
            ·
              refine ⟨197524303164296482226398595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131682868776197654817599063 197524303164296482226398595)
              ·
                refine ⟨296286454746444723339597893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197524303164296482226398595 296286454746444723339597893)
                ·
                  refine ⟨55553710264958385626174605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296286454746444723339597893 55553710264958385626174605)
                  ·
                    refine ⟨20832641349359394609815477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55553710264958385626174605 20832641349359394609815477)
                    ·
                      refine ⟨1953060126502443244670201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20832641349359394609815477 1953060126502443244670201)
                      ·
                        rfl

theorem cell23_3803571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_3803571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803571 prefixEnd_3803571 := by exact prefixLift 3803571
  have htrace : WordTrace (prefixWord ++ tailWord_3803571) baseStart_3803571 baseEnd_3803571 := by
    simpa [prefixWord, tailWord_3803571, baseEnd_3803571] using wordTrace_append hprefix tailTrace_3803571
  have hstable : (prefixWord ++ tailWord_3803571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803571).length < 2 ^ (prefixWord ++ tailWord_3803571).sum := by decide
  have hdescent : baseEnd_3803571 < baseStart_3803571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803578 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_3803578 : Nat := 118140960795 + 3803578 * 2 ^ 59
def prefixEnd_3803578 : Nat := 4983230072969 + 3 ^ 40 * 3803578 * 2
def baseEnd_3803578 : Nat := 651021240289008239094223

theorem tailTrace_3803578 : CollatzResearch.WordTrace tailWord_3803578 prefixEnd_3803578 651021240289008239094223 := by
  unfold tailWord_3803578
  simp only [CollatzResearch.WordTrace]
  refine ⟨34681971653573495062564847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92485257742862653500172925 34681971653573495062564847)
  ·
    refine ⟨52022957480360242593847271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34681971653573495062564847 52022957480360242593847271)
    ·
      refine ⟨78034436220540363890770907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52022957480360242593847271 78034436220540363890770907)
      ·
        refine ⟨117051654330810545836156361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78034436220540363890770907 117051654330810545836156361)
        ·
          refine ⟨87788740748107909377117271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117051654330810545836156361 87788740748107909377117271)
          ·
            refine ⟨131683111122161864065675907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87788740748107909377117271 131683111122161864065675907)
            ·
              refine ⟨197524666683242796098513861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131683111122161864065675907 197524666683242796098513861)
              ·
                refine ⟨37035875003108024268471349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197524666683242796098513861 37035875003108024268471349)
                ·
                  refine ⟨3472113281541377275169189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37035875003108024268471349 3472113281541377275169189)
                  ·
                    refine ⟨651021240289008239094223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472113281541377275169189 651021240289008239094223)
                    ·
                      rfl

theorem cell23_3803578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_3803578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803578 prefixEnd_3803578 := by exact prefixLift 3803578
  have htrace : WordTrace (prefixWord ++ tailWord_3803578) baseStart_3803578 baseEnd_3803578 := by
    simpa [prefixWord, tailWord_3803578, baseEnd_3803578] using wordTrace_append hprefix tailTrace_3803578
  have hstable : (prefixWord ++ tailWord_3803578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803578).length < 2 ^ (prefixWord ++ tailWord_3803578).sum := by decide
  have hdescent : baseEnd_3803578 < baseStart_3803578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803611 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_3803611 : Nat := 118140960795 + 3803611 * 2 ^ 59
def prefixEnd_3803611 : Nat := 4983230072969 + 3 ^ 40 * 3803611 * 2
def baseEnd_3803611 : Nat := 1953080665728623088170017

theorem tailTrace_3803611 : CollatzResearch.WordTrace tailWord_3803611 prefixEnd_3803611 1953080665728623088170017 := by
  unfold tailWord_3803611
  simp only [CollatzResearch.WordTrace]
  refine ⟨138729090223174426886210687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92486060148782951257473791 138729090223174426886210687)
  ·
    refine ⟨208093635334761640329316031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138729090223174426886210687 208093635334761640329316031)
    ·
      refine ⟨312140453002142460493974047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208093635334761640329316031 312140453002142460493974047)
      ·
        refine ⟨468210679503213690740961071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312140453002142460493974047 468210679503213690740961071)
        ·
          refine ⟨702316019254820536111441607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468210679503213690740961071 702316019254820536111441607)
          ·
            refine ⟨1053474028882230804167162411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702316019254820536111441607 1053474028882230804167162411)
            ·
              refine ⟨1580211043323346206250743617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053474028882230804167162411 1580211043323346206250743617)
              ·
                refine ⟨1185158282492509654688057713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580211043323346206250743617 1185158282492509654688057713)
                ·
                  refine ⟨888868711869382241016043285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185158282492509654688057713 888868711869382241016043285)
                  ·
                    refine ⟨41665720868877292547627029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 888868711869382241016043285 41665720868877292547627029)
                    ·
                      refine ⟨1953080665728623088170017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41665720868877292547627029 1953080665728623088170017)
                      ·
                        rfl

theorem cell23_3803611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_3803611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803611 prefixEnd_3803611 := by exact prefixLift 3803611
  have htrace : WordTrace (prefixWord ++ tailWord_3803611) baseStart_3803611 baseEnd_3803611 := by
    simpa [prefixWord, tailWord_3803611, baseEnd_3803611] using wordTrace_append hprefix tailTrace_3803611
  have hstable : (prefixWord ++ tailWord_3803611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803611).length < 2 ^ (prefixWord ++ tailWord_3803611).sum := by decide
  have hdescent : baseEnd_3803611 < baseStart_3803611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803693 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 6]
def baseStart_3803693 : Nat := 118140960795 + 3803693 * 2 ^ 59
def prefixEnd_3803693 : Nat := 4983230072969 + 3 ^ 40 * 3803693 * 2
def baseEnd_3803693 : Nat := 217013641238032418593849

theorem tailTrace_3803693 : CollatzResearch.WordTrace tailWord_3803693 prefixEnd_3803693 217013641238032418593849 := by
  unfold tailWord_3803693
  simp only [CollatzResearch.WordTrace]
  refine ⟨138732081008877354890695733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92488054005918236593797155 138732081008877354890695733)
  ·
    refine ⟨13006132594582252021002725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138732081008877354890695733 13006132594582252021002725)
    ·
      refine ⟨2438649861484172253938011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13006132594582252021002725 2438649861484172253938011)
      ·
        refine ⟨3657974792226258380907017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438649861484172253938011 3657974792226258380907017)
        ·
          refine ⟨2743481094169693785680263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3657974792226258380907017 2743481094169693785680263)
          ·
            refine ⟨4115221641254540678520395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743481094169693785680263 4115221641254540678520395)
            ·
              refine ⟨6172832461881811017780593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115221641254540678520395 6172832461881811017780593)
              ·
                refine ⟨4629624346411358263335445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172832461881811017780593 4629624346411358263335445)
                ·
                  refine ⟨217013641238032418593849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4629624346411358263335445 217013641238032418593849)
                  ·
                    rfl

theorem cell23_3803693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_3803693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803693 prefixEnd_3803693 := by exact prefixLift 3803693
  have htrace : WordTrace (prefixWord ++ tailWord_3803693) baseStart_3803693 baseEnd_3803693 := by
    simpa [prefixWord, tailWord_3803693, baseEnd_3803693] using wordTrace_append hprefix tailTrace_3803693
  have hstable : (prefixWord ++ tailWord_3803693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803693).length < 2 ^ (prefixWord ++ tailWord_3803693).sum := by decide
  have hdescent : baseEnd_3803693 < baseStart_3803693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803709 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3803709 : Nat := 118140960795 + 3803709 * 2 ^ 59
def prefixEnd_3803709 : Nat := 4983230072969 + 3 ^ 40 * 3803709 * 2
def baseEnd_3803709 : Nat := 1953130986832763704744567

theorem tailTrace_3803709 : CollatzResearch.WordTrace tailWord_3803709 prefixEnd_3803709 1953130986832763704744567 := by
  unfold tailWord_3803709
  simp only [CollatzResearch.WordTrace]
  refine ⟨138732664576819389623278181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92488443051212926415518787 138732664576819389623278181)
  ·
    refine ⟨26012374608153635554364659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138732664576819389623278181 26012374608153635554364659)
    ·
      refine ⟨39018561912230453331546989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26012374608153635554364659 39018561912230453331546989)
      ·
        refine ⟨14631960717086419999330121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39018561912230453331546989 14631960717086419999330121)
        ·
          refine ⟨10973970537814814999497591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14631960717086419999330121 10973970537814814999497591)
          ·
            refine ⟨16460955806722222499246387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973970537814814999497591 16460955806722222499246387)
            ·
              refine ⟨24691433710083333748869581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16460955806722222499246387 24691433710083333748869581)
              ·
                refine ⟨9259287641281250155826093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24691433710083333748869581 9259287641281250155826093)
                ·
                  refine ⟨3472232865480468808434785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9259287641281250155826093 3472232865480468808434785)
                  ·
                    refine ⟨2604174649110351606326089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3472232865480468808434785 2604174649110351606326089)
                    ·
                      refine ⟨1953130986832763704744567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604174649110351606326089 1953130986832763704744567)
                      ·
                        rfl

theorem cell23_3803709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3803709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803709 prefixEnd_3803709 := by exact prefixLift 3803709
  have htrace : WordTrace (prefixWord ++ tailWord_3803709) baseStart_3803709 baseEnd_3803709 := by
    simpa [prefixWord, tailWord_3803709, baseEnd_3803709] using wordTrace_append hprefix tailTrace_3803709
  have hstable : (prefixWord ++ tailWord_3803709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803709).length < 2 ^ (prefixWord ++ tailWord_3803709).sum := by decide
  have hdescent : baseEnd_3803709 < baseStart_3803709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803719 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 2, 4]
def baseStart_3803719 : Nat := 118140960795 + 3803719 * 2 ^ 59
def prefixEnd_3803719 : Nat := 4983230072969 + 3 ^ 40 * 3803719 * 2
def baseEnd_3803719 : Nat := 651045373879769555206507

theorem tailTrace_3803719 : CollatzResearch.WordTrace tailWord_3803719 prefixEnd_3803719 651045373879769555206507 := by
  unfold tailWord_3803719
  simp only [CollatzResearch.WordTrace]
  refine ⟨138733029306783161331142211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92488686204522107554094807 138733029306783161331142211)
  ·
    refine ⟨208099543960174741996713317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138733029306783161331142211 208099543960174741996713317)
    ·
      refine ⟨39018664492532764124383747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208099543960174741996713317 39018664492532764124383747)
      ·
        refine ⟨58527996738799146186575621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39018664492532764124383747 58527996738799146186575621)
        ·
          refine ⟨10973999388524839909982929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58527996738799146186575621 10973999388524839909982929)
          ·
            refine ⟨8230499541393629932487197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10973999388524839909982929 8230499541393629932487197)
            ·
              refine ⟨3086437328022611224682699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8230499541393629932487197 3086437328022611224682699)
              ·
                refine ⟨4629655992033916837024049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086437328022611224682699 4629655992033916837024049)
                ·
                  refine ⟨3472241994025437627768037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629655992033916837024049 3472241994025437627768037)
                  ·
                    refine ⟨651045373879769555206507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472241994025437627768037 651045373879769555206507)
                    ·
                      rfl

theorem cell23_3803719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_3803719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803719 prefixEnd_3803719 := by exact prefixLift 3803719
  have htrace : WordTrace (prefixWord ++ tailWord_3803719) baseStart_3803719 baseEnd_3803719 := by
    simpa [prefixWord, tailWord_3803719, baseEnd_3803719] using wordTrace_append hprefix tailTrace_3803719
  have hstable : (prefixWord ++ tailWord_3803719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803719).length < 2 ^ (prefixWord ++ tailWord_3803719).sum := by decide
  have hdescent : baseEnd_3803719 < baseStart_3803719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803722 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_3803722 : Nat := 118140960795 + 3803722 * 2 ^ 59
def prefixEnd_3803722 : Nat := 4983230072969 + 3 ^ 40 * 3803722 * 2
def baseEnd_3803722 : Nat := 1953137662081272153882007

theorem tailTrace_3803722 : CollatzResearch.WordTrace tailWord_3803722 prefixEnd_3803722 1953137662081272153882007 := by
  unfold tailWord_3803722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34683284681443073210875355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92488759150514861895667613 34683284681443073210875355)
  ·
    refine ⟨52024927022164609816313033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34683284681443073210875355 52024927022164609816313033)
    ·
      refine ⟨39018695266623457362234775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52024927022164609816313033 39018695266623457362234775)
      ·
        refine ⟨58528042899935186043352163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39018695266623457362234775 58528042899935186043352163)
        ·
          refine ⟨87792064349902779065028245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58528042899935186043352163 87792064349902779065028245)
          ·
            refine ⟨4115253016401692768673199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87792064349902779065028245 4115253016401692768673199)
            ·
              refine ⟨6172879524602539153009799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115253016401692768673199 6172879524602539153009799)
              ·
                refine ⟨9259319286903808729514699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172879524602539153009799 9259319286903808729514699)
                ·
                  refine ⟨13888978930355713094272049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9259319286903808729514699 13888978930355713094272049)
                  ·
                    refine ⟨10416734197766784820704037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13888978930355713094272049 10416734197766784820704037)
                    ·
                      refine ⟨1953137662081272153882007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10416734197766784820704037 1953137662081272153882007)
                      ·
                        rfl

theorem cell23_3803722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_3803722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803722 prefixEnd_3803722 := by exact prefixLift 3803722
  have htrace : WordTrace (prefixWord ++ tailWord_3803722) baseStart_3803722 baseEnd_3803722 := by
    simpa [prefixWord, tailWord_3803722, baseEnd_3803722] using wordTrace_append hprefix tailTrace_3803722
  have hstable : (prefixWord ++ tailWord_3803722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803722).length < 2 ^ (prefixWord ++ tailWord_3803722).sum := by decide
  have hdescent : baseEnd_3803722 < baseStart_3803722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803732 : List Nat := [2, 4, 1, 1, 1, 5, 2, 7]
def baseStart_3803732 : Nat := 118140960795 + 3803732 * 2 ^ 59
def prefixEnd_3803732 : Nat := 4983230072969 + 3 ^ 40 * 3803732 * 2
def baseEnd_3803732 : Nat := 72338622106956189435443

theorem tailTrace_3803732 : CollatzResearch.WordTrace tailWord_3803732 prefixEnd_3803732 72338622106956189435443 := by
  unfold tailWord_3803732
  simp only [CollatzResearch.WordTrace]
  refine ⟨69366751727868032275682725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92489002303824043034243633 69366751727868032275682725)
  ·
    refine ⟨13006265948975256051690511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69366751727868032275682725 13006265948975256051690511)
    ·
      refine ⟨19509398923462884077535767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13006265948975256051690511 19509398923462884077535767)
      ·
        refine ⟨29264098385194326116303651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19509398923462884077535767 29264098385194326116303651)
        ·
          refine ⟨43896147577791489174455477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29264098385194326116303651 43896147577791489174455477)
          ·
            refine ⟨4115263835417952110105201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43896147577791489174455477 4115263835417952110105201)
            ·
              refine ⟨3086447876563464082578901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115263835417952110105201 3086447876563464082578901)
              ·
                refine ⟨72338622106956189435443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3086447876563464082578901 72338622106956189435443)
                ·
                  rfl

theorem cell23_3803732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 7].length) (baseStart_3803732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803732 prefixEnd_3803732 := by exact prefixLift 3803732
  have htrace : WordTrace (prefixWord ++ tailWord_3803732) baseStart_3803732 baseEnd_3803732 := by
    simpa [prefixWord, tailWord_3803732, baseEnd_3803732] using wordTrace_append hprefix tailTrace_3803732
  have hstable : (prefixWord ++ tailWord_3803732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803732).length < 2 ^ (prefixWord ++ tailWord_3803732).sum := by decide
  have hdescent : baseEnd_3803732 < baseStart_3803732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803776 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 2, 1, 3]
def baseStart_3803776 : Nat := 118140960795 + 3803776 * 2 ^ 59
def prefixEnd_3803776 : Nat := 4983230072969 + 3 ^ 40 * 3803776 * 2
def baseEnd_3803776 : Nat := 1953165390036614942606759

theorem tailTrace_3803776 : CollatzResearch.WordTrace tailWord_3803776 prefixEnd_3803776 1953165390036614942606759 := by
  unfold tailWord_3803776
  simp only [CollatzResearch.WordTrace]
  refine ⟨69367554133788330032983591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92490072178384440043978121 69367554133788330032983591)
  ·
    refine ⟨104051331200682495049475387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69367554133788330032983591 104051331200682495049475387)
    ·
      refine ⟨156076996801023742574213081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104051331200682495049475387 156076996801023742574213081)
      ·
        refine ⟨117057747600767806930659811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156076996801023742574213081 117057747600767806930659811)
        ·
          refine ⟨175586621401151710395989717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117057747600767806930659811 175586621401151710395989717)
          ·
            refine ⟨4115311439089493212406009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175586621401151710395989717 4115311439089493212406009)
            ·
              refine ⟨3086483579317119909304507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115311439089493212406009 3086483579317119909304507)
              ·
                refine ⟨4629725368975679863956761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086483579317119909304507 4629725368975679863956761)
                ·
                  refine ⟨3472294026731759897967571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629725368975679863956761 3472294026731759897967571)
                  ·
                    refine ⟨5208441040097639846951357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3472294026731759897967571 5208441040097639846951357)
                    ·
                      refine ⟨1953165390036614942606759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5208441040097639846951357 1953165390036614942606759)
                      ·
                        rfl

theorem cell23_3803776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_3803776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803776 prefixEnd_3803776 := by exact prefixLift 3803776
  have htrace : WordTrace (prefixWord ++ tailWord_3803776) baseStart_3803776 baseEnd_3803776 := by
    simpa [prefixWord, tailWord_3803776, baseEnd_3803776] using wordTrace_append hprefix tailTrace_3803776
  have hstable : (prefixWord ++ tailWord_3803776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803776).length < 2 ^ (prefixWord ++ tailWord_3803776).sum := by decide
  have hdescent : baseEnd_3803776 < baseStart_3803776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803852 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_3803852 : Nat := 118140960795 + 3803852 * 2 ^ 59
def prefixEnd_3803852 : Nat := 4983230072969 + 3 ^ 40 * 3803852 * 2
def baseEnd_3803852 : Nat := 651068138188785548418803

theorem tailTrace_3803852 : CollatzResearch.WordTrace tailWord_3803852 prefixEnd_3803852 651068138188785548418803 := by
  unfold tailWord_3803852
  simp only [CollatzResearch.WordTrace]
  refine ⟨69368940107650662522866905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92491920143534216697155873 69368940107650662522866905)
  ·
    refine ⟨52026705080737996892150179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69368940107650662522866905 52026705080737996892150179)
    ·
      refine ⟨78040057621106995338225269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52026705080737996892150179 78040057621106995338225269)
      ·
        refine ⟨7316255401978780812958619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78040057621106995338225269 7316255401978780812958619)
        ·
          refine ⟨10974383102968171219437929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7316255401978780812958619 10974383102968171219437929)
          ·
            refine ⟨8230787327226128414578447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10974383102968171219437929 8230787327226128414578447)
            ·
              refine ⟨12346180990839192621867671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230787327226128414578447 12346180990839192621867671)
              ·
                refine ⟨18519271486258788932801507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12346180990839192621867671 18519271486258788932801507)
                ·
                  refine ⟨27778907229388183399202261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18519271486258788932801507 27778907229388183399202261)
                  ·
                    refine ⟨651068138188785548418803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27778907229388183399202261 651068138188785548418803)
                    ·
                      rfl

theorem cell23_3803852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_3803852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803852 prefixEnd_3803852 := by exact prefixLift 3803852
  have htrace : WordTrace (prefixWord ++ tailWord_3803852) baseStart_3803852 baseEnd_3803852 := by
    simpa [prefixWord, tailWord_3803852, baseEnd_3803852] using wordTrace_append hprefix tailTrace_3803852
  have hstable : (prefixWord ++ tailWord_3803852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803852).length < 2 ^ (prefixWord ++ tailWord_3803852).sum := by decide
  have hdescent : baseEnd_3803852 < baseStart_3803852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803933 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3803933 : Nat := 118140960795 + 3803933 * 2 ^ 59
def prefixEnd_3803933 : Nat := 4983230072969 + 3 ^ 40 * 3803933 * 2
def baseEnd_3803933 : Nat := 651082002166456942781179

theorem tailTrace_3803933 : CollatzResearch.WordTrace tailWord_3803933 prefixEnd_3803933 651082002166456942781179 := by
  unfold tailWord_3803933
  simp only [CollatzResearch.WordTrace]
  refine ⟨138740834528007875879432453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92493889685338583919621635 138740834528007875879432453)
  ·
    refine ⟨26013906474001476727393585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138740834528007875879432453 26013906474001476727393585)
    ·
      refine ⟨19510429855501107545545189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26013906474001476727393585 19510429855501107545545189)
      ·
        refine ⟨3658205597906457664789723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19510429855501107545545189 3658205597906457664789723)
        ·
          refine ⟨5487308396859686497184585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658205597906457664789723 5487308396859686497184585)
          ·
            refine ⟨4115481297644764872888439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5487308396859686497184585 4115481297644764872888439)
            ·
              refine ⟨6173221946467147309332659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115481297644764872888439 6173221946467147309332659)
              ·
                refine ⟨9259832919700720963998989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6173221946467147309332659 9259832919700720963998989)
                ·
                  refine ⟨3472437344887770361499621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9259832919700720963998989 3472437344887770361499621)
                  ·
                    refine ⟨651082002166456942781179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472437344887770361499621 651082002166456942781179)
                    ·
                      rfl

theorem cell23_3803933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3803933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803933 prefixEnd_3803933 := by exact prefixLift 3803933
  have htrace : WordTrace (prefixWord ++ tailWord_3803933) baseStart_3803933 baseEnd_3803933 := by
    simpa [prefixWord, tailWord_3803933, baseEnd_3803933] using wordTrace_append hprefix tailTrace_3803933
  have hstable : (prefixWord ++ tailWord_3803933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803933).length < 2 ^ (prefixWord ++ tailWord_3803933).sum := by decide
  have hdescent : baseEnd_3803933 < baseStart_3803933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803946 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_3803946 : Nat := 118140960795 + 3803946 * 2 ^ 59
def prefixEnd_3803946 : Nat := 4983230072969 + 3 ^ 40 * 3803946 * 2
def baseEnd_3803946 : Nat := 217028075749764364164553

theorem tailTrace_3803946 : CollatzResearch.WordTrace tailWord_3803946 prefixEnd_3803946 217028075749764364164553 := by
  unfold tailWord_3803946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34685327169240194774913923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92494205784640519399770461 34685327169240194774913923)
  ·
    refine ⟨52027990753860292162370885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34685327169240194774913923 52027990753860292162370885)
    ·
      refine ⟨9755248266348804780444541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52027990753860292162370885 9755248266348804780444541)
      ·
        refine ⟨3658218099880801792666703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9755248266348804780444541 3658218099880801792666703)
        ·
          refine ⟨5487327149821202689000055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658218099880801792666703 5487327149821202689000055)
          ·
            refine ⟨8230990724731804033500083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5487327149821202689000055 8230990724731804033500083)
            ·
              refine ⟨12346486087097706050250125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230990724731804033500083 12346486087097706050250125)
              ·
                refine ⟨4629932282661639768843797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12346486087097706050250125 4629932282661639768843797)
                ·
                  refine ⟨217028075749764364164553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4629932282661639768843797 217028075749764364164553)
                  ·
                    rfl

theorem cell23_3803946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_3803946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803946 prefixEnd_3803946 := by exact prefixLift 3803946
  have htrace : WordTrace (prefixWord ++ tailWord_3803946) baseStart_3803946 baseEnd_3803946 := by
    simpa [prefixWord, tailWord_3803946, baseEnd_3803946] using wordTrace_append hprefix tailTrace_3803946
  have hstable : (prefixWord ++ tailWord_3803946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803946).length < 2 ^ (prefixWord ++ tailWord_3803946).sum := by decide
  have hdescent : baseEnd_3803946 < baseStart_3803946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803985 : List Nat := [1, 2, 2, 1, 17]
def baseStart_3803985 : Nat := 118140960795 + 3803985 * 2 ^ 59
def prefixEnd_3803985 : Nat := 4983230072969 + 3 ^ 40 * 3803985 * 2
def baseEnd_3803985 : Nat := 2679386430032105109593

theorem tailTrace_3803985 : CollatzResearch.WordTrace tailWord_3803985 prefixEnd_3803985 2679386430032105109593 := by
  unfold tailWord_3803985
  simp only [CollatzResearch.WordTrace]
  refine ⟨138742731123819488760325409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92495154082546325840216939 138742731123819488760325409)
  ·
    refine ⟨104057048342864616570244057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138742731123819488760325409 104057048342864616570244057)
    ·
      refine ⟨78042786257148462427683043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104057048342864616570244057 78042786257148462427683043)
      ·
        refine ⟨117064179385722693641524565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78042786257148462427683043 117064179385722693641524565)
        ·
          refine ⟨2679386430032105109593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 117064179385722693641524565 2679386430032105109593)
          ·
            rfl

theorem cell23_3803985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 17].length) (baseStart_3803985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3803985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3803985 prefixEnd_3803985 := by exact prefixLift 3803985
  have htrace : WordTrace (prefixWord ++ tailWord_3803985) baseStart_3803985 baseEnd_3803985 := by
    simpa [prefixWord, tailWord_3803985, baseEnd_3803985] using wordTrace_append hprefix tailTrace_3803985
  have hstable : (prefixWord ++ tailWord_3803985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803985).length < 2 ^ (prefixWord ++ tailWord_3803985).sum := by decide
  have hdescent : baseEnd_3803985 < baseStart_3803985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804029 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_3804029 : Nat := 118140960795 + 3804029 * 2 ^ 59
def prefixEnd_3804029 : Nat := 4983230072969 + 3 ^ 40 * 3804029 * 2
def baseEnd_3804029 : Nat := 1953295300642202452743095

theorem tailTrace_3804029 : CollatzResearch.WordTrace tailWord_3804029 prefixEnd_3804029 1953295300642202452743095 := by
  unfold tailWord_3804029
  simp only [CollatzResearch.WordTrace]
  refine ⟨138744335935660084274927141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92496223957106722849951427 138744335935660084274927141)
  ·
    refine ⟨26014562987936265801548839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138744335935660084274927141 26014562987936265801548839)
    ·
      refine ⟨39021844481904398702323259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26014562987936265801548839 39021844481904398702323259)
      ·
        refine ⟨58532766722856598053484889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39021844481904398702323259 58532766722856598053484889)
        ·
          refine ⟨43899575042142448540113667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58532766722856598053484889 43899575042142448540113667)
          ·
            refine ⟨65849362563213672810170501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43899575042142448540113667 65849362563213672810170501)
            ·
              refine ⟨12346755480602563651906969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65849362563213672810170501 12346755480602563651906969)
              ·
                refine ⟨9260066610451922738930227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12346755480602563651906969 9260066610451922738930227)
                ·
                  refine ⟨13890099915677884108395341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9260066610451922738930227 13890099915677884108395341)
                  ·
                    refine ⟨5208787468379206540648253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13890099915677884108395341 5208787468379206540648253)
                    ·
                      refine ⟨1953295300642202452743095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5208787468379206540648253 1953295300642202452743095)
                      ·
                        rfl

theorem cell23_3804029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_3804029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804029 prefixEnd_3804029 := by exact prefixLift 3804029
  have htrace : WordTrace (prefixWord ++ tailWord_3804029) baseStart_3804029 baseEnd_3804029 := by
    simpa [prefixWord, tailWord_3804029, baseEnd_3804029] using wordTrace_append hprefix tailTrace_3804029
  have hstable : (prefixWord ++ tailWord_3804029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804029).length < 2 ^ (prefixWord ++ tailWord_3804029).sum := by decide
  have hdescent : baseEnd_3804029 < baseStart_3804029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804089 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3804089 : Nat := 118140960795 + 3804089 * 2 ^ 59
def prefixEnd_3804089 : Nat := 4983230072969 + 3 ^ 40 * 3804089 * 2
def baseEnd_3804089 : Nat := 1953326109481472217992819

theorem tailTrace_3804089 : CollatzResearch.WordTrace tailWord_3804089 prefixEnd_3804089 1953326109481472217992819 := by
  unfold tailWord_3804089
  simp only [CollatzResearch.WordTrace]
  refine ⟨138746524315442714522111321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92497682876961809681407547 138746524315442714522111321)
  ·
    refine ⟨104059893236582035891583491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138746524315442714522111321 104059893236582035891583491)
    ·
      refine ⟨156089839854873053837375237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104059893236582035891583491 156089839854873053837375237)
      ·
        refine ⟨29266844972788697594507857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156089839854873053837375237 29266844972788697594507857)
        ·
          refine ⟨21950133729591523195880893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29266844972788697594507857 21950133729591523195880893)
          ·
            refine ⟨8231300148596821198455335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21950133729591523195880893 8231300148596821198455335)
            ·
              refine ⟨12346950222895231797683003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231300148596821198455335 12346950222895231797683003)
              ·
                refine ⟨18520425334342847696524505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12346950222895231797683003 18520425334342847696524505)
                ·
                  refine ⟨13890319000757135772393379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18520425334342847696524505 13890319000757135772393379)
                  ·
                    refine ⟨20835478501135703658590069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13890319000757135772393379 20835478501135703658590069)
                    ·
                      refine ⟨1953326109481472217992819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20835478501135703658590069 1953326109481472217992819)
                      ·
                        rfl

theorem cell23_3804089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3804089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804089 prefixEnd_3804089 := by exact prefixLift 3804089
  have htrace : WordTrace (prefixWord ++ tailWord_3804089) baseStart_3804089 baseEnd_3804089 := by
    simpa [prefixWord, tailWord_3804089, baseEnd_3804089] using wordTrace_append hprefix tailTrace_3804089
  have hstable : (prefixWord ++ tailWord_3804089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804089).length < 2 ^ (prefixWord ++ tailWord_3804089).sum := by decide
  have hdescent : baseEnd_3804089 < baseStart_3804089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804120 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 2, 2, 2]
def baseStart_3804120 : Nat := 118140960795 + 3804120 * 2 ^ 59
def prefixEnd_3804120 : Nat := 4983230072969 + 3 ^ 40 * 3804120 * 2
def baseEnd_3804120 : Nat := 1953342027381761596705177

theorem tailTrace_3804120 : CollatzResearch.WordTrace tailWord_3804120 prefixEnd_3804120 1953342027381761596705177 := by
  unfold tailWord_3804120
  simp only [CollatzResearch.WordTrace]
  refine ⟨69373827489165203408244907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92498436652220271210993209 69373827489165203408244907)
  ·
    refine ⟨104060741233747805112367361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69373827489165203408244907 104060741233747805112367361)
    ·
      refine ⟨78045555925310853834275521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104060741233747805112367361 78045555925310853834275521)
      ·
        refine ⟨58534166943983140375706641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78045555925310853834275521 58534166943983140375706641)
        ·
          refine ⟨43900625207987355281779981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58534166943983140375706641 43900625207987355281779981)
          ·
            refine ⟨16462734452995258230667493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43900625207987355281779981 16462734452995258230667493)
            ·
              refine ⟨3086762709936610918250155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16462734452995258230667493 3086762709936610918250155)
              ·
                refine ⟨4630144064904916377375233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086762709936610918250155 4630144064904916377375233)
                ·
                  refine ⟨3472608048678687283031425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4630144064904916377375233 3472608048678687283031425)
                  ·
                    refine ⟨2604456036509015462273569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3472608048678687283031425 2604456036509015462273569)
                    ·
                      refine ⟨1953342027381761596705177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604456036509015462273569 1953342027381761596705177)
                      ·
                        rfl

theorem cell23_3804120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_3804120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804120 prefixEnd_3804120 := by exact prefixLift 3804120
  have htrace : WordTrace (prefixWord ++ tailWord_3804120) baseStart_3804120 baseEnd_3804120 := by
    simpa [prefixWord, tailWord_3804120, baseEnd_3804120] using wordTrace_append hprefix tailTrace_3804120
  have hstable : (prefixWord ++ tailWord_3804120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804120).length < 2 ^ (prefixWord ++ tailWord_3804120).sum := by decide
  have hdescent : baseEnd_3804120 < baseStart_3804120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804169 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 7, 4]
def baseStart_3804169 : Nat := 118140960795 + 3804169 * 2 ^ 59
def prefixEnd_3804169 : Nat := 4983230072969 + 3 ^ 40 * 3804169 * 2
def baseEnd_3804169 : Nat := 651122395977943968330817

theorem tailTrace_3804169 : CollatzResearch.WordTrace tailWord_3804169 prefixEnd_3804169 651122395977943968330817 := by
  unfold tailWord_3804169
  simp only [CollatzResearch.WordTrace]
  refine ⟨138749442155152888185023561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92499628103435258790015707 138749442155152888185023561)
  ·
    refine ⟨104062081616364666138767671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138749442155152888185023561 104062081616364666138767671)
    ·
      refine ⟨156093122424546999208151507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104062081616364666138767671 156093122424546999208151507)
      ·
        refine ⟨234139683636820498812227261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156093122424546999208151507 234139683636820498812227261)
        ·
          refine ⟨87802381363807687054585223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234139683636820498812227261 87802381363807687054585223)
          ·
            refine ⟨131703572045711530581877835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87802381363807687054585223 131703572045711530581877835)
            ·
              refine ⟨197555358068567295872816753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131703572045711530581877835 197555358068567295872816753)
              ·
                refine ⟨148166518551425471904612565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197555358068567295872816753 148166518551425471904612565)
                ·
                  refine ⟨3472652778549034497764357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 148166518551425471904612565 3472652778549034497764357)
                  ·
                    refine ⟨651122395977943968330817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472652778549034497764357 651122395977943968330817)
                    ·
                      rfl

theorem cell23_3804169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_3804169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804169 prefixEnd_3804169 := by exact prefixLift 3804169
  have htrace : WordTrace (prefixWord ++ tailWord_3804169) baseStart_3804169 baseEnd_3804169 := by
    simpa [prefixWord, tailWord_3804169, baseEnd_3804169] using wordTrace_append hprefix tailTrace_3804169
  have hstable : (prefixWord ++ tailWord_3804169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804169).length < 2 ^ (prefixWord ++ tailWord_3804169).sum := by decide
  have hdescent : baseEnd_3804169 < baseStart_3804169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804179 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 3]
def baseStart_3804179 : Nat := 118140960795 + 3804179 * 2 ^ 59
def prefixEnd_3804179 : Nat := 4983230072969 + 3 ^ 40 * 3804179 * 2
def baseEnd_3804179 : Nat := 1953372322740376865867405

theorem tailTrace_3804179 : CollatzResearch.WordTrace tailWord_3804179 prefixEnd_3804179 1953372322740376865867405 := by
  unfold tailWord_3804179
  simp only [CollatzResearch.WordTrace]
  refine ⟨138749806885116659892887591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92499871256744439928591727 138749806885116659892887591)
  ·
    refine ⟨208124710327674989839331387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138749806885116659892887591 208124710327674989839331387)
    ·
      refine ⟨312187065491512484758997081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208124710327674989839331387 312187065491512484758997081)
      ·
        refine ⟨234140299118634363569247811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312187065491512484758997081 234140299118634363569247811)
        ·
          refine ⟨351210448677951545353871717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234140299118634363569247811 351210448677951545353871717)
          ·
            refine ⟨65851959127115914753850947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351210448677951545353871717 65851959127115914753850947)
            ·
              refine ⟨98777938690673872130776421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65851959127115914753850947 98777938690673872130776421)
              ·
                refine ⟨18520863504501351024520579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98777938690673872130776421 18520863504501351024520579)
                ·
                  refine ⟨27781295256752026536780869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18520863504501351024520579 27781295256752026536780869)
                  ·
                    refine ⟨5208992860641004975646413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27781295256752026536780869 5208992860641004975646413)
                    ·
                      refine ⟨1953372322740376865867405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5208992860641004975646413 1953372322740376865867405)
                      ·
                        rfl

theorem cell23_3804179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_3804179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804179 prefixEnd_3804179 := by exact prefixLift 3804179
  have htrace : WordTrace (prefixWord ++ tailWord_3804179) baseStart_3804179 baseEnd_3804179 := by
    simpa [prefixWord, tailWord_3804179, baseEnd_3804179] using wordTrace_append hprefix tailTrace_3804179
  have hstable : (prefixWord ++ tailWord_3804179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804179).length < 2 ^ (prefixWord ++ tailWord_3804179).sum := by decide
  have hdescent : baseEnd_3804179 < baseStart_3804179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804186 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_3804186 : Nat := 118140960795 + 3804186 * 2 ^ 59
def prefixEnd_3804186 : Nat := 4983230072969 + 3 ^ 40 * 3804186 * 2
def baseEnd_3804186 : Nat := 651125305701652779493291

theorem tailTrace_3804186 : CollatzResearch.WordTrace tailWord_3804186 prefixEnd_3804186 651125305701652779493291 := by
  unfold tailWord_3804186
  simp only [CollatzResearch.WordTrace]
  refine ⟨34687515549022825022098103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92500041464060866725594941 34687515549022825022098103)
  ·
    refine ⟨52031273323534237533147155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34687515549022825022098103 52031273323534237533147155)
    ·
      refine ⟨78046909985301356299720733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52031273323534237533147155 78046909985301356299720733)
      ·
        refine ⟨29267591244488008612395275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78046909985301356299720733 29267591244488008612395275)
        ·
          refine ⟨43901386866732012918592913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29267591244488008612395275 43901386866732012918592913)
          ·
            refine ⟨32926040150049009688944685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43901386866732012918592913 32926040150049009688944685)
            ·
              refine ⟨12347265056268378633354257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32926040150049009688944685 12347265056268378633354257)
              ·
                refine ⟨9260448792201283975015693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12347265056268378633354257 9260448792201283975015693)
                ·
                  refine ⟨3472668297075481490630885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9260448792201283975015693 3472668297075481490630885)
                  ·
                    refine ⟨651125305701652779493291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472668297075481490630885 651125305701652779493291)
                    ·
                      rfl

theorem cell23_3804186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_3804186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804186 prefixEnd_3804186 := by exact prefixLift 3804186
  have htrace : WordTrace (prefixWord ++ tailWord_3804186) baseStart_3804186 baseEnd_3804186 := by
    simpa [prefixWord, tailWord_3804186, baseEnd_3804186] using wordTrace_append hprefix tailTrace_3804186
  have hstable : (prefixWord ++ tailWord_3804186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804186).length < 2 ^ (prefixWord ++ tailWord_3804186).sum := by decide
  have hdescent : baseEnd_3804186 < baseStart_3804186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804193 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3804193 : Nat := 118140960795 + 3804193 * 2 ^ 59
def prefixEnd_3804193 : Nat := 4983230072969 + 3 ^ 40 * 3804193 * 2
def baseEnd_3804193 : Nat := 1953379511469539811092341

theorem tailTrace_3804193 : CollatzResearch.WordTrace tailWord_3804193 prefixEnd_3804193 1953379511469539811092341 := by
  unfold tailWord_3804193
  simp only [CollatzResearch.WordTrace]
  refine ⟨138750317507065940283897233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92500211671377293522598155 138750317507065940283897233)
  ·
    refine ⟨104062738130299455212922925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138750317507065940283897233 104062738130299455212922925)
    ·
      refine ⟨39023526798862295704846097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104062738130299455212922925 39023526798862295704846097)
      ·
        refine ⟨29267645099146721778634573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39023526798862295704846097 29267645099146721778634573)
        ·
          refine ⟨10975366912180020666987965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29267645099146721778634573 10975366912180020666987965)
          ·
            refine ⟨4115762592067507750120487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10975366912180020666987965 4115762592067507750120487)
            ·
              refine ⟨6173643888101261625180731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115762592067507750120487 6173643888101261625180731)
              ·
                refine ⟨9260465832151892437771097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6173643888101261625180731 9260465832151892437771097)
                ·
                  refine ⟨6945349374113919328328323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9260465832151892437771097 6945349374113919328328323)
                  ·
                    refine ⟨10418024061170878992492485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6945349374113919328328323 10418024061170878992492485)
                    ·
                      refine ⟨1953379511469539811092341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10418024061170878992492485 1953379511469539811092341)
                      ·
                        rfl

theorem cell23_3804193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3804193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804193 prefixEnd_3804193 := by exact prefixLift 3804193
  have htrace : WordTrace (prefixWord ++ tailWord_3804193) baseStart_3804193 baseEnd_3804193 := by
    simpa [prefixWord, tailWord_3804193, baseEnd_3804193] using wordTrace_append hprefix tailTrace_3804193
  have hstable : (prefixWord ++ tailWord_3804193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804193).length < 2 ^ (prefixWord ++ tailWord_3804193).sum := by decide
  have hdescent : baseEnd_3804193 < baseStart_3804193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804203 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 1, 4]
def baseStart_3804203 : Nat := 118140960795 + 3804203 * 2 ^ 59
def prefixEnd_3804203 : Nat := 4983230072969 + 3 ^ 40 * 3804203 * 2
def baseEnd_3804203 : Nat := 651128215425361590655765

theorem tailTrace_3804203 : CollatzResearch.WordTrace tailWord_3804203 prefixEnd_3804203 651128215425361590655765 := by
  unfold tailWord_3804203
  simp only [CollatzResearch.WordTrace]
  refine ⟨138750682237029711991761263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92500454824686474661174175 138750682237029711991761263)
  ·
    refine ⟨208126023355544567987641895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138750682237029711991761263 208126023355544567987641895)
    ·
      refine ⟨312189035033316851981462843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208126023355544567987641895 312189035033316851981462843)
      ·
        refine ⟨468283552549975277972194265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312189035033316851981462843 468283552549975277972194265)
        ·
          refine ⟨351212664412481458479145699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468283552549975277972194265 351212664412481458479145699)
          ·
            refine ⟨526818996618722187718718549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351212664412481458479145699 526818996618722187718718549)
            ·
              refine ⟨6173660116625650637328733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 526818996618722187718718549 6173660116625650637328733)
              ·
                refine ⟨2315122543734618988998275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173660116625650637328733 2315122543734618988998275)
                ·
                  refine ⟨3472683815601928483497413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315122543734618988998275 3472683815601928483497413)
                  ·
                    refine ⟨651128215425361590655765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472683815601928483497413 651128215425361590655765)
                    ·
                      rfl

theorem cell23_3804203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 4].length) (baseStart_3804203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804203 prefixEnd_3804203 := by exact prefixLift 3804203
  have htrace : WordTrace (prefixWord ++ tailWord_3804203) baseStart_3804203 baseEnd_3804203 := by
    simpa [prefixWord, tailWord_3804203, baseEnd_3804203] using wordTrace_append hprefix tailTrace_3804203
  have hstable : (prefixWord ++ tailWord_3804203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804203).length < 2 ^ (prefixWord ++ tailWord_3804203).sum := by decide
  have hdescent : baseEnd_3804203 < baseStart_3804203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804216 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 6]
def baseStart_3804216 : Nat := 118140960795 + 3804216 * 2 ^ 59
def prefixEnd_3804216 : Nat := 4983230072969 + 3 ^ 40 * 3804216 * 2
def baseEnd_3804216 : Nat := 217043480169399246789415

theorem tailTrace_3804216 : CollatzResearch.WordTrace tailWord_3804216 prefixEnd_3804216 217043480169399246789415 := by
  unfold tailWord_3804216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69375578192991307605992251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92500770923988410141323001 69375578192991307605992251)
  ·
    refine ⟨104063367289486961408988377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69375578192991307605992251 104063367289486961408988377)
    ·
      refine ⟨78047525467115221056741283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104063367289486961408988377 78047525467115221056741283)
      ·
        refine ⟨117071288200672831585111925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78047525467115221056741283 117071288200672831585111925)
        ·
          refine ⟨10975433268813077961104243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117071288200672831585111925 10975433268813077961104243)
          ·
            refine ⟨16463149903219616941656365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10975433268813077961104243 16463149903219616941656365)
            ·
              refine ⟨6173681213707356353121137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16463149903219616941656365 6173681213707356353121137)
              ·
                refine ⟨4630260910280517264840853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6173681213707356353121137 4630260910280517264840853)
                ·
                  refine ⟨217043480169399246789415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4630260910280517264840853 217043480169399246789415)
                  ·
                    rfl

theorem cell23_3804216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 6].length) (baseStart_3804216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804216 prefixEnd_3804216 := by exact prefixLift 3804216
  have htrace : WordTrace (prefixWord ++ tailWord_3804216) baseStart_3804216 baseEnd_3804216 := by
    simpa [prefixWord, tailWord_3804216, baseEnd_3804216] using wordTrace_append hprefix tailTrace_3804216
  have hstable : (prefixWord ++ tailWord_3804216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804216).length < 2 ^ (prefixWord ++ tailWord_3804216).sum := by decide
  have hdescent : baseEnd_3804216 < baseStart_3804216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804229 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_3804229 : Nat := 118140960795 + 3804229 * 2 ^ 59
def prefixEnd_3804229 : Nat := 4983230072969 + 3 ^ 40 * 3804229 * 2
def baseEnd_3804229 : Nat := 651132665591033890080725

theorem tailTrace_3804229 : CollatzResearch.WordTrace tailWord_3804229 prefixEnd_3804229 651132665591033890080725 := by
  unfold tailWord_3804229
  simp only [CollatzResearch.WordTrace]
  refine ⟨138751630534935518432207741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92501087023290345621471827 138751630534935518432207741)
  ·
    refine ⟨52031861450600819412077903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138751630534935518432207741 52031861450600819412077903)
    ·
      refine ⟨78047792175901229118116855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52031861450600819412077903 78047792175901229118116855)
      ·
        refine ⟨117071688263851843677175283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78047792175901229118116855 117071688263851843677175283)
        ·
          refine ⟨175607532395777765515762925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117071688263851843677175283 175607532395777765515762925)
          ·
            refine ⟨65852824648416662068411097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175607532395777765515762925 65852824648416662068411097)
            ·
              refine ⟨49389618486312496551308323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65852824648416662068411097 49389618486312496551308323)
              ·
                refine ⟨74084427729468744826962485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49389618486312496551308323 74084427729468744826962485)
                ·
                  refine ⟨6945415099637694827527733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74084427729468744826962485 6945415099637694827527733)
                  ·
                    refine ⟨651132665591033890080725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6945415099637694827527733 651132665591033890080725)
                    ·
                      rfl

theorem cell23_3804229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_3804229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804229 prefixEnd_3804229 := by exact prefixLift 3804229
  have htrace : WordTrace (prefixWord ++ tailWord_3804229) baseStart_3804229 baseEnd_3804229 := by
    simpa [prefixWord, tailWord_3804229, baseEnd_3804229] using wordTrace_append hprefix tailTrace_3804229
  have hstable : (prefixWord ++ tailWord_3804229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804229).length < 2 ^ (prefixWord ++ tailWord_3804229).sum := by decide
  have hdescent : baseEnd_3804229 < baseStart_3804229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804254 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3804254 : Nat := 118140960795 + 3804254 * 2 ^ 59
def prefixEnd_3804254 : Nat := 4983230072969 + 3 ^ 40 * 3804254 * 2
def baseEnd_3804254 : Nat := 651136944596488024143187

theorem tailTrace_3804254 : CollatzResearch.WordTrace tailWord_3804254 prefixEnd_3804254 651136944596488024143187 := by
  unfold tailWord_3804254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344067794980618462733477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92501694906563298467911877 17344067794980618462733477)
  ·
    refine ⟨3252012711558865961762527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17344067794980618462733477 3252012711558865961762527)
    ·
      refine ⟨4878019067338298942643791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252012711558865961762527 4878019067338298942643791)
      ·
        refine ⟨7317028601007448413965687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878019067338298942643791 7317028601007448413965687)
        ·
          refine ⟨10975542901511172620948531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317028601007448413965687 10975542901511172620948531)
          ·
            refine ⟨16463314352266758931422797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10975542901511172620948531 16463314352266758931422797)
            ·
              refine ⟨6173742882100034599283549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16463314352266758931422797 6173742882100034599283549)
              ·
                refine ⟨2315153580787512974731331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173742882100034599283549 2315153580787512974731331)
                ·
                  refine ⟨3472730371181269462096997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315153580787512974731331 3472730371181269462096997)
                  ·
                    refine ⟨651136944596488024143187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472730371181269462096997 651136944596488024143187)
                    ·
                      rfl

theorem cell23_3804254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3804254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804254 prefixEnd_3804254 := by exact prefixLift 3804254
  have htrace : WordTrace (prefixWord ++ tailWord_3804254) baseStart_3804254 baseEnd_3804254 := by
    simpa [prefixWord, tailWord_3804254, baseEnd_3804254] using wordTrace_append hprefix tailTrace_3804254
  have hstable : (prefixWord ++ tailWord_3804254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804254).length < 2 ^ (prefixWord ++ tailWord_3804254).sum := by decide
  have hdescent : baseEnd_3804254 < baseStart_3804254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804259 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 3, 6]
def baseStart_3804259 : Nat := 118140960795 + 3804259 * 2 ^ 59
def prefixEnd_3804259 : Nat := 4983230072969 + 3 ^ 40 * 3804259 * 2
def baseEnd_3804259 : Nat := 651137800397578850955679

theorem tailTrace_3804259 : CollatzResearch.WordTrace tailWord_3804259 prefixEnd_3804259 651137800397578850955679 := by
  unfold tailWord_3804259
  simp only [CollatzResearch.WordTrace]
  refine ⟨138752724724826833555799831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92501816483217889037199887 138752724724826833555799831)
  ·
    refine ⟨208129087087240250333699747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138752724724826833555799831 208129087087240250333699747)
    ·
      refine ⟨312193630630860375500549621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208129087087240250333699747 312193630630860375500549621)
      ·
        refine ⟨29268152871643160203176527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312193630630860375500549621 29268152871643160203176527)
        ·
          refine ⟨43902229307464740304764791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29268152871643160203176527 43902229307464740304764791)
          ·
            refine ⟨65853343961197110457147187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43902229307464740304764791 65853343961197110457147187)
            ·
              refine ⟨98780015941795665685720781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65853343961197110457147187 98780015941795665685720781)
              ·
                refine ⟨37042505978173374632145293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98780015941795665685720781 37042505978173374632145293)
                ·
                  refine ⟨13890939741815015487054485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37042505978173374632145293 13890939741815015487054485)
                  ·
                    refine ⟨651137800397578850955679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13890939741815015487054485 651137800397578850955679)
                    ·
                      rfl

theorem cell23_3804259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 6].length) (baseStart_3804259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804259 prefixEnd_3804259 := by exact prefixLift 3804259
  have htrace : WordTrace (prefixWord ++ tailWord_3804259) baseStart_3804259 baseEnd_3804259 := by
    simpa [prefixWord, tailWord_3804259, baseEnd_3804259] using wordTrace_append hprefix tailTrace_3804259
  have hstable : (prefixWord ++ tailWord_3804259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804259).length < 2 ^ (prefixWord ++ tailWord_3804259).sum := by decide
  have hdescent : baseEnd_3804259 < baseStart_3804259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804270 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_3804270 : Nat := 118140960795 + 3804270 * 2 ^ 59
def prefixEnd_3804270 : Nat := 4983230072969 + 3 ^ 40 * 3804270 * 2
def baseEnd_3804270 : Nat := 1953419049479936009829487

theorem tailTrace_3804270 : CollatzResearch.WordTrace tailWord_3804270 prefixEnd_3804270 1953419049479936009829487 := by
  unfold tailWord_3804270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344140740973372804306283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92502083951857988289633509 17344140740973372804306283)
  ·
    refine ⟨26016211111460059206459425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17344140740973372804306283 26016211111460059206459425)
    ·
      refine ⟨19512158333595044404844569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26016211111460059206459425 19512158333595044404844569)
      ·
        refine ⟨14634118750196283303633427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19512158333595044404844569 14634118750196283303633427)
        ·
          refine ⟨21951178125294424955450141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14634118750196283303633427 21951178125294424955450141)
          ·
            refine ⟨8231691796985409358293803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21951178125294424955450141 8231691796985409358293803)
            ·
              refine ⟨12347537695478114037440705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231691796985409358293803 12347537695478114037440705)
              ·
                refine ⟨9260653271608585528080529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12347537695478114037440705 9260653271608585528080529)
                ·
                  refine ⟨6945489953706439146060397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9260653271608585528080529 6945489953706439146060397)
                  ·
                    refine ⟨2604558732639914679772649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6945489953706439146060397 2604558732639914679772649)
                    ·
                      refine ⟨1953419049479936009829487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604558732639914679772649 1953419049479936009829487)
                      ·
                        rfl

theorem cell23_3804270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_3804270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804270 prefixEnd_3804270 := by exact prefixLift 3804270
  have htrace : WordTrace (prefixWord ++ tailWord_3804270) baseStart_3804270 baseEnd_3804270 := by
    simpa [prefixWord, tailWord_3804270, baseEnd_3804270] using wordTrace_append hprefix tailTrace_3804270
  have hstable : (prefixWord ++ tailWord_3804270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804270).length < 2 ^ (prefixWord ++ tailWord_3804270).sum := by decide
  have hdescent : baseEnd_3804270 < baseStart_3804270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804279 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3804279 : Nat := 118140960795 + 3804279 * 2 ^ 59
def prefixEnd_3804279 : Nat := 4983230072969 + 3 ^ 40 * 3804279 * 2
def baseEnd_3804279 : Nat := 1953423670805826474616945

theorem tailTrace_3804279 : CollatzResearch.WordTrace tailWord_3804279 prefixEnd_3804279 1953423670805826474616945 := by
  unfold tailWord_3804279
  simp only [CollatzResearch.WordTrace]
  refine ⟨138753454184754376971527891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92502302789836251314351927 138753454184754376971527891)
  ·
    refine ⟨208130181277131565457291837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138753454184754376971527891 208130181277131565457291837)
    ·
      refine ⟨78048817978924337046484439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208130181277131565457291837 78048817978924337046484439)
      ·
        refine ⟨117073226968386505569726659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78048817978924337046484439 117073226968386505569726659)
        ·
          refine ⟨175609840452579758354589989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117073226968386505569726659 175609840452579758354589989)
          ·
            refine ⟨32926845084858704691485623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175609840452579758354589989 32926845084858704691485623)
            ·
              refine ⟨49390267627288057037228435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32926845084858704691485623 49390267627288057037228435)
              ·
                refine ⟨74085401440932085555842653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49390267627288057037228435 74085401440932085555842653)
                ·
                  refine ⟨27782025540349532083440995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74085401440932085555842653 27782025540349532083440995)
                  ·
                    refine ⟨41673038310524298125161493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27782025540349532083440995 41673038310524298125161493)
                    ·
                      refine ⟨1953423670805826474616945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41673038310524298125161493 1953423670805826474616945)
                      ·
                        rfl

theorem cell23_3804279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3804279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804279 prefixEnd_3804279 := by exact prefixLift 3804279
  have htrace : WordTrace (prefixWord ++ tailWord_3804279) baseStart_3804279 baseEnd_3804279 := by
    simpa [prefixWord, tailWord_3804279, baseEnd_3804279] using wordTrace_append hprefix tailTrace_3804279
  have hstable : (prefixWord ++ tailWord_3804279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804279).length < 2 ^ (prefixWord ++ tailWord_3804279).sum := by decide
  have hdescent : baseEnd_3804279 < baseStart_3804279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804306 : List Nat := [3, 2, 3, 1, 1, 2, 2, 9]
def baseStart_3804306 : Nat := 118140960795 + 3804306 * 2 ^ 59
def prefixEnd_3804306 : Nat := 4983230072969 + 3 ^ 40 * 3804306 * 2
def baseEnd_3804306 : Nat := 72349538325314735888123

theorem tailTrace_3804306 : CollatzResearch.WordTrace tailWord_3804306 prefixEnd_3804306 72349538325314735888123 := by
  unfold tailWord_3804306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34688609738914140145690193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92502959303771040388507181 34688609738914140145690193)
  ·
    refine ⟨26016457304185605109267645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34688609738914140145690193 26016457304185605109267645)
    ·
      refine ⟨9756171489069601915975367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26016457304185605109267645 9756171489069601915975367)
      ·
        refine ⟨14634257233604402873963051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9756171489069601915975367 14634257233604402873963051)
        ·
          refine ⟨21951385850406604310944577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14634257233604402873963051 21951385850406604310944577)
          ·
            refine ⟨16463539387804953233208433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21951385850406604310944577 16463539387804953233208433)
            ·
              refine ⟨12347654540853714924906325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16463539387804953233208433 12347654540853714924906325)
              ·
                refine ⟨72349538325314735888123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12347654540853714924906325 72349538325314735888123)
                ·
                  rfl

theorem cell23_3804306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_3804306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804306 prefixEnd_3804306 := by exact prefixLift 3804306
  have htrace : WordTrace (prefixWord ++ tailWord_3804306) baseStart_3804306 baseEnd_3804306 := by
    simpa [prefixWord, tailWord_3804306, baseEnd_3804306] using wordTrace_append hprefix tailTrace_3804306
  have hstable : (prefixWord ++ tailWord_3804306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804306).length < 2 ^ (prefixWord ++ tailWord_3804306).sum := by decide
  have hdescent : baseEnd_3804306 < baseStart_3804306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804317 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_3804317 : Nat := 118140960795 + 3804317 * 2 ^ 59
def prefixEnd_3804317 : Nat := 4983230072969 + 3 ^ 40 * 3804317 * 2
def baseEnd_3804317 : Nat := 1953443183070697325941771

theorem tailTrace_3804317 : CollatzResearch.WordTrace tailWord_3804317 prefixEnd_3804317 1953443183070697325941771 := by
  unfold tailWord_3804317
  simp only [CollatzResearch.WordTrace]
  refine ⟨138754840158616709461411205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92503226772411139640940803 138754840158616709461411205)
  ·
    refine ⟨26016532529740633024014601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138754840158616709461411205 26016532529740633024014601)
    ·
      refine ⟨19512399397305474768010951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26016532529740633024014601 19512399397305474768010951)
      ·
        refine ⟨29268599095958212152016427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19512399397305474768010951 29268599095958212152016427)
        ·
          refine ⟨43902898643937318228024641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29268599095958212152016427 43902898643937318228024641)
          ·
            refine ⟨32927173982952988671018481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43902898643937318228024641 32927173982952988671018481)
            ·
              refine ⟨24695380487214741503263861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32927173982952988671018481 24695380487214741503263861)
              ·
                refine ⟨2315191920676382015930987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24695380487214741503263861 2315191920676382015930987)
                ·
                  refine ⟨3472787881014573023896481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315191920676382015930987 3472787881014573023896481)
                  ·
                    refine ⟨2604590910760929767922361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3472787881014573023896481 2604590910760929767922361)
                    ·
                      refine ⟨1953443183070697325941771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604590910760929767922361 1953443183070697325941771)
                      ·
                        rfl

theorem cell23_3804317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_3804317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804317 prefixEnd_3804317 := by exact prefixLift 3804317
  have htrace : WordTrace (prefixWord ++ tailWord_3804317) baseStart_3804317 baseEnd_3804317 := by
    simpa [prefixWord, tailWord_3804317, baseEnd_3804317] using wordTrace_append hprefix tailTrace_3804317
  have hstable : (prefixWord ++ tailWord_3804317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804317).length < 2 ^ (prefixWord ++ tailWord_3804317).sum := by decide
  have hdescent : baseEnd_3804317 < baseStart_3804317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804320 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 1, 2, 3]
def baseStart_3804320 : Nat := 118140960795 + 3804320 * 2 ^ 59
def prefixEnd_3804320 : Nat := 4983230072969 + 3 ^ 40 * 3804320 * 2
def baseEnd_3804320 : Nat := 1953444723512660814204257

theorem tailTrace_3804320 : CollatzResearch.WordTrace tailWord_3804320 prefixEnd_3804320 1953444723512660814204257 := by
  unfold tailWord_3804320
  simp only [CollatzResearch.WordTrace]
  refine ⟨69377474788802920486885207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92503299718403893982513609 69377474788802920486885207)
  ·
    refine ⟨104066212183204380730327811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69377474788802920486885207 104066212183204380730327811)
    ·
      refine ⟨156099318274806571095491717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104066212183204380730327811 156099318274806571095491717)
      ·
        refine ⟨29268622176526232080404697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156099318274806571095491717 29268622176526232080404697)
        ·
          refine ⟨21951466632394674060303523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29268622176526232080404697 21951466632394674060303523)
          ·
            refine ⟨32927199948592011090455285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21951466632394674060303523 32927199948592011090455285)
            ·
              refine ⟨3086924995180501039730183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32927199948592011090455285 3086924995180501039730183)
              ·
                refine ⟨4630387492770751559595275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086924995180501039730183 4630387492770751559595275)
                ·
                  refine ⟨6945581239156127339392913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630387492770751559595275 6945581239156127339392913)
                  ·
                    refine ⟨5209185929367095504544685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945581239156127339392913 5209185929367095504544685)
                    ·
                      refine ⟨1953444723512660814204257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5209185929367095504544685 1953444723512660814204257)
                      ·
                        rfl

theorem cell23_3804320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_3804320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804320 prefixEnd_3804320 := by exact prefixLift 3804320
  have htrace : WordTrace (prefixWord ++ tailWord_3804320) baseStart_3804320 baseEnd_3804320 := by
    simpa [prefixWord, tailWord_3804320, baseEnd_3804320] using wordTrace_append hprefix tailTrace_3804320
  have hstable : (prefixWord ++ tailWord_3804320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804320).length < 2 ^ (prefixWord ++ tailWord_3804320).sum := by decide
  have hdescent : baseEnd_3804320 < baseStart_3804320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804343 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 5, 3, 2]
def baseStart_3804343 : Nat := 118140960795 + 3804343 * 2 ^ 59
def prefixEnd_3804343 : Nat := 4983230072969 + 3 ^ 40 * 3804343 * 2
def baseEnd_3804343 : Nat := 1953456533567714224216651

theorem tailTrace_3804343 : CollatzResearch.WordTrace tailWord_3804343 prefixEnd_3804343 1953456533567714224216651 := by
  unfold tailWord_3804343
  simp only [CollatzResearch.WordTrace]
  refine ⟨138755788456522515901857683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92503858971015010601238455 138755788456522515901857683)
  ·
    refine ⟨208133682684783773852786525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138755788456522515901857683 208133682684783773852786525)
    ·
      refine ⟨78050131006793915194794947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208133682684783773852786525 78050131006793915194794947)
      ·
        refine ⟨117075196510190872792192421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78050131006793915194794947 117075196510190872792192421)
        ·
          refine ⟨21951599345660788648536079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117075196510190872792192421 21951599345660788648536079)
          ·
            refine ⟨32927399018491182972804119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21951599345660788648536079 32927399018491182972804119)
            ·
              refine ⟨49391098527736774459206179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32927399018491182972804119 49391098527736774459206179)
              ·
                refine ⟨74086647791605161688809269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49391098527736774459206179 74086647791605161688809269)
                ·
                  refine ⟨6945623230462983908325869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74086647791605161688809269 6945623230462983908325869)
                  ·
                    refine ⟨2604608711423618965622201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6945623230462983908325869 2604608711423618965622201)
                    ·
                      refine ⟨1953456533567714224216651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604608711423618965622201 1953456533567714224216651)
                      ·
                        rfl

theorem cell23_3804343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_3804343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804343 prefixEnd_3804343 := by exact prefixLift 3804343
  have htrace : WordTrace (prefixWord ++ tailWord_3804343) baseStart_3804343 baseEnd_3804343 := by
    simpa [prefixWord, tailWord_3804343, baseEnd_3804343] using wordTrace_append hprefix tailTrace_3804343
  have hstable : (prefixWord ++ tailWord_3804343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804343).length < 2 ^ (prefixWord ++ tailWord_3804343).sum := by decide
  have hdescent : baseEnd_3804343 < baseStart_3804343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804350 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3804350 : Nat := 118140960795 + 3804350 * 2 ^ 59
def prefixEnd_3804350 : Nat := 4983230072969 + 3 ^ 40 * 3804350 * 2
def baseEnd_3804350 : Nat := 1953460127932295696829119

theorem tailTrace_3804350 : CollatzResearch.WordTrace tailWord_3804350 prefixEnd_3804350 1953460127932295696829119 := by
  unfold tailWord_3804350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344505470937144512170313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92504029178331437398241669 17344505470937144512170313)
  ·
    refine ⟨13008379103202858384127735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17344505470937144512170313 13008379103202858384127735)
    ·
      refine ⟨19512568654804287576191603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13008379103202858384127735 19512568654804287576191603)
      ·
        refine ⟨29268852982206431364287405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19512568654804287576191603 29268852982206431364287405)
        ·
          refine ⟨10975819868327411761607777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29268852982206431364287405 10975819868327411761607777)
          ·
            refine ⟨8231864901245558821205833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10975819868327411761607777 8231864901245558821205833)
            ·
              refine ⟨6173898675934169115904375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8231864901245558821205833 6173898675934169115904375)
              ·
                refine ⟨9260848013901253673856563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6173898675934169115904375 9260848013901253673856563)
                ·
                  refine ⟨13891272020851880510784845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9260848013901253673856563 13891272020851880510784845)
                  ·
                    refine ⟨5209227007819455191544317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13891272020851880510784845 5209227007819455191544317)
                    ·
                      refine ⟨1953460127932295696829119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5209227007819455191544317 1953460127932295696829119)
                      ·
                        rfl

theorem cell23_3804350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3804350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804350 prefixEnd_3804350 := by exact prefixLift 3804350
  have htrace : WordTrace (prefixWord ++ tailWord_3804350) baseStart_3804350 baseEnd_3804350 := by
    simpa [prefixWord, tailWord_3804350, baseEnd_3804350] using wordTrace_append hprefix tailTrace_3804350
  have hstable : (prefixWord ++ tailWord_3804350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804350).length < 2 ^ (prefixWord ++ tailWord_3804350).sum := by decide
  have hdescent : baseEnd_3804350 < baseStart_3804350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804396 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 7]
def baseStart_3804396 : Nat := 118140960795 + 3804396 * 2 ^ 59
def prefixEnd_3804396 : Nat := 4983230072969 + 3 ^ 40 * 3804396 * 2
def baseEnd_3804396 : Nat := 217053749782489168539323

theorem tailTrace_3804396 : CollatzResearch.WordTrace tailWord_3804396 prefixEnd_3804396 217053749782489168539323 := by
  unfold tailWord_3804396
  simp only [CollatzResearch.WordTrace]
  refine ⟨69378860762665252976768521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92505147683553670635691361 69378860762665252976768521)
  ·
    refine ⟨52034145571998939732576391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69378860762665252976768521 52034145571998939732576391)
    ·
      refine ⟨78051218357998409598864587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52034145571998939732576391 78051218357998409598864587)
      ·
        refine ⟨117076827536997614398296881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78051218357998409598864587 117076827536997614398296881)
        ·
          refine ⟨87807620652748210798722661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117076827536997614398296881 87807620652748210798722661)
          ·
            refine ⟨16463928872390289524760499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87807620652748210798722661 16463928872390289524760499)
            ·
              refine ⟨24695893308585434287140749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16463928872390289524760499 24695893308585434287140749)
              ·
                refine ⟨9260959990719537857677781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24695893308585434287140749 9260959990719537857677781)
                ·
                  refine ⟨217053749782489168539323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9260959990719537857677781 217053749782489168539323)
                  ·
                    rfl

theorem cell23_3804396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_3804396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804396 prefixEnd_3804396 := by exact prefixLift 3804396
  have htrace : WordTrace (prefixWord ++ tailWord_3804396) baseStart_3804396 baseEnd_3804396 := by
    simpa [prefixWord, tailWord_3804396, baseEnd_3804396] using wordTrace_append hprefix tailTrace_3804396
  have hstable : (prefixWord ++ tailWord_3804396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804396).length < 2 ^ (prefixWord ++ tailWord_3804396).sum := by decide
  have hdescent : baseEnd_3804396 < baseStart_3804396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804430 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_3804430 : Nat := 118140960795 + 3804430 * 2 ^ 59
def prefixEnd_3804430 : Nat := 4983230072969 + 3 ^ 40 * 3804430 * 2
def baseEnd_3804430 : Nat := 217055689598295042647639

theorem tailTrace_3804430 : CollatzResearch.WordTrace tailWord_3804430 prefixEnd_3804430 217055689598295042647639 := by
  unfold tailWord_3804430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344870200900916220034343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92505974404804886506849829 17344870200900916220034343)
  ·
    refine ⟨26017305301351374330051515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17344870200900916220034343 26017305301351374330051515)
    ·
      refine ⟨39025957952027061495077273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26017305301351374330051515 39025957952027061495077273)
      ·
        refine ⟨29269468464020296121307955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39025957952027061495077273 29269468464020296121307955)
        ·
          refine ⟨43904202696030444181961933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29269468464020296121307955 43904202696030444181961933)
          ·
            refine ⟨16464076011011416568235725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43904202696030444181961933 16464076011011416568235725)
            ·
              refine ⟨6174028504129281213088397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16464076011011416568235725 6174028504129281213088397)
              ·
                refine ⟨2315260689048480454908149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6174028504129281213088397 2315260689048480454908149)
                ·
                  refine ⟨217055689598295042647639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2315260689048480454908149 217055689598295042647639)
                  ·
                    rfl

theorem cell23_3804430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_3804430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804430 prefixEnd_3804430 := by exact prefixLift 3804430
  have htrace : WordTrace (prefixWord ++ tailWord_3804430) baseStart_3804430 baseEnd_3804430 := by
    simpa [prefixWord, tailWord_3804430, baseEnd_3804430] using wordTrace_append hprefix tailTrace_3804430
  have hstable : (prefixWord ++ tailWord_3804430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804430).length < 2 ^ (prefixWord ++ tailWord_3804430).sum := by decide
  have hdescent : baseEnd_3804430 < baseStart_3804430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804447 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 5]
def baseStart_3804447 : Nat := 118140960795 + 3804447 * 2 ^ 59
def prefixEnd_3804447 : Nat := 4983230072969 + 3 ^ 40 * 3804447 * 2
def baseEnd_3804447 : Nat := 217056659506197979701797

theorem tailTrace_3804447 : CollatzResearch.WordTrace tailWord_3804447 prefixEnd_3804447 217056659506197979701797 := by
  unfold tailWord_3804447
  simp only [CollatzResearch.WordTrace]
  refine ⟨138759581648145741663643595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92506387765430494442429063 138759581648145741663643595)
  ·
    refine ⟨208139372472218612495465393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138759581648145741663643595 208139372472218612495465393)
    ·
      refine ⟨156104529354163959371599045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208139372472218612495465393 156104529354163959371599045)
      ·
        refine ⟨29269599253905742382174821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156104529354163959371599045 29269599253905742382174821)
        ·
          refine ⟨5488049860107326696657779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29269599253905742382174821 5488049860107326696657779)
          ·
            refine ⟨8232074790160990044986669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488049860107326696657779 8232074790160990044986669)
            ·
              refine ⟨3087028046310371266870001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8232074790160990044986669 3087028046310371266870001)
              ·
                refine ⟨2315271034732778450152501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087028046310371266870001 2315271034732778450152501)
                ·
                  refine ⟨217056659506197979701797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2315271034732778450152501 217056659506197979701797)
                  ·
                    rfl

theorem cell23_3804447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 5].length) (baseStart_3804447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804447 prefixEnd_3804447 := by exact prefixLift 3804447
  have htrace : WordTrace (prefixWord ++ tailWord_3804447) baseStart_3804447 baseEnd_3804447 := by
    simpa [prefixWord, tailWord_3804447, baseEnd_3804447] using wordTrace_append hprefix tailTrace_3804447
  have hstable : (prefixWord ++ tailWord_3804447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804447).length < 2 ^ (prefixWord ++ tailWord_3804447).sum := by decide
  have hdescent : baseEnd_3804447 < baseStart_3804447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804453 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3804453 : Nat := 118140960795 + 3804453 * 2 ^ 59
def prefixEnd_3804453 : Nat := 4983230072969 + 3 ^ 40 * 3804453 * 2
def baseEnd_3804453 : Nat := 1953513016439708793841145

theorem tailTrace_3804453 : CollatzResearch.WordTrace tailWord_3804453 prefixEnd_3804453 1953513016439708793841145 := by
  unfold tailWord_3804453
  simp only [CollatzResearch.WordTrace]
  refine ⟨138759800486124004688362013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92506533657416003125574675 138759800486124004688362013)
  ·
    refine ⟨52034925182296501758135755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138759800486124004688362013 52034925182296501758135755)
    ·
      refine ⟨78052387773444752637203633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52034925182296501758135755 78052387773444752637203633)
      ·
        refine ⟨58539290830083564477902725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78052387773444752637203633 58539290830083564477902725)
        ·
          refine ⟨10976117030640668339606761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58539290830083564477902725 10976117030640668339606761)
          ·
            refine ⟨8232087772980501254705071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10976117030640668339606761 8232087772980501254705071)
            ·
              refine ⟨12348131659470751882057607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232087772980501254705071 12348131659470751882057607)
              ·
                refine ⟨18522197489206127823086411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12348131659470751882057607 18522197489206127823086411)
                ·
                  refine ⟨27783296233809191734629617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18522197489206127823086411 27783296233809191734629617)
                  ·
                    refine ⟨20837472175356893800972213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27783296233809191734629617 20837472175356893800972213)
                    ·
                      refine ⟨1953513016439708793841145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20837472175356893800972213 1953513016439708793841145)
                      ·
                        rfl

theorem cell23_3804453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3804453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804453 prefixEnd_3804453 := by exact prefixLift 3804453
  have htrace : WordTrace (prefixWord ++ tailWord_3804453) baseStart_3804453 baseEnd_3804453 := by
    simpa [prefixWord, tailWord_3804453, baseEnd_3804453] using wordTrace_append hprefix tailTrace_3804453
  have hstable : (prefixWord ++ tailWord_3804453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804453).length < 2 ^ (prefixWord ++ tailWord_3804453).sum := by decide
  have hdescent : baseEnd_3804453 < baseStart_3804453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804463 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 6, 2]
def baseStart_3804463 : Nat := 118140960795 + 3804463 * 2 ^ 59
def prefixEnd_3804463 : Nat := 4983230072969 + 3 ^ 40 * 3804463 * 2
def baseEnd_3804463 : Nat := 1953518151246253754716099

theorem tailTrace_3804463 : CollatzResearch.WordTrace tailWord_3804463 prefixEnd_3804463 1953518151246253754716099 := by
  unfold tailWord_3804463
  simp only [CollatzResearch.WordTrace]
  refine ⟨138760165216087776396226043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92506776810725184264150695 138760165216087776396226043)
  ·
    refine ⟨208140247824131664594339065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138760165216087776396226043 208140247824131664594339065)
    ·
      refine ⟨156105185868098748445754299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208140247824131664594339065 156105185868098748445754299)
      ·
        refine ⟨234157778802148122668631449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156105185868098748445754299 234157778802148122668631449)
        ·
          refine ⟨175618334101611092001473587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234157778802148122668631449 175618334101611092001473587)
          ·
            refine ⟨263427501152416638002210381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175618334101611092001473587 263427501152416638002210381)
            ·
              refine ⟨98785312932156239250828893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263427501152416638002210381 98785312932156239250828893)
              ·
                refine ⟨37044492349558589719060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98785312932156239250828893 37044492349558589719060835)
                ·
                  refine ⟨55566738524337884578591253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37044492349558589719060835 55566738524337884578591253)
                  ·
                    refine ⟨2604690868328338339621465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55566738524337884578591253 2604690868328338339621465)
                    ·
                      refine ⟨1953518151246253754716099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604690868328338339621465 1953518151246253754716099)
                      ·
                        rfl

theorem cell23_3804463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6, 2].length) (baseStart_3804463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804463 prefixEnd_3804463 := by exact prefixLift 3804463
  have htrace : WordTrace (prefixWord ++ tailWord_3804463) baseStart_3804463 baseEnd_3804463 := by
    simpa [prefixWord, tailWord_3804463, baseEnd_3804463] using wordTrace_append hprefix tailTrace_3804463
  have hstable : (prefixWord ++ tailWord_3804463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804463).length < 2 ^ (prefixWord ++ tailWord_3804463).sum := by decide
  have hdescent : baseEnd_3804463 < baseStart_3804463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804477 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3804477 : Nat := 118140960795 + 3804477 * 2 ^ 59
def prefixEnd_3804477 : Nat := 4983230072969 + 3 ^ 40 * 3804477 * 2
def baseEnd_3804477 : Nat := 651175113325138899980345

theorem tailTrace_3804477 : CollatzResearch.WordTrace tailWord_3804477 prefixEnd_3804477 651175113325138899980345 := by
  unfold tailWord_3804477
  simp only [CollatzResearch.WordTrace]
  refine ⟨138760675838037056787235685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92507117225358037858157123 138760675838037056787235685)
  ·
    refine ⟨26017626719631948147606691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138760675838037056787235685 26017626719631948147606691)
    ·
      refine ⟨39026440079447922221410037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26017626719631948147606691 39026440079447922221410037)
      ·
        refine ⟨3658728757448242708257191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39026440079447922221410037 3658728757448242708257191)
        ·
          refine ⟨5488093136172364062385787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658728757448242708257191 5488093136172364062385787)
          ·
            refine ⟨8232139704258546093578681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488093136172364062385787 8232139704258546093578681)
            ·
              refine ⟨6174104778193909570184011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232139704258546093578681 6174104778193909570184011)
              ·
                refine ⟨9261157167290864355276017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174104778193909570184011 9261157167290864355276017)
                ·
                  refine ⟨6945867875468148266457013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261157167290864355276017 6945867875468148266457013)
                  ·
                    refine ⟨651175113325138899980345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6945867875468148266457013 651175113325138899980345)
                    ·
                      rfl

theorem cell23_3804477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3804477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804477 prefixEnd_3804477 := by exact prefixLift 3804477
  have htrace : WordTrace (prefixWord ++ tailWord_3804477) baseStart_3804477 baseEnd_3804477 := by
    simpa [prefixWord, tailWord_3804477, baseEnd_3804477] using wordTrace_append hprefix tailTrace_3804477
  have hstable : (prefixWord ++ tailWord_3804477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804477).length < 2 ^ (prefixWord ++ tailWord_3804477).sum := by decide
  have hdescent : baseEnd_3804477 < baseStart_3804477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804500 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_3804500 : Nat := 118140960795 + 3804500 * 2 ^ 59
def prefixEnd_3804500 : Nat := 4983230072969 + 3 ^ 40 * 3804500 * 2
def baseEnd_3804500 : Nat := 1953537150030470109953429

theorem tailTrace_3804500 : CollatzResearch.WordTrace tailWord_3804500 prefixEnd_3804500 1953537150030470109953429 := by
  unfold tailWord_3804500
  simp only [CollatzResearch.WordTrace]
  refine ⟨69380757358476865857661477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92507676477969154476881969 69380757358476865857661477)
  ·
    refine ⟨13008892004714412348311527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69380757358476865857661477 13008892004714412348311527)
    ·
      refine ⟨19513338007071618522467291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13008892004714412348311527 19513338007071618522467291)
      ·
        refine ⟨29270007010607427783700937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19513338007071618522467291 29270007010607427783700937)
        ·
          refine ⟨21952505257955570837775703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29270007010607427783700937 21952505257955570837775703)
          ·
            refine ⟨32928757886933356256663555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21952505257955570837775703 32928757886933356256663555)
            ·
              refine ⟨49393136830400034384995333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32928757886933356256663555 49393136830400034384995333)
              ·
                refine ⟨9261213155700006447186625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49393136830400034384995333 9261213155700006447186625)
                ·
                  refine ⟨6945909866775004835389969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261213155700006447186625 6945909866775004835389969)
                  ·
                    refine ⟨5209432400081253626542477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945909866775004835389969 5209432400081253626542477)
                    ·
                      refine ⟨1953537150030470109953429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5209432400081253626542477 1953537150030470109953429)
                      ·
                        rfl

theorem cell23_3804500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_3804500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804500 prefixEnd_3804500 := by exact prefixLift 3804500
  have htrace : WordTrace (prefixWord ++ tailWord_3804500) baseStart_3804500 baseEnd_3804500 := by
    simpa [prefixWord, tailWord_3804500, baseEnd_3804500] using wordTrace_append hprefix tailTrace_3804500
  have hstable : (prefixWord ++ tailWord_3804500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804500).length < 2 ^ (prefixWord ++ tailWord_3804500).sum := by decide
  have hdescent : baseEnd_3804500 < baseStart_3804500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804503 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 6]
def baseStart_3804503 : Nat := 118140960795 + 3804503 * 2 ^ 59
def prefixEnd_3804503 : Nat := 4983230072969 + 3 ^ 40 * 3804503 * 2
def baseEnd_3804503 : Nat := 217059854496937066468435

theorem tailTrace_3804503 : CollatzResearch.WordTrace tailWord_3804503 prefixEnd_3804503 217059854496937066468435 := by
  unfold tailWord_3804503
  simp only [CollatzResearch.WordTrace]
  refine ⟨138761624135942863227682163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92507749423961908818454775 138761624135942863227682163)
  ·
    refine ⟨208142436203914294841523245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138761624135942863227682163 208142436203914294841523245)
    ·
      refine ⟨78053413576467860565571217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208142436203914294841523245 78053413576467860565571217)
      ·
        refine ⟨58540060182350895424178413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78053413576467860565571217 58540060182350895424178413)
        ·
          refine ⟨21952522568381585784066905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58540060182350895424178413 21952522568381585784066905)
          ·
            refine ⟨16464391926286189338050179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21952522568381585784066905 16464391926286189338050179)
            ·
              refine ⟨24696587889429284007075269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16464391926286189338050179 24696587889429284007075269)
              ·
                refine ⟨4630610229267990751326613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24696587889429284007075269 4630610229267990751326613)
                ·
                  refine ⟨217059854496937066468435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4630610229267990751326613 217059854496937066468435)
                  ·
                    rfl

theorem cell23_3804503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 6].length) (baseStart_3804503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804503 prefixEnd_3804503 := by exact prefixLift 3804503
  have htrace : WordTrace (prefixWord ++ tailWord_3804503) baseStart_3804503 baseEnd_3804503 := by
    simpa [prefixWord, tailWord_3804503, baseEnd_3804503] using wordTrace_append hprefix tailTrace_3804503
  have hstable : (prefixWord ++ tailWord_3804503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804503).length < 2 ^ (prefixWord ++ tailWord_3804503).sum := by decide
  have hdescent : baseEnd_3804503 < baseStart_3804503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804540 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_3804540 : Nat := 118140960795 + 3804540 * 2 ^ 59
def prefixEnd_3804540 : Nat := 4983230072969 + 3 ^ 40 * 3804540 * 2
def baseEnd_3804540 : Nat := 1953557689256649953453245

theorem tailTrace_3804540 : CollatzResearch.WordTrace tailWord_3804540 prefixEnd_3804540 1953557689256649953453245 := by
  unfold tailWord_3804540
  simp only [CollatzResearch.WordTrace]
  refine ⟨69381486818404409273389537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92508649091205879031186049 69381486818404409273389537)
  ·
    refine ⟨52036115113803306955042153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69381486818404409273389537 52036115113803306955042153)
    ·
      refine ⟨39027086335352480216281615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52036115113803306955042153 39027086335352480216281615)
      ·
        refine ⟨58540629503028720324422423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39027086335352480216281615 58540629503028720324422423)
        ·
          refine ⟨87810944254543080486633635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58540629503028720324422423 87810944254543080486633635)
          ·
            refine ⟨131716416381814620729950453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87810944254543080486633635 131716416381814620729950453)
            ·
              refine ⟨12348414035795120693432855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131716416381814620729950453 12348414035795120693432855)
              ·
                refine ⟨18522621053692681040149283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12348414035795120693432855 18522621053692681040149283)
                ·
                  refine ⟨27783931580539021560223925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18522621053692681040149283 27783931580539021560223925)
                  ·
                    refine ⟨2604743585675533271270993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27783931580539021560223925 2604743585675533271270993)
                    ·
                      refine ⟨1953557689256649953453245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604743585675533271270993 1953557689256649953453245)
                      ·
                        rfl

theorem cell23_3804540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_3804540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804540 prefixEnd_3804540 := by exact prefixLift 3804540
  have htrace : WordTrace (prefixWord ++ tailWord_3804540) baseStart_3804540 baseEnd_3804540 := by
    simpa [prefixWord, tailWord_3804540, baseEnd_3804540] using wordTrace_append hprefix tailTrace_3804540
  have hstable : (prefixWord ++ tailWord_3804540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804540).length < 2 ^ (prefixWord ++ tailWord_3804540).sum := by decide
  have hdescent : baseEnd_3804540 < baseStart_3804540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804564 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3804564 : Nat := 118140960795 + 3804564 * 2 ^ 59
def prefixEnd_3804564 : Nat := 4983230072969 + 3 ^ 40 * 3804564 * 2
def baseEnd_3804564 : Nat := 1953570012792357859553135

theorem tailTrace_3804564 : CollatzResearch.WordTrace tailWord_3804564 prefixEnd_3804564 1953570012792357859553135 := by
  unfold tailWord_3804564
  simp only [CollatzResearch.WordTrace]
  refine ⟨69381924494360935322826373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92509232659147913763768497 69381924494360935322826373)
  ·
    refine ⟨13009110842692675373029945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69381924494360935322826373 13009110842692675373029945)
    ·
      refine ⟨9756833132019506529772459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13009110842692675373029945 9756833132019506529772459)
      ·
        refine ⟨14635249698029259794658689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9756833132019506529772459 14635249698029259794658689)
        ·
          refine ⟨10976437273521944845994017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14635249698029259794658689 10976437273521944845994017)
          ·
            refine ⟨8232327955141458634495513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10976437273521944845994017 8232327955141458634495513)
            ·
              refine ⟨6174245966356093975871635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232327955141458634495513 6174245966356093975871635)
              ·
                refine ⟨9261368949534140963807453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174245966356093975871635 9261368949534140963807453)
                ·
                  refine ⟨3473013356075302861427795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9261368949534140963807453 3473013356075302861427795)
                  ·
                    refine ⟨5209520034112954292141693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473013356075302861427795 5209520034112954292141693)
                    ·
                      refine ⟨1953570012792357859553135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5209520034112954292141693 1953570012792357859553135)
                      ·
                        rfl

theorem cell23_3804564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3804564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804564 prefixEnd_3804564 := by exact prefixLift 3804564
  have htrace : WordTrace (prefixWord ++ tailWord_3804564) baseStart_3804564 baseEnd_3804564 := by
    simpa [prefixWord, tailWord_3804564, baseEnd_3804564] using wordTrace_append hprefix tailTrace_3804564
  have hstable : (prefixWord ++ tailWord_3804564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804564).length < 2 ^ (prefixWord ++ tailWord_3804564).sum := by decide
  have hdescent : baseEnd_3804564 < baseStart_3804564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804584 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3804584 : Nat := 118140960795 + 3804584 * 2 ^ 59
def prefixEnd_3804584 : Nat := 4983230072969 + 3 ^ 40 * 3804584 * 2
def baseEnd_3804584 : Nat := 651193427468482593767681

theorem tailTrace_3804584 : CollatzResearch.WordTrace tailWord_3804584 prefixEnd_3804584 651193427468482593767681 := by
  unfold tailWord_3804584
  simp only [CollatzResearch.WordTrace]
  refine ⟨69382289224324707030690403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92509718965766276040920537 69382289224324707030690403)
  ·
    refine ⟨104073433836487060546035605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69382289224324707030690403 104073433836487060546035605)
    ·
      refine ⟨4878442211085330963095419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104073433836487060546035605 4878442211085330963095419)
      ·
        refine ⟨7317663316627996444643129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878442211085330963095419 7317663316627996444643129)
        ·
          refine ⟨5488247487470997333482347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7317663316627996444643129 5488247487470997333482347)
          ·
            refine ⟨8232371231206496000223521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488247487470997333482347 8232371231206496000223521)
            ·
              refine ⟨6174278423404872000167641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232371231206496000223521 6174278423404872000167641)
              ·
                refine ⟨4630708817553654000125731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174278423404872000167641 4630708817553654000125731)
                ·
                  refine ⟨6946063226330481000188597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630708817553654000125731 6946063226330481000188597)
                  ·
                    refine ⟨651193427468482593767681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6946063226330481000188597 651193427468482593767681)
                    ·
                      rfl

theorem cell23_3804584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3804584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804584 prefixEnd_3804584 := by exact prefixLift 3804584
  have htrace : WordTrace (prefixWord ++ tailWord_3804584) baseStart_3804584 baseEnd_3804584 := by
    simpa [prefixWord, tailWord_3804584, baseEnd_3804584] using wordTrace_append hprefix tailTrace_3804584
  have hstable : (prefixWord ++ tailWord_3804584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804584).length < 2 ^ (prefixWord ++ tailWord_3804584).sum := by decide
  have hdescent : baseEnd_3804584 < baseStart_3804584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804593 : List Nat := [1, 2, 2, 4, 1, 1, 3, 9]
def baseStart_3804593 : Nat := 118140960795 + 3804593 * 2 ^ 59
def prefixEnd_3804593 : Nat := 4983230072969 + 3 ^ 40 * 3804593 * 2
def baseEnd_3804593 : Nat := 72354996434494009114463

theorem tailTrace_3804593 : CollatzResearch.WordTrace tailWord_3804593 prefixEnd_3804593 72354996434494009114463 := by
  unfold tailWord_3804593
  simp only [CollatzResearch.WordTrace]
  refine ⟨138764906705616808598458433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92509937803744539065638955 138764906705616808598458433)
  ·
    refine ⟨104073680029212606448843825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138764906705616808598458433 104073680029212606448843825)
    ·
      refine ⟨78055260021909454836632869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104073680029212606448843825 78055260021909454836632869)
      ·
        refine ⟨14635361254108022781868663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78055260021909454836632869 14635361254108022781868663)
        ·
          refine ⟨21953041881162034172802995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14635361254108022781868663 21953041881162034172802995)
          ·
            refine ⟨32929562821743051259204493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953041881162034172802995 32929562821743051259204493)
            ·
              refine ⟨12348586058153644222201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32929562821743051259204493 12348586058153644222201685)
              ·
                refine ⟨72354996434494009114463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12348586058153644222201685 72354996434494009114463)
                ·
                  rfl

theorem cell23_3804593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 9].length) (baseStart_3804593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804593 prefixEnd_3804593 := by exact prefixLift 3804593
  have htrace : WordTrace (prefixWord ++ tailWord_3804593) baseStart_3804593 baseEnd_3804593 := by
    simpa [prefixWord, tailWord_3804593, baseEnd_3804593] using wordTrace_append hprefix tailTrace_3804593
  have hstable : (prefixWord ++ tailWord_3804593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804593).length < 2 ^ (prefixWord ++ tailWord_3804593).sum := by decide
  have hdescent : baseEnd_3804593 < baseStart_3804593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804663 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3804663 : Nat := 118140960795 + 3804663 * 2 ^ 59
def prefixEnd_3804663 : Nat := 4983230072969 + 3 ^ 40 * 3804663 * 2
def baseEnd_3804663 : Nat := 1953620847377152972215179

theorem tailTrace_3804663 : CollatzResearch.WordTrace tailWord_3804663 prefixEnd_3804663 1953620847377152972215179 := by
  unfold tailWord_3804663
  simp only [CollatzResearch.WordTrace]
  refine ⟨138767459815363210553506643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92511639876908807035671095 138767459815363210553506643)
  ·
    refine ⟨208151189723044815830259965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138767459815363210553506643 208151189723044815830259965)
    ·
      refine ⟨78056696146141805936347487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208151189723044815830259965 78056696146141805936347487)
      ·
        refine ⟨117085044219212708904521231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78056696146141805936347487 117085044219212708904521231)
        ·
          refine ⟨175627566328819063356781847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117085044219212708904521231 175627566328819063356781847)
          ·
            refine ⟨263441349493228595035172771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175627566328819063356781847 263441349493228595035172771)
            ·
              refine ⟨395162024239842892552759157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263441349493228595035172771 395162024239842892552759157)
              ·
                refine ⟨37046439772485271176821171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395162024239842892552759157 37046439772485271176821171)
                ·
                  refine ⟨55569659658727906765231757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37046439772485271176821171 55569659658727906765231757)
                  ·
                    refine ⟨20838622372022965036961909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55569659658727906765231757 20838622372022965036961909)
                    ·
                      refine ⟨1953620847377152972215179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20838622372022965036961909 1953620847377152972215179)
                      ·
                        rfl

theorem cell23_3804663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3804663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804663 prefixEnd_3804663 := by exact prefixLift 3804663
  have htrace : WordTrace (prefixWord ++ tailWord_3804663) baseStart_3804663 baseEnd_3804663 := by
    simpa [prefixWord, tailWord_3804663, baseEnd_3804663] using wordTrace_append hprefix tailTrace_3804663
  have hstable : (prefixWord ++ tailWord_3804663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804663).length < 2 ^ (prefixWord ++ tailWord_3804663).sum := by decide
  have hdescent : baseEnd_3804663 < baseStart_3804663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804678 : List Nat := [6, 2, 1, 1, 3, 1, 1, 8]
def baseStart_3804678 : Nat := 118140960795 + 3804678 * 2 ^ 59
def prefixEnd_3804678 : Nat := 4983230072969 + 3 ^ 40 * 3804678 * 2
def baseEnd_3804678 : Nat := 72356612947665570871393

theorem tailTrace_3804678 : CollatzResearch.WordTrace tailWord_3804678 prefixEnd_3804678 72356612947665570871393 := by
  unfold tailWord_3804678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336500215947152128603209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92512004606872578743535125 4336500215947152128603209)
  ·
    refine ⟨3252375161960364096452407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4336500215947152128603209 3252375161960364096452407)
    ·
      refine ⟨4878562742940546144678611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252375161960364096452407 4878562742940546144678611)
      ·
        refine ⟨7317844114410819217017917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878562742940546144678611 7317844114410819217017917)
        ·
          refine ⟨2744191542904057206381719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7317844114410819217017917 2744191542904057206381719)
          ·
            refine ⟨4116287314356085809572579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744191542904057206381719 4116287314356085809572579)
            ·
              refine ⟨6174430971534128714358869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116287314356085809572579 6174430971534128714358869)
              ·
                refine ⟨72356612947665570871393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6174430971534128714358869 72356612947665570871393)
                ·
                  rfl

theorem cell23_3804678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_3804678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804678 prefixEnd_3804678 := by exact prefixLift 3804678
  have htrace : WordTrace (prefixWord ++ tailWord_3804678) baseStart_3804678 baseEnd_3804678 := by
    simpa [prefixWord, tailWord_3804678, baseEnd_3804678] using wordTrace_append hprefix tailTrace_3804678
  have hstable : (prefixWord ++ tailWord_3804678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804678).length < 2 ^ (prefixWord ++ tailWord_3804678).sum := by decide
  have hdescent : baseEnd_3804678 < baseStart_3804678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804680 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_3804680 : Nat := 118140960795 + 3804680 * 2 ^ 59
def prefixEnd_3804680 : Nat := 4983230072969 + 3 ^ 40 * 3804680 * 2
def baseEnd_3804680 : Nat := 1953629576548279405702601

theorem tailTrace_3804680 : CollatzResearch.WordTrace tailWord_3804680 prefixEnd_3804680 1953629576548279405702601 := by
  unfold tailWord_3804680
  simp only [CollatzResearch.WordTrace]
  refine ⟨69384039928150811228437747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92512053237534414971250329 69384039928150811228437747)
  ·
    refine ⟨104076059892226216842656621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69384039928150811228437747 104076059892226216842656621)
    ·
      refine ⟨39028522459584831315996233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104076059892226216842656621 39028522459584831315996233)
      ·
        refine ⟨29271391844688623486997175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39028522459584831315996233 29271391844688623486997175)
        ·
          refine ⟨43907087767032935230495763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29271391844688623486997175 43907087767032935230495763)
          ·
            refine ⟨65860631650549402845743645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43907087767032935230495763 65860631650549402845743645)
            ·
              refine ⟨24697736868956026067153867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65860631650549402845743645 24697736868956026067153867)
              ·
                refine ⟨37046605303434039100730801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24697736868956026067153867 37046605303434039100730801)
                ·
                  refine ⟨27784953977575529325548101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37046605303434039100730801 27784953977575529325548101)
                  ·
                    refine ⟨5209678870795411748540269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27784953977575529325548101 5209678870795411748540269)
                    ·
                      refine ⟨1953629576548279405702601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5209678870795411748540269 1953629576548279405702601)
                      ·
                        rfl

theorem cell23_3804680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_3804680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804680 prefixEnd_3804680 := by exact prefixLift 3804680
  have htrace : WordTrace (prefixWord ++ tailWord_3804680) baseStart_3804680 baseEnd_3804680 := by
    simpa [prefixWord, tailWord_3804680, baseEnd_3804680] using wordTrace_append hprefix tailTrace_3804680
  have hstable : (prefixWord ++ tailWord_3804680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804680).length < 2 ^ (prefixWord ++ tailWord_3804680).sum := by decide
  have hdescent : baseEnd_3804680 < baseStart_3804680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804700 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 7]
def baseStart_3804700 : Nat := 118140960795 + 3804700 * 2 ^ 59
def prefixEnd_3804700 : Nat := 4983230072969 + 3 ^ 40 * 3804700 * 2
def baseEnd_3804700 : Nat := 217071094017929925272501

theorem tailTrace_3804700 : CollatzResearch.WordTrace tailWord_3804700 prefixEnd_3804700 217071094017929925272501 := by
  unfold tailWord_3804700
  simp only [CollatzResearch.WordTrace]
  refine ⟨69384404658114582936301777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92512539544152777248402369 69384404658114582936301777)
  ·
    refine ⟨52038303493585937202226333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69384404658114582936301777 52038303493585937202226333)
    ·
      refine ⟨19514363810094726450834875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52038303493585937202226333 19514363810094726450834875)
      ·
        refine ⟨29271545715142089676252313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19514363810094726450834875 29271545715142089676252313)
        ·
          refine ⟨21953659286356567257189235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29271545715142089676252313 21953659286356567257189235)
          ·
            refine ⟨32930488929534850885783853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953659286356567257189235 32930488929534850885783853)
            ·
              refine ⟨12348933348575569082168945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32930488929534850885783853 12348933348575569082168945)
              ·
                refine ⟨9261700011431676811626709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12348933348575569082168945 9261700011431676811626709)
                ·
                  refine ⟨217071094017929925272501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9261700011431676811626709 217071094017929925272501)
                  ·
                    rfl

theorem cell23_3804700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_3804700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804700 prefixEnd_3804700 := by exact prefixLift 3804700
  have htrace : WordTrace (prefixWord ++ tailWord_3804700) baseStart_3804700 baseEnd_3804700 := by
    simpa [prefixWord, tailWord_3804700, baseEnd_3804700] using wordTrace_append hprefix tailTrace_3804700
  have hstable : (prefixWord ++ tailWord_3804700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804700).length < 2 ^ (prefixWord ++ tailWord_3804700).sum := by decide
  have hdescent : baseEnd_3804700 < baseStart_3804700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804730 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_3804730 : Nat := 118140960795 + 3804730 * 2 ^ 59
def prefixEnd_3804730 : Nat := 4983230072969 + 3 ^ 40 * 3804730 * 2
def baseEnd_3804730 : Nat := 651218416860334736692457

theorem tailTrace_3804730 : CollatzResearch.WordTrace tailWord_3804730 prefixEnd_3804730 651218416860334736692457 := by
  unfold tailWord_3804730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34692475876530120249048911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92513269004080320664130429 34692475876530120249048911)
  ·
    refine ⟨52038713814795180373573367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34692475876530120249048911 52038713814795180373573367)
    ·
      refine ⟨78058070722192770560360051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52038713814795180373573367 78058070722192770560360051)
      ·
        refine ⟨117087106083289155840540077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78058070722192770560360051 117087106083289155840540077)
        ·
          refine ⟨43907664781233433440202529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117087106083289155840540077 43907664781233433440202529)
          ·
            refine ⟨32930748585925075080151897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43907664781233433440202529 32930748585925075080151897)
            ·
              refine ⟨24698061439443806310113923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32930748585925075080151897 24698061439443806310113923)
              ·
                refine ⟨37047092159165709465170885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24698061439443806310113923 37047092159165709465170885)
                ·
                  refine ⟨6946329779843570524719541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37047092159165709465170885 6946329779843570524719541)
                  ·
                    refine ⟨651218416860334736692457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6946329779843570524719541 651218416860334736692457)
                    ·
                      rfl

theorem cell23_3804730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_3804730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804730 prefixEnd_3804730 := by exact prefixLift 3804730
  have htrace : WordTrace (prefixWord ++ tailWord_3804730) baseStart_3804730 baseEnd_3804730 := by
    simpa [prefixWord, tailWord_3804730, baseEnd_3804730] using wordTrace_append hprefix tailTrace_3804730
  have hstable : (prefixWord ++ tailWord_3804730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804730).length < 2 ^ (prefixWord ++ tailWord_3804730).sum := by decide
  have hdescent : baseEnd_3804730 < baseStart_3804730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804807 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 6]
def baseStart_3804807 : Nat := 118140960795 + 3804807 * 2 ^ 59
def prefixEnd_3804807 : Nat := 4983230072969 + 3 ^ 40 * 3804807 * 2
def baseEnd_3804807 : Nat := 217077198732377823201613

theorem tailTrace_3804807 : CollatzResearch.WordTrace tailWord_3804807 prefixEnd_3804807 217077198732377823201613 := by
  unfold tailWord_3804807
  simp only [CollatzResearch.WordTrace]
  refine ⟨138772711926841523146748675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92515141284561015431165783 138772711926841523146748675)
  ·
    refine ⟨208159067890262284720123013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138772711926841523146748675 208159067890262284720123013)
    ·
      refine ⟨39029825229424178385023065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208159067890262284720123013 39029825229424178385023065)
      ·
        refine ⟨29272368922068133788767299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39029825229424178385023065 29272368922068133788767299)
        ·
          refine ⟨43908553383102200683150949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29272368922068133788767299 43908553383102200683150949)
          ·
            refine ⟨8232853759331662628090803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43908553383102200683150949 8232853759331662628090803)
            ·
              refine ⟨12349280638997493942136205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232853759331662628090803 12349280638997493942136205)
              ·
                refine ⟨4630980239624060228301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12349280638997493942136205 4630980239624060228301077)
                ·
                  refine ⟨217077198732377823201613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4630980239624060228301077 217077198732377823201613)
                  ·
                    rfl

theorem cell23_3804807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 6].length) (baseStart_3804807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804807 prefixEnd_3804807 := by exact prefixLift 3804807
  have htrace : WordTrace (prefixWord ++ tailWord_3804807) baseStart_3804807 baseEnd_3804807 := by
    simpa [prefixWord, tailWord_3804807, baseEnd_3804807] using wordTrace_append hprefix tailTrace_3804807
  have hstable : (prefixWord ++ tailWord_3804807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804807).length < 2 ^ (prefixWord ++ tailWord_3804807).sum := by decide
  have hdescent : baseEnd_3804807 < baseStart_3804807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804837 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_3804837 : Nat := 118140960795 + 3804837 * 2 ^ 59
def prefixEnd_3804837 : Nat := 4983230072969 + 3 ^ 40 * 3804837 * 2
def baseEnd_3804837 : Nat := 651236731003678430479793

theorem tailTrace_3804837 : CollatzResearch.WordTrace tailWord_3804837 prefixEnd_3804837 651236731003678430479793 := by
  unfold tailWord_3804837
  simp only [CollatzResearch.WordTrace]
  refine ⟨138773806116732838270340765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92515870744488558846893843 138773806116732838270340765)
  ·
    refine ⟨52040177293774814351377787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138773806116732838270340765 52040177293774814351377787)
    ·
      refine ⟨78060265940662221527066681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52040177293774814351377787 78060265940662221527066681)
      ·
        refine ⟨58545199455496666145300011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78060265940662221527066681 58545199455496666145300011)
        ·
          refine ⟨87817799183244999217950017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58545199455496666145300011 87817799183244999217950017)
          ·
            refine ⟨65863349387433749413462513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87817799183244999217950017 65863349387433749413462513)
            ·
              refine ⟨49397512040575312060096885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65863349387433749413462513 49397512040575312060096885)
              ·
                refine ⟨4631016753803935505634083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49397512040575312060096885 4631016753803935505634083)
                ·
                  refine ⟨6946525130705903258451125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631016753803935505634083 6946525130705903258451125)
                  ·
                    refine ⟨651236731003678430479793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6946525130705903258451125 651236731003678430479793)
                    ·
                      rfl

theorem cell23_3804837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_3804837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804837 prefixEnd_3804837 := by exact prefixLift 3804837
  have htrace : WordTrace (prefixWord ++ tailWord_3804837) baseStart_3804837 baseEnd_3804837 := by
    simpa [prefixWord, tailWord_3804837, baseEnd_3804837] using wordTrace_append hprefix tailTrace_3804837
  have hstable : (prefixWord ++ tailWord_3804837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804837).length < 2 ^ (prefixWord ++ tailWord_3804837).sum := by decide
  have hdescent : baseEnd_3804837 < baseStart_3804837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804851 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 1, 1, 3]
def baseStart_3804851 : Nat := 118140960795 + 3804851 * 2 ^ 59
def prefixEnd_3804851 : Nat := 4983230072969 + 3 ^ 40 * 3804851 * 2
def baseEnd_3804851 : Nat := 1953717381740198236664315

theorem tailTrace_3804851 : CollatzResearch.WordTrace tailWord_3804851 prefixEnd_3804851 1953717381740198236664315 := by
  unfold tailWord_3804851
  simp only [CollatzResearch.WordTrace]
  refine ⟨138774316738682118661350407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92516211159121412440900271 138774316738682118661350407)
  ·
    refine ⟨208161475108023177992025611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138774316738682118661350407 208161475108023177992025611)
    ·
      refine ⟨312242212662034766988038417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208161475108023177992025611 312242212662034766988038417)
      ·
        refine ⟨234181659496526075241028813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312242212662034766988038417 234181659496526075241028813)
        ·
          refine ⟨87818122311197278215385805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234181659496526075241028813 87818122311197278215385805)
          ·
            refine ⟨32931795866698979330769677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87818122311197278215385805 32931795866698979330769677)
            ·
              refine ⟨12349423450012117249038629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32931795866698979330769677 12349423450012117249038629)
              ·
                refine ⟨2315516896877271984194743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12349423450012117249038629 2315516896877271984194743)
                ·
                  refine ⟨3473275345315907976292115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315516896877271984194743 3473275345315907976292115)
                  ·
                    refine ⟨5209913017973861964438173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473275345315907976292115 5209913017973861964438173)
                    ·
                      refine ⟨1953717381740198236664315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5209913017973861964438173 1953717381740198236664315)
                      ·
                        rfl

theorem cell23_3804851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 1, 3].length) (baseStart_3804851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804851 prefixEnd_3804851 := by exact prefixLift 3804851
  have htrace : WordTrace (prefixWord ++ tailWord_3804851) baseStart_3804851 baseEnd_3804851 := by
    simpa [prefixWord, tailWord_3804851, baseEnd_3804851] using wordTrace_append hprefix tailTrace_3804851
  have hstable : (prefixWord ++ tailWord_3804851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804851).length < 2 ^ (prefixWord ++ tailWord_3804851).sum := by decide
  have hdescent : baseEnd_3804851 < baseStart_3804851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804857 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3804857 : Nat := 118140960795 + 3804857 * 2 ^ 59
def prefixEnd_3804857 : Nat := 4983230072969 + 3 ^ 40 * 3804857 * 2
def baseEnd_3804857 : Nat := 1953720462624125213189287

theorem tailTrace_3804857 : CollatzResearch.WordTrace tailWord_3804857 prefixEnd_3804857 1953720462624125213189287 := by
  unfold tailWord_3804857
  simp only [CollatzResearch.WordTrace]
  refine ⟨138774535576660381686068825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92516357051106921124045883 138774535576660381686068825)
  ·
    refine ⟨104080901682495286264551619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138774535576660381686068825 104080901682495286264551619)
    ·
      refine ⟨156121352523742929396827429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104080901682495286264551619 156121352523742929396827429)
      ·
        refine ⟨29272753598201799261905143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156121352523742929396827429 29272753598201799261905143)
        ·
          refine ⟨43909130397302698892857715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29272753598201799261905143 43909130397302698892857715)
          ·
            refine ⟨65863695595954048339286573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43909130397302698892857715 65863695595954048339286573)
            ·
              refine ⟨24698885848482768127232465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65863695595954048339286573 24698885848482768127232465)
              ·
                refine ⟨18524164386362076095424349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24698885848482768127232465 18524164386362076095424349)
                ·
                  refine ⟨6946561644885778535784131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18524164386362076095424349 6946561644885778535784131)
                  ·
                    refine ⟨10419842467328667803676197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6946561644885778535784131 10419842467328667803676197)
                    ·
                      refine ⟨1953720462624125213189287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10419842467328667803676197 1953720462624125213189287)
                      ·
                        rfl

theorem cell23_3804857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3804857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804857 prefixEnd_3804857 := by exact prefixLift 3804857
  have htrace : WordTrace (prefixWord ++ tailWord_3804857) baseStart_3804857 baseEnd_3804857 := by
    simpa [prefixWord, tailWord_3804857, baseEnd_3804857] using wordTrace_append hprefix tailTrace_3804857
  have hstable : (prefixWord ++ tailWord_3804857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804857).length < 2 ^ (prefixWord ++ tailWord_3804857).sum := by decide
  have hdescent : baseEnd_3804857 < baseStart_3804857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804884 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_3804884 : Nat := 118140960795 + 3804884 * 2 ^ 59
def prefixEnd_3804884 : Nat := 4983230072969 + 3 ^ 40 * 3804884 * 2
def baseEnd_3804884 : Nat := 651244775533932202517221

theorem tailTrace_3804884 : CollatzResearch.WordTrace tailWord_3804884 prefixEnd_3804884 651244775533932202517221 := by
  unfold tailWord_3804884
  simp only [CollatzResearch.WordTrace]
  refine ⟨69387760173781282648650853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92517013565041710198201137 69387760173781282648650853)
  ·
    refine ⟨13010205032583990496622035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69387760173781282648650853 13010205032583990496622035)
    ·
      refine ⟨19515307548875985744933053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13010205032583990496622035 19515307548875985744933053)
      ·
        refine ⟨7318240330828494654349895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19515307548875985744933053 7318240330828494654349895)
        ·
          refine ⟨10977360496242741981524843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318240330828494654349895 10977360496242741981524843)
          ·
            refine ⟨16466040744364112972287265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10977360496242741981524843 16466040744364112972287265)
            ·
              refine ⟨12349530558273084729215449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16466040744364112972287265 12349530558273084729215449)
              ·
                refine ⟨9262147918704813546911587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12349530558273084729215449 9262147918704813546911587)
                ·
                  refine ⟨13893221878057220320367381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9262147918704813546911587 13893221878057220320367381)
                  ·
                    refine ⟨651244775533932202517221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13893221878057220320367381 651244775533932202517221)
                    ·
                      rfl

theorem cell23_3804884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_3804884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804884 prefixEnd_3804884 := by exact prefixLift 3804884
  have htrace : WordTrace (prefixWord ++ tailWord_3804884) baseStart_3804884 baseEnd_3804884 := by
    simpa [prefixWord, tailWord_3804884, baseEnd_3804884] using wordTrace_append hprefix tailTrace_3804884
  have hstable : (prefixWord ++ tailWord_3804884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804884).length < 2 ^ (prefixWord ++ tailWord_3804884).sum := by decide
  have hdescent : baseEnd_3804884 < baseStart_3804884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804887 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_3804887 : Nat := 118140960795 + 3804887 * 2 ^ 59
def prefixEnd_3804887 : Nat := 4983230072969 + 3 ^ 40 * 3804887 * 2
def baseEnd_3804887 : Nat := 1953735867043760095814149

theorem tailTrace_3804887 : CollatzResearch.WordTrace tailWord_3804887 prefixEnd_3804887 1953735867043760095814149 := by
  unfold tailWord_3804887
  simp only [CollatzResearch.WordTrace]
  refine ⟨138775629766551696809660915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92517086511034464539773943 138775629766551696809660915)
  ·
    refine ⟨208163444649827545214491373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138775629766551696809660915 208163444649827545214491373)
    ·
      refine ⟨78061291743685329455434265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208163444649827545214491373 78061291743685329455434265)
      ·
        refine ⟨58545968807763997091575699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78061291743685329455434265 58545968807763997091575699)
        ·
          refine ⟨87818953211645995637363549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58545968807763997091575699 87818953211645995637363549)
          ·
            refine ⟨32932107454367248364011331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87818953211645995637363549 32932107454367248364011331)
            ·
              refine ⟨49398161181550872546016997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32932107454367248364011331 49398161181550872546016997)
              ·
                refine ⟨9262155221540788602378187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49398161181550872546016997 9262155221540788602378187)
                ·
                  refine ⟨13893232832311182903567281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9262155221540788602378187 13893232832311182903567281)
                  ·
                    refine ⟨10419924624233387177675461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13893232832311182903567281 10419924624233387177675461)
                    ·
                      refine ⟨1953735867043760095814149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10419924624233387177675461 1953735867043760095814149)
                      ·
                        rfl

theorem cell23_3804887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_3804887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804887 prefixEnd_3804887 := by exact prefixLift 3804887
  have htrace : WordTrace (prefixWord ++ tailWord_3804887) baseStart_3804887 baseEnd_3804887 := by
    simpa [prefixWord, tailWord_3804887, baseEnd_3804887] using wordTrace_append hprefix tailTrace_3804887
  have hstable : (prefixWord ++ tailWord_3804887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804887).length < 2 ^ (prefixWord ++ tailWord_3804887).sum := by decide
  have hdescent : baseEnd_3804887 < baseStart_3804887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804897 : List Nat := [1, 2, 3, 1, 5, 1, 10]
def baseStart_3804897 : Nat := 118140960795 + 3804897 * 2 ^ 59
def prefixEnd_3804897 : Nat := 4983230072969 + 3 ^ 40 * 3804897 * 2
def baseEnd_3804897 : Nat := 24120259282102531564063

theorem tailTrace_3804897 : CollatzResearch.WordTrace tailWord_3804897 prefixEnd_3804897 24120259282102531564063 := by
  unfold tailWord_3804897
  simp only [CollatzResearch.WordTrace]
  refine ⟨138775994496515468517524945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92517329664343645678349963 138775994496515468517524945)
  ·
    refine ⟨104081995872386601388143709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138775994496515468517524945 104081995872386601388143709)
    ·
      refine ⟨39030748452144975520553891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104081995872386601388143709 39030748452144975520553891)
      ·
        refine ⟨58546122678217463280830837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39030748452144975520553891 58546122678217463280830837)
        ·
          refine ⟨5488699001082887182577891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58546122678217463280830837 5488699001082887182577891)
          ·
            refine ⟨8233048501624330773866837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488699001082887182577891 8233048501624330773866837)
            ·
              refine ⟨24120259282102531564063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8233048501624330773866837 24120259282102531564063)
              ·
                rfl

theorem cell23_3804897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 10].length) (baseStart_3804897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804897 prefixEnd_3804897 := by exact prefixLift 3804897
  have htrace : WordTrace (prefixWord ++ tailWord_3804897) baseStart_3804897 baseEnd_3804897 := by
    simpa [prefixWord, tailWord_3804897, baseEnd_3804897] using wordTrace_append hprefix tailTrace_3804897
  have hstable : (prefixWord ++ tailWord_3804897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804897).length < 2 ^ (prefixWord ++ tailWord_3804897).sum := by decide
  have hdescent : baseEnd_3804897 < baseStart_3804897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804907 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 3]
def baseStart_3804907 : Nat := 118140960795 + 3804907 * 2 ^ 59
def prefixEnd_3804907 : Nat := 4983230072969 + 3 ^ 40 * 3804907 * 2
def baseEnd_3804907 : Nat := 1953746136656850017564057

theorem tailTrace_3804907 : CollatzResearch.WordTrace tailWord_3804907 prefixEnd_3804907 1953746136656850017564057 := by
  unfold tailWord_3804907
  simp only [CollatzResearch.WordTrace]
  refine ⟨138776359226479240225388975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92517572817652826816925983 138776359226479240225388975)
  ·
    refine ⟨208164538839718860338083463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138776359226479240225388975 208164538839718860338083463)
    ·
      refine ⟨312246808259578290507125195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208164538839718860338083463 312246808259578290507125195)
      ·
        refine ⟨468370212389367435760687793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312246808259578290507125195 468370212389367435760687793)
        ·
          refine ⟨351277659292025576820515845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468370212389367435760687793 351277659292025576820515845)
          ·
            refine ⟨65864561117254795653846721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351277659292025576820515845 65864561117254795653846721)
            ·
              refine ⟨49398420837941096740385041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65864561117254795653846721 49398420837941096740385041)
              ·
                refine ⟨37048815628455822555288781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49398420837941096740385041 37048815628455822555288781)
                ·
                  refine ⟨13893305860670933458233293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37048815628455822555288781 13893305860670933458233293)
                  ·
                    refine ⟨5209989697751600046837485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13893305860670933458233293 5209989697751600046837485)
                    ·
                      refine ⟨1953746136656850017564057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5209989697751600046837485 1953746136656850017564057)
                      ·
                        rfl

theorem cell23_3804907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 3].length) (baseStart_3804907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804907 prefixEnd_3804907 := by exact prefixLift 3804907
  have htrace : WordTrace (prefixWord ++ tailWord_3804907) baseStart_3804907 baseEnd_3804907 := by
    simpa [prefixWord, tailWord_3804907, baseEnd_3804907] using wordTrace_append hprefix tailTrace_3804907
  have hstable : (prefixWord ++ tailWord_3804907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804907).length < 2 ^ (prefixWord ++ tailWord_3804907).sum := by decide
  have hdescent : baseEnd_3804907 < baseStart_3804907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804908 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 1, 2, 2]
def baseStart_3804908 : Nat := 118140960795 + 3804908 * 2 ^ 59
def prefixEnd_3804908 : Nat := 4983230072969 + 3 ^ 40 * 3804908 * 2
def baseEnd_3804908 : Nat := 1953746650137504513651553

theorem tailTrace_3804908 : CollatzResearch.WordTrace tailWord_3804908 prefixEnd_3804908 1953746650137504513651553 := by
  unfold tailWord_3804908
  simp only [CollatzResearch.WordTrace]
  refine ⟨69388197849737808698087689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92517597132983744930783585 69388197849737808698087689)
  ·
    refine ⟨52041148387303356523565767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69388197849737808698087689 52041148387303356523565767)
    ·
      refine ⟨78061722580955034785348651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52041148387303356523565767 78061722580955034785348651)
      ·
        refine ⟨117092583871432552178022977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78061722580955034785348651 117092583871432552178022977)
        ·
          refine ⟨87819437903574414133517233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117092583871432552178022977 87819437903574414133517233)
          ·
            refine ⟨65864578427680810600137925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87819437903574414133517233 65864578427680810600137925)
            ·
              refine ⟨12349608455190151987525861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65864578427680810600137925 12349608455190151987525861)
              ·
                refine ⟨2315551585348153497661099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12349608455190151987525861 2315551585348153497661099)
                ·
                  refine ⟨3473327378022230246491649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315551585348153497661099 3473327378022230246491649)
                  ·
                    refine ⟨2604995533516672684868737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3473327378022230246491649 2604995533516672684868737)
                    ·
                      refine ⟨1953746650137504513651553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2604995533516672684868737 1953746650137504513651553)
                      ·
                        rfl

theorem cell23_3804908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_3804908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804908 prefixEnd_3804908 := by exact prefixLift 3804908
  have htrace : WordTrace (prefixWord ++ tailWord_3804908) baseStart_3804908 baseEnd_3804908 := by
    simpa [prefixWord, tailWord_3804908, baseEnd_3804908] using wordTrace_append hprefix tailTrace_3804908
  have hstable : (prefixWord ++ tailWord_3804908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804908).length < 2 ^ (prefixWord ++ tailWord_3804908).sum := by decide
  have hdescent : baseEnd_3804908 < baseStart_3804908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804918 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_3804918 : Nat := 118140960795 + 3804918 * 2 ^ 59
def prefixEnd_3804918 : Nat := 4983230072969 + 3 ^ 40 * 3804918 * 2
def baseEnd_3804918 : Nat := 651250594981349824842169

theorem tailTrace_3804918 : CollatzResearch.WordTrace tailWord_3804918 prefixEnd_3804918 651250594981349824842169 := by
  unfold tailWord_3804918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673547526839961819002463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92517840286292926069359605 8673547526839961819002463)
  ·
    refine ⟨13010321290259942728503695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8673547526839961819002463 13010321290259942728503695)
    ·
      refine ⟨19515481935389914092755543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13010321290259942728503695 19515481935389914092755543)
      ·
        refine ⟨29273222903084871139133315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19515481935389914092755543 29273222903084871139133315)
        ·
          refine ⟨43909834354627306708699973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29273222903084871139133315 43909834354627306708699973)
          ·
            refine ⟨8233093941492620007881245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43909834354627306708699973 8233093941492620007881245)
            ·
              refine ⟨3087410228059732502955467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8233093941492620007881245 3087410228059732502955467)
              ·
                refine ⟨4631115342089598754433201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087410228059732502955467 4631115342089598754433201)
                ·
                  refine ⟨3473336506567199065824901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631115342089598754433201 3473336506567199065824901)
                  ·
                    refine ⟨651250594981349824842169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3473336506567199065824901 651250594981349824842169)
                    ·
                      rfl

theorem cell23_3804918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_3804918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804918 prefixEnd_3804918 := by exact prefixLift 3804918
  have htrace : WordTrace (prefixWord ++ tailWord_3804918) baseStart_3804918 baseEnd_3804918 := by
    simpa [prefixWord, tailWord_3804918, baseEnd_3804918] using wordTrace_append hprefix tailTrace_3804918
  have hstable : (prefixWord ++ tailWord_3804918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804918).length < 2 ^ (prefixWord ++ tailWord_3804918).sum := by decide
  have hdescent : baseEnd_3804918 < baseStart_3804918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804948 : List Nat := [2, 4, 4, 1, 1, 2, 9]
def baseStart_3804948 : Nat := 118140960795 + 3804948 * 2 ^ 59
def prefixEnd_3804948 : Nat := 4983230072969 + 3 ^ 40 * 3804948 * 2
def baseEnd_3804948 : Nat := 24120582584736843915449

theorem tailTrace_3804948 : CollatzResearch.WordTrace tailWord_3804948 prefixEnd_3804948 24120582584736843915449 := by
  unfold tailWord_3804948
  simp only [CollatzResearch.WordTrace]
  refine ⟨69388927309665352113815749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92518569746220469485087665 69388927309665352113815749)
  ·
    refine ⟨13010423870562253521340453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69388927309665352113815749 13010423870562253521340453)
    ·
      refine ⟨2439454475730422535251335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13010423870562253521340453 2439454475730422535251335)
      ·
        refine ⟨3659181713595633802877003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439454475730422535251335 3659181713595633802877003)
        ·
          refine ⟨5488772570393450704315505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659181713595633802877003 5488772570393450704315505)
          ·
            refine ⟨4116579427795088028236629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488772570393450704315505 4116579427795088028236629)
            ·
              refine ⟨24120582584736843915449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4116579427795088028236629 24120582584736843915449)
              ·
                rfl

theorem cell23_3804948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 9].length) (baseStart_3804948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3804948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3804948 prefixEnd_3804948 := by exact prefixLift 3804948
  have htrace : WordTrace (prefixWord ++ tailWord_3804948) baseStart_3804948 baseEnd_3804948 := by
    simpa [prefixWord, tailWord_3804948, baseEnd_3804948] using wordTrace_append hprefix tailTrace_3804948
  have hstable : (prefixWord ++ tailWord_3804948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804948).length < 2 ^ (prefixWord ++ tailWord_3804948).sum := by decide
  have hdescent : baseEnd_3804948 < baseStart_3804948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805015 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 2, 2, 2]
def baseStart_3805015 : Nat := 118140960795 + 3805015 * 2 ^ 59
def prefixEnd_3805015 : Nat := 4983230072969 + 3 ^ 40 * 3805015 * 2
def baseEnd_3805015 : Nat := 1953801592567535595013561

theorem tailTrace_3805015 : CollatzResearch.WordTrace tailWord_3805015 prefixEnd_3805015 1953801592567535595013561 := by
  unfold tailWord_3805015
  simp only [CollatzResearch.WordTrace]
  refine ⟨138780298310087974670320499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92520198873391983113546999 138780298310087974670320499)
  ·
    refine ⟨208170447465131962005480749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138780298310087974670320499 208170447465131962005480749)
    ·
      refine ⟨78063917799424485752055281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208170447465131962005480749 78063917799424485752055281)
      ·
        refine ⟨58547938349568364314041461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78063917799424485752055281 58547938349568364314041461)
        ·
          refine ⟨5488869220272034154441387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58547938349568364314041461 5488869220272034154441387)
          ·
            refine ⟨8233303830408051231662081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488869220272034154441387 8233303830408051231662081)
            ·
              refine ⟨6174977872806038423746561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8233303830408051231662081 6174977872806038423746561)
              ·
                refine ⟨4631233404604528817809921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174977872806038423746561 4631233404604528817809921)
                ·
                  refine ⟨3473425053453396613357441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631233404604528817809921 3473425053453396613357441)
                  ·
                    refine ⟨2605068790090047460018081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3473425053453396613357441 2605068790090047460018081)
                    ·
                      refine ⟨1953801592567535595013561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605068790090047460018081 1953801592567535595013561)
                      ·
                        rfl

theorem cell23_3805015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_3805015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805015 prefixEnd_3805015 := by exact prefixLift 3805015
  have htrace : WordTrace (prefixWord ++ tailWord_3805015) baseStart_3805015 baseEnd_3805015 := by
    simpa [prefixWord, tailWord_3805015, baseEnd_3805015] using wordTrace_append hprefix tailTrace_3805015
  have hstable : (prefixWord ++ tailWord_3805015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805015).length < 2 ^ (prefixWord ++ tailWord_3805015).sum := by decide
  have hdescent : baseEnd_3805015 < baseStart_3805015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805145 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 6]
def baseStart_3805145 : Nat := 118140960795 + 3805145 * 2 ^ 59
def prefixEnd_3805145 : Nat := 4983230072969 + 3 ^ 40 * 3805145 * 2
def baseEnd_3805145 : Nat := 217096482783624454043107

theorem tailTrace_3805145 : CollatzResearch.WordTrace tailWord_3805145 prefixEnd_3805145 217096482783624454043107 := by
  unfold tailWord_3805145
  simp only [CollatzResearch.WordTrace]
  refine ⟨138785039799617006872552889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92523359866411337915035259 138785039799617006872552889)
  ·
    refine ⟨104088779849712755154414667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138785039799617006872552889 104088779849712755154414667)
    ·
      refine ⟨156133169774569132731622001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104088779849712755154414667 156133169774569132731622001)
      ·
        refine ⟨117099877330926849548716501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156133169774569132731622001 117099877330926849548716501)
        ·
          refine ⟨2744528374943598036298043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117099877330926849548716501 2744528374943598036298043)
          ·
            refine ⟨4116792562415397054447065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744528374943598036298043 4116792562415397054447065)
            ·
              refine ⟨3087594421811547790835299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116792562415397054447065 3087594421811547790835299)
              ·
                refine ⟨4631391632717321686252949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087594421811547790835299 4631391632717321686252949)
                ·
                  refine ⟨217096482783624454043107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4631391632717321686252949 217096482783624454043107)
                  ·
                    rfl

theorem cell23_3805145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 6].length) (baseStart_3805145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805145 prefixEnd_3805145 := by exact prefixLift 3805145
  have htrace : WordTrace (prefixWord ++ tailWord_3805145) baseStart_3805145 baseEnd_3805145 := by
    simpa [prefixWord, tailWord_3805145, baseEnd_3805145] using wordTrace_append hprefix tailTrace_3805145
  have hstable : (prefixWord ++ tailWord_3805145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805145).length < 2 ^ (prefixWord ++ tailWord_3805145).sum := by decide
  have hdescent : baseEnd_3805145 < baseStart_3805145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805164 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_3805164 : Nat := 118140960795 + 3805164 * 2 ^ 59
def prefixEnd_3805164 : Nat := 4983230072969 + 3 ^ 40 * 3805164 * 2
def baseEnd_3805164 : Nat := 1953878101185055512050375

theorem tailTrace_3805164 : CollatzResearch.WordTrace tailWord_3805164 prefixEnd_3805164 1953878101185055512050375 := by
  unfold tailWord_3805164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69392866393274086558747273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92523821857698782078329697 69392866393274086558747273)
  ·
    refine ⟨52044649794955564919060455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69392866393274086558747273 52044649794955564919060455)
    ·
      refine ⟨78066974692433347378590683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52044649794955564919060455 78066974692433347378590683)
      ·
        refine ⟨117100462038650021067886025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78066974692433347378590683 117100462038650021067886025)
        ·
          refine ⟨87825346528987515800914519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117100462038650021067886025 87825346528987515800914519)
          ·
            refine ⟨131738019793481273701371779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87825346528987515800914519 131738019793481273701371779)
            ·
              refine ⟨197607029690221910552057669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131738019793481273701371779 197607029690221910552057669)
              ·
                refine ⟨37051318066916608228510813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197607029690221910552057669 37051318066916608228510813)
                ·
                  refine ⟨13894244275093728085691555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37051318066916608228510813 13894244275093728085691555)
                  ·
                    refine ⟨20841366412640592128537333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13894244275093728085691555 20841366412640592128537333)
                    ·
                      refine ⟨1953878101185055512050375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20841366412640592128537333 1953878101185055512050375)
                      ·
                        rfl

theorem cell23_3805164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_3805164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805164 prefixEnd_3805164 := by exact prefixLift 3805164
  have htrace : WordTrace (prefixWord ++ tailWord_3805164) baseStart_3805164 baseEnd_3805164 := by
    simpa [prefixWord, tailWord_3805164, baseEnd_3805164] using wordTrace_append hprefix tailTrace_3805164
  have hstable : (prefixWord ++ tailWord_3805164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805164).length < 2 ^ (prefixWord ++ tailWord_3805164).sum := by decide
  have hdescent : baseEnd_3805164 < baseStart_3805164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805181 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_3805181 : Nat := 118140960795 + 3805181 * 2 ^ 59
def prefixEnd_3805181 : Nat := 4983230072969 + 3 ^ 40 * 3805181 * 2
def baseEnd_3805181 : Nat := 1953886830356181945537797

theorem tailTrace_3805181 : CollatzResearch.WordTrace tailWord_3805181 prefixEnd_3805181 1953886830356181945537797 := by
  unfold tailWord_3805181
  simp only [CollatzResearch.WordTrace]
  refine ⟨138786352827486585020863397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92524235218324390013908931 138786352827486585020863397)
  ·
    refine ⟨26022441155153734691411887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138786352827486585020863397 26022441155153734691411887)
    ·
      refine ⟨39033661732730602037117831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26022441155153734691411887 39033661732730602037117831)
      ·
        refine ⟨58550492599095903055676747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39033661732730602037117831 58550492599095903055676747)
        ·
          refine ⟨87825738898643854583515121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58550492599095903055676747 87825738898643854583515121)
          ·
            refine ⟨65869304173982890937636341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87825738898643854583515121 65869304173982890937636341)
            ·
              refine ⟨6175247266310896025403407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65869304173982890937636341 6175247266310896025403407)
              ·
                refine ⟨9262870899466344038105111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175247266310896025403407 9262870899466344038105111)
                ·
                  refine ⟨13894306349199516057157667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9262870899466344038105111 13894306349199516057157667)
                  ·
                    refine ⟨20841459523799274085736501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13894306349199516057157667 20841459523799274085736501)
                    ·
                      refine ⟨1953886830356181945537797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20841459523799274085736501 1953886830356181945537797)
                      ·
                        rfl

theorem cell23_3805181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_3805181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805181 prefixEnd_3805181 := by exact prefixLift 3805181
  have htrace : WordTrace (prefixWord ++ tailWord_3805181) baseStart_3805181 baseEnd_3805181 := by
    simpa [prefixWord, tailWord_3805181, baseEnd_3805181] using wordTrace_append hprefix tailTrace_3805181
  have hstable : (prefixWord ++ tailWord_3805181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805181).length < 2 ^ (prefixWord ++ tailWord_3805181).sum := by decide
  have hdescent : baseEnd_3805181 < baseStart_3805181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805262 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_3805262 : Nat := 118140960795 + 3805262 * 2 ^ 59
def prefixEnd_3805262 : Nat := 4983230072969 + 3 ^ 40 * 3805262 * 2
def baseEnd_3805262 : Nat := 1953928422289196128624925

theorem tailTrace_3805262 : CollatzResearch.WordTrace tailWord_3805262 prefixEnd_3805262 1953928422289196128624925 := by
  unfold tailWord_3805262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17348663392524141981820255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92526204760128757236374693 17348663392524141981820255)
  ·
    refine ⟨26022995088786212972730383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17348663392524141981820255 26022995088786212972730383)
    ·
      refine ⟨39034492633179319459095575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26022995088786212972730383 39034492633179319459095575)
      ·
        refine ⟨58551738949768979188643363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39034492633179319459095575 58551738949768979188643363)
        ·
          refine ⟨87827608424653468782965045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58551738949768979188643363 87827608424653468782965045)
          ·
            refine ⟨8233838289811262698402973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87827608424653468782965045 8233838289811262698402973)
            ·
              refine ⟨3087689358679223511901115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8233838289811262698402973 3087689358679223511901115)
              ·
                refine ⟨4631534038018835267851673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087689358679223511901115 4631534038018835267851673)
                ·
                  refine ⟨3473650528514126450888755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631534038018835267851673 3473650528514126450888755)
                  ·
                    refine ⟨5210475792771189676333133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473650528514126450888755 5210475792771189676333133)
                    ·
                      refine ⟨1953928422289196128624925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210475792771189676333133 1953928422289196128624925)
                      ·
                        rfl

theorem cell23_3805262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_3805262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805262 prefixEnd_3805262 := by exact prefixLift 3805262
  have htrace : WordTrace (prefixWord ++ tailWord_3805262) baseStart_3805262 baseEnd_3805262 := by
    simpa [prefixWord, tailWord_3805262, baseEnd_3805262] using wordTrace_append hprefix tailTrace_3805262
  have hstable : (prefixWord ++ tailWord_3805262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805262).length < 2 ^ (prefixWord ++ tailWord_3805262).sum := by decide
  have hdescent : baseEnd_3805262 < baseStart_3805262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805271 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_3805271 : Nat := 118140960795 + 3805271 * 2 ^ 59
def prefixEnd_3805271 : Nat := 4983230072969 + 3 ^ 40 * 3805271 * 2
def baseEnd_3805271 : Nat := 1953933043615086593412383

theorem tailTrace_3805271 : CollatzResearch.WordTrace tailWord_3805271 prefixEnd_3805271 1953933043615086593412383 := by
  unfold tailWord_3805271
  simp only [CollatzResearch.WordTrace]
  refine ⟨138789635397160530391639667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92526423598107020261093111 138789635397160530391639667)
  ·
    refine ⟨208184453095740795587459501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138789635397160530391639667 208184453095740795587459501)
    ·
      refine ⟨78069169910902798345297313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208184453095740795587459501 78069169910902798345297313)
      ·
        refine ⟨58551877433177098758972985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78069169910902798345297313 58551877433177098758972985)
        ·
          refine ⟨43913908074882824069229739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58551877433177098758972985 43913908074882824069229739)
          ·
            refine ⟨65870862112324236103844609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43913908074882824069229739 65870862112324236103844609)
            ·
              refine ⟨49403146584243177077883457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65870862112324236103844609 49403146584243177077883457)
              ·
                refine ⟨37052359938182382808412593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49403146584243177077883457 37052359938182382808412593)
                ·
                  refine ⟨27789269953636787106309445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37052359938182382808412593 27789269953636787106309445)
                  ·
                    refine ⟨5210488116306897582433021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27789269953636787106309445 5210488116306897582433021)
                    ·
                      refine ⟨1953933043615086593412383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210488116306897582433021 1953933043615086593412383)
                      ·
                        rfl

theorem cell23_3805271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_3805271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805271 prefixEnd_3805271 := by exact prefixLift 3805271
  have htrace : WordTrace (prefixWord ++ tailWord_3805271) baseStart_3805271 baseEnd_3805271 := by
    simpa [prefixWord, tailWord_3805271, baseEnd_3805271] using wordTrace_append hprefix tailTrace_3805271
  have hstable : (prefixWord ++ tailWord_3805271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805271).length < 2 ^ (prefixWord ++ tailWord_3805271).sum := by decide
  have hdescent : baseEnd_3805271 < baseStart_3805271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805285 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 4, 2, 2]
def baseStart_3805285 : Nat := 118140960795 + 3805285 * 2 ^ 59
def prefixEnd_3805285 : Nat := 4983230072969 + 3 ^ 40 * 3805285 * 2
def baseEnd_3805285 : Nat := 1953940232344249538637319

theorem tailTrace_3805285 : CollatzResearch.WordTrace tailWord_3805285 prefixEnd_3805285 1953940232344249538637319 := by
  unfold tailWord_3805285
  simp only [CollatzResearch.WordTrace]
  refine ⟨138790146019109810782649309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92526764012739873855099539 138790146019109810782649309)
  ·
    refine ⟨52046304757166179043493491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138790146019109810782649309 52046304757166179043493491)
    ·
      refine ⟨78069457135749268565240237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52046304757166179043493491 78069457135749268565240237)
      ·
        refine ⟨29276046425905975711965089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78069457135749268565240237 29276046425905975711965089)
        ·
          refine ⟨21957034819429481783973817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29276046425905975711965089 21957034819429481783973817)
          ·
            refine ⟨16467776114572111337980363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21957034819429481783973817 16467776114572111337980363)
            ·
              refine ⟨24701664171858167006970545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16467776114572111337980363 24701664171858167006970545)
              ·
                refine ⟨18526248128893625255227909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24701664171858167006970545 18526248128893625255227909)
                ·
                  refine ⟨3473671524167554735355233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18526248128893625255227909 3473671524167554735355233)
                  ·
                    refine ⟨2605253643125666051516425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3473671524167554735355233 2605253643125666051516425)
                    ·
                      refine ⟨1953940232344249538637319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605253643125666051516425 1953940232344249538637319)
                      ·
                        rfl

theorem cell23_3805285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_3805285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805285 prefixEnd_3805285 := by exact prefixLift 3805285
  have htrace : WordTrace (prefixWord ++ tailWord_3805285) baseStart_3805285 baseEnd_3805285 := by
    simpa [prefixWord, tailWord_3805285, baseEnd_3805285] using wordTrace_append hprefix tailTrace_3805285
  have hstable : (prefixWord ++ tailWord_3805285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805285).length < 2 ^ (prefixWord ++ tailWord_3805285).sum := by decide
  have hdescent : baseEnd_3805285 < baseStart_3805285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805302 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3805302 : Nat := 118140960795 + 3805302 * 2 ^ 59
def prefixEnd_3805302 : Nat := 4983230072969 + 3 ^ 40 * 3805302 * 2
def baseEnd_3805302 : Nat := 1953948961515375972124741

theorem tailTrace_3805302 : CollatzResearch.WordTrace tailWord_3805302 prefixEnd_3805302 1953948961515375972124741 := by
  unfold tailWord_3805302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674422878753013917876135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92527177373365481790678773 8674422878753013917876135)
  ·
    refine ⟨13011634318129520876814203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674422878753013917876135 13011634318129520876814203)
    ·
      refine ⟨19517451477194281315221305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13011634318129520876814203 19517451477194281315221305)
      ·
        refine ⟨14638088607895710986415979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19517451477194281315221305 14638088607895710986415979)
        ·
          refine ⟨21957132911843566479623969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14638088607895710986415979 21957132911843566479623969)
          ·
            refine ⟨16467849683882674859717977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21957132911843566479623969 16467849683882674859717977)
            ·
              refine ⟨12350887262912006144788483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16467849683882674859717977 12350887262912006144788483)
              ·
                refine ⟨18526330894368009217182725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12350887262912006144788483 18526330894368009217182725)
                ·
                  refine ⟨3473687042694001728221761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18526330894368009217182725 3473687042694001728221761)
                  ·
                    refine ⟨2605265282020501296166321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3473687042694001728221761 2605265282020501296166321)
                    ·
                      refine ⟨1953948961515375972124741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605265282020501296166321 1953948961515375972124741)
                      ·
                        rfl

theorem cell23_3805302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3805302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805302 prefixEnd_3805302 := by exact prefixLift 3805302
  have htrace : WordTrace (prefixWord ++ tailWord_3805302) baseStart_3805302 baseEnd_3805302 := by
    simpa [prefixWord, tailWord_3805302, baseEnd_3805302] using wordTrace_append hprefix tailTrace_3805302
  have hstable : (prefixWord ++ tailWord_3805302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805302).length < 2 ^ (prefixWord ++ tailWord_3805302).sum := by decide
  have hdescent : baseEnd_3805302 < baseStart_3805302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805308 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 7]
def baseStart_3805308 : Nat := 118140960795 + 3805308 * 2 ^ 59
def prefixEnd_3805308 : Nat := 4983230072969 + 3 ^ 40 * 3805308 * 2
def baseEnd_3805308 : Nat := 217105782488811438738857

theorem tailTrace_3805308 : CollatzResearch.WordTrace tailWord_3805308 prefixEnd_3805308 217105782488811438738857 := by
  unfold tailWord_3805308
  simp only [CollatzResearch.WordTrace]
  refine ⟨69395492449013242855368289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92527323265350990473824385 69395492449013242855368289)
  ·
    refine ⟨52046619336759932141526217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69395492449013242855368289 52046619336759932141526217)
    ·
      refine ⟨39034964502569949106144663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52046619336759932141526217 39034964502569949106144663)
      ·
        refine ⟨58552446753854923659216995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39034964502569949106144663 58552446753854923659216995)
        ·
          refine ⟨87828670130782385488825493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58552446753854923659216995 87828670130782385488825493)
          ·
            refine ⟨4116968912380424319788695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87828670130782385488825493 4116968912380424319788695)
            ·
              refine ⟨6175453368570636479683043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116968912380424319788695 6175453368570636479683043)
              ·
                refine ⟨9263180052855954719524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175453368570636479683043 9263180052855954719524565)
                ·
                  refine ⟨217105782488811438738857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9263180052855954719524565 217105782488811438738857)
                  ·
                    rfl

theorem cell23_3805308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_3805308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805308 prefixEnd_3805308 := by exact prefixLift 3805308
  have htrace : WordTrace (prefixWord ++ tailWord_3805308) baseStart_3805308 baseEnd_3805308 := by
    simpa [prefixWord, tailWord_3805308, baseEnd_3805308] using wordTrace_append hprefix tailTrace_3805308
  have hstable : (prefixWord ++ tailWord_3805308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805308).length < 2 ^ (prefixWord ++ tailWord_3805308).sum := by decide
  have hdescent : baseEnd_3805308 < baseStart_3805308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805321 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_3805321 : Nat := 118140960795 + 3805321 * 2 ^ 59
def prefixEnd_3805321 : Nat := 4983230072969 + 3 ^ 40 * 3805321 * 2
def baseEnd_3805321 : Nat := 651319572549270465929051

theorem tailTrace_3805321 : CollatzResearch.WordTrace tailWord_3805321 prefixEnd_3805321 651319572549270465929051 := by
  unfold tailWord_3805321
  simp only [CollatzResearch.WordTrace]
  refine ⟨138791459046979388930959817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92527639364652925953973211 138791459046979388930959817)
  ·
    refine ⟨104093594285234541698219863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138791459046979388930959817 104093594285234541698219863)
    ·
      refine ⟨156140391427851812547329795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104093594285234541698219863 156140391427851812547329795)
      ·
        refine ⟨234210587141777718820994693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156140391427851812547329795 234210587141777718820994693)
        ·
          refine ⟨43914485089083322278936505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234210587141777718820994693 43914485089083322278936505)
          ·
            refine ⟨32935863816812491709202379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43914485089083322278936505 32935863816812491709202379)
            ·
              refine ⟨49403795725218737563803569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32935863816812491709202379 49403795725218737563803569)
              ·
                refine ⟨37052846793914053172852677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49403795725218737563803569 37052846793914053172852677)
                ·
                  refine ⟨6947408773858884969909877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37052846793914053172852677 6947408773858884969909877)
                  ·
                    refine ⟨651319572549270465929051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6947408773858884969909877 651319572549270465929051)
                    ·
                      rfl

theorem cell23_3805321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_3805321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805321 prefixEnd_3805321 := by exact prefixLift 3805321
  have htrace : WordTrace (prefixWord ++ tailWord_3805321) baseStart_3805321 baseEnd_3805321 := by
    simpa [prefixWord, tailWord_3805321, baseEnd_3805321] using wordTrace_append hprefix tailTrace_3805321
  have hstable : (prefixWord ++ tailWord_3805321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805321).length < 2 ^ (prefixWord ++ tailWord_3805321).sum := by decide
  have hdescent : baseEnd_3805321 < baseStart_3805321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805368 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 3, 4]
def baseStart_3805368 : Nat := 118140960795 + 3805368 * 2 ^ 59
def prefixEnd_3805368 : Nat := 4983230072969 + 3 ^ 40 * 3805368 * 2
def baseEnd_3805368 : Nat := 651327617079524237966479

theorem tailTrace_3805368 : CollatzResearch.WordTrace tailWord_3805368 prefixEnd_3805368 651327617079524237966479 := by
  unfold tailWord_3805368
  simp only [CollatzResearch.WordTrace]
  refine ⟨69396586638904557978960379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92528782185206077305280505 69396586638904557978960379)
  ·
    refine ⟨104094879958356836968440569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69396586638904557978960379 104094879958356836968440569)
    ·
      refine ⟨78071159968767627726330427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104094879958356836968440569 78071159968767627726330427)
      ·
        refine ⟨117106739953151441589495641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78071159968767627726330427 117106739953151441589495641)
        ·
          refine ⟨87830054964863581192121731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117106739953151441589495641 87830054964863581192121731)
          ·
            refine ⟨131745082447295371788182597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87830054964863581192121731 131745082447295371788182597)
            ·
              refine ⟨24702202958867882210284237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131745082447295371788182597 24702202958867882210284237)
              ·
                refine ⟨9263326109575455828856589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24702202958867882210284237 9263326109575455828856589)
                ·
                  refine ⟨3473747291090795935821221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9263326109575455828856589 3473747291090795935821221)
                  ·
                    refine ⟨651327617079524237966479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3473747291090795935821221 651327617079524237966479)
                    ·
                      rfl

theorem cell23_3805368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_3805368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805368 prefixEnd_3805368 := by exact prefixLift 3805368
  have htrace : WordTrace (prefixWord ++ tailWord_3805368) baseStart_3805368 baseEnd_3805368 := by
    simpa [prefixWord, tailWord_3805368, baseEnd_3805368] using wordTrace_append hprefix tailTrace_3805368
  have hstable : (prefixWord ++ tailWord_3805368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805368).length < 2 ^ (prefixWord ++ tailWord_3805368).sum := by decide
  have hdescent : baseEnd_3805368 < baseStart_3805368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805415 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 6]
def baseStart_3805415 : Nat := 118140960795 + 3805415 * 2 ^ 59
def prefixEnd_3805415 : Nat := 4983230072969 + 3 ^ 40 * 3805415 * 2
def baseEnd_3805415 : Nat := 217111887203259336667969

theorem tailTrace_3805415 : CollatzResearch.WordTrace tailWord_3805415 prefixEnd_3805415 217111887203259336667969 := by
  unfold tailWord_3805415
  simp only [CollatzResearch.WordTrace]
  refine ⟨138794887508638842984881699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92529925005759228656587799 138794887508638842984881699)
  ·
    refine ⟨208192331262958264477322549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138794887508638842984881699 208192331262958264477322549)
    ·
      refine ⟨19518031055902337294748989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208192331262958264477322549 19518031055902337294748989)
      ·
        refine ⟨7319261645963376485530871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19518031055902337294748989 7319261645963376485530871)
        ·
          refine ⟨10978892468945064728296307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319261645963376485530871 10978892468945064728296307)
          ·
            refine ⟨16468338703417597092444461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978892468945064728296307 16468338703417597092444461)
            ·
              refine ⟨6175627013781598909666673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16468338703417597092444461 6175627013781598909666673)
              ·
                refine ⟨4631720260336199182250005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6175627013781598909666673 4631720260336199182250005)
                ·
                  refine ⟨217111887203259336667969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4631720260336199182250005 217111887203259336667969)
                  ·
                    rfl

theorem cell23_3805415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 6].length) (baseStart_3805415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805415 prefixEnd_3805415 := by exact prefixLift 3805415
  have htrace : WordTrace (prefixWord ++ tailWord_3805415) baseStart_3805415 baseEnd_3805415 := by
    simpa [prefixWord, tailWord_3805415, baseEnd_3805415] using wordTrace_append hprefix tailTrace_3805415
  have hstable : (prefixWord ++ tailWord_3805415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805415).length < 2 ^ (prefixWord ++ tailWord_3805415).sum := by decide
  have hdescent : baseEnd_3805415 < baseStart_3805415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805425 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_3805425 : Nat := 118140960795 + 3805425 * 2 ^ 59
def prefixEnd_3805425 : Nat := 4983230072969 + 3 ^ 40 * 3805425 * 2
def baseEnd_3805425 : Nat := 1954012119635878990886675

theorem tailTrace_3805425 : CollatzResearch.WordTrace tailWord_3805425 prefixEnd_3805425 1954012119635878990886675 := by
  unfold tailWord_3805425
  simp only [CollatzResearch.WordTrace]
  refine ⟨138795252238602614692745729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92530168159068409795163819 138795252238602614692745729)
  ·
    refine ⟨104096439178951961019559297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138795252238602614692745729 104096439178951961019559297)
    ·
      refine ⟨78072329384213970764669473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104096439178951961019559297 78072329384213970764669473)
      ·
        refine ⟨58554247038160478073502105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78072329384213970764669473 58554247038160478073502105)
        ·
          refine ⟨43915685278620358555126579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58554247038160478073502105 43915685278620358555126579)
          ·
            refine ⟨65873527917930537832689869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43915685278620358555126579 65873527917930537832689869)
            ·
              refine ⟨24702572969223951687258701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65873527917930537832689869 24702572969223951687258701)
              ·
                refine ⟨9263464863458981882722013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24702572969223951687258701 9263464863458981882722013)
                ·
                  refine ⟨3473799323797118206020755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9263464863458981882722013 3473799323797118206020755)
                  ·
                    refine ⟨5210698985695677309031133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473799323797118206020755 5210698985695677309031133)
                    ·
                      refine ⟨1954012119635878990886675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210698985695677309031133 1954012119635878990886675)
                      ·
                        rfl

theorem cell23_3805425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_3805425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805425 prefixEnd_3805425 := by exact prefixLift 3805425
  have htrace : WordTrace (prefixWord ++ tailWord_3805425) baseStart_3805425 baseEnd_3805425 := by
    simpa [prefixWord, tailWord_3805425, baseEnd_3805425] using wordTrace_append hprefix tailTrace_3805425
  have hstable : (prefixWord ++ tailWord_3805425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805425).length < 2 ^ (prefixWord ++ tailWord_3805425).sum := by decide
  have hdescent : baseEnd_3805425 < baseStart_3805425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805469 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3805469 : Nat := 118140960795 + 3805469 * 2 ^ 59
def prefixEnd_3805469 : Nat := 4983230072969 + 3 ^ 40 * 3805469 * 2
def baseEnd_3805469 : Nat := 1954034712784676818736473

theorem tailTrace_3805469 : CollatzResearch.WordTrace tailWord_3805469 prefixEnd_3805469 1954034712784676818736473 := by
  unfold tailWord_3805469
  simp only [CollatzResearch.WordTrace]
  refine ⟨138796857050443210207347461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92531238033628806804898307 138796857050443210207347461)
  ·
    refine ⟨26024410696958101913877649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138796857050443210207347461 26024410696958101913877649)
    ·
      refine ⟨19518308022718576435408237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26024410696958101913877649 19518308022718576435408237)
      ·
        refine ⟨7319365508519466163278089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19518308022718576435408237 7319365508519466163278089)
        ·
          refine ⟨5489524131389599622458567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7319365508519466163278089 5489524131389599622458567)
          ·
            refine ⟨8234286197084399433687851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489524131389599622458567 8234286197084399433687851)
            ·
              refine ⟨12351429295626599150531777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234286197084399433687851 12351429295626599150531777)
              ·
                refine ⟨9263571971719949362898833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12351429295626599150531777 9263571971719949362898833)
                ·
                  refine ⟨6947678978789962022174125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9263571971719949362898833 6947678978789962022174125)
                  ·
                    refine ⟨2605379617046235758315297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6947678978789962022174125 2605379617046235758315297)
                    ·
                      refine ⟨1954034712784676818736473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605379617046235758315297 1954034712784676818736473)
                      ·
                        rfl

theorem cell23_3805469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3805469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805469 prefixEnd_3805469 := by exact prefixLift 3805469
  have htrace : WordTrace (prefixWord ++ tailWord_3805469) baseStart_3805469 baseEnd_3805469 := by
    simpa [prefixWord, tailWord_3805469, baseEnd_3805469] using wordTrace_append hprefix tailTrace_3805469
  have hstable : (prefixWord ++ tailWord_3805469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805469).length < 2 ^ (prefixWord ++ tailWord_3805469).sum := by decide
  have hdescent : baseEnd_3805469 < baseStart_3805469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805475 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 2, 4]
def baseStart_3805475 : Nat := 118140960795 + 3805475 * 2 ^ 59
def prefixEnd_3805475 : Nat := 4983230072969 + 3 ^ 40 * 3805475 * 2
def baseEnd_3805475 : Nat := 651345931222867931753815

theorem tailTrace_3805475 : CollatzResearch.WordTrace tailWord_3805475 prefixEnd_3805475 651345931222867931753815 := by
  unfold tailWord_3805475
  simp only [CollatzResearch.WordTrace]
  refine ⟨138797075888421473232065879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92531383925614315488043919 138797075888421473232065879)
  ·
    refine ⟨208195613832632209848098819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138797075888421473232065879 208195613832632209848098819)
    ·
      refine ⟨312293420748948314772148229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208195613832632209848098819 312293420748948314772148229)
      ·
        refine ⟨58555016390427809019777793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312293420748948314772148229 58555016390427809019777793)
        ·
          refine ⟨43916262292820856764833345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58555016390427809019777793 43916262292820856764833345)
          ·
            refine ⟨32937196719615642573625009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43916262292820856764833345 32937196719615642573625009)
            ·
              refine ⟨24702897539711731930218757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32937196719615642573625009 24702897539711731930218757)
              ·
                refine ⟨4631793288695949736916017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24702897539711731930218757 4631793288695949736916017)
                ·
                  refine ⟨3473844966521962302687013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631793288695949736916017 3473844966521962302687013)
                  ·
                    refine ⟨651345931222867931753815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3473844966521962302687013 651345931222867931753815)
                    ·
                      rfl

theorem cell23_3805475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 4].length) (baseStart_3805475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805475 prefixEnd_3805475 := by exact prefixLift 3805475
  have htrace : WordTrace (prefixWord ++ tailWord_3805475) baseStart_3805475 baseEnd_3805475 := by
    simpa [prefixWord, tailWord_3805475, baseEnd_3805475] using wordTrace_append hprefix tailTrace_3805475
  have hstable : (prefixWord ++ tailWord_3805475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805475).length < 2 ^ (prefixWord ++ tailWord_3805475).sum := by decide
  have hdescent : baseEnd_3805475 < baseStart_3805475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805476 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_3805476 : Nat := 118140960795 + 3805476 * 2 ^ 59
def prefixEnd_3805476 : Nat := 4983230072969 + 3 ^ 40 * 3805476 * 2
def baseEnd_3805476 : Nat := 1954038307149258291348941

theorem tailTrace_3805476 : CollatzResearch.WordTrace tailWord_3805476 prefixEnd_3805476 1954038307149258291348941 := by
  unfold tailWord_3805476
  simp only [CollatzResearch.WordTrace]
  refine ⟨69398556180708925201426141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92531408240945233601901521 69398556180708925201426141)
  ·
    refine ⟨26024458567765846950534803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69398556180708925201426141 26024458567765846950534803)
    ·
      refine ⟨39036687851648770425802205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26024458567765846950534803 39036687851648770425802205)
      ·
        refine ⟨14638757944368288909675827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39036687851648770425802205 14638757944368288909675827)
        ·
          refine ⟨21958136916552433364513741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14638757944368288909675827 21958136916552433364513741)
          ·
            refine ⟨8234301343707162511692653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21958136916552433364513741 8234301343707162511692653)
            ·
              refine ⟨3087863003890185941884745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8234301343707162511692653 3087863003890185941884745)
              ·
                refine ⟨2315897252917639456413559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087863003890185941884745 2315897252917639456413559)
                ·
                  refine ⟨3473845879376459184620339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315897252917639456413559 3473845879376459184620339)
                  ·
                    refine ⟨5210768819064688776930509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473845879376459184620339 5210768819064688776930509)
                    ·
                      refine ⟨1954038307149258291348941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210768819064688776930509 1954038307149258291348941)
                      ·
                        rfl

theorem cell23_3805476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_3805476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805476 prefixEnd_3805476 := by exact prefixLift 3805476
  have htrace : WordTrace (prefixWord ++ tailWord_3805476) baseStart_3805476 baseEnd_3805476 := by
    simpa [prefixWord, tailWord_3805476, baseEnd_3805476] using wordTrace_append hprefix tailTrace_3805476
  have hstable : (prefixWord ++ tailWord_3805476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805476).length < 2 ^ (prefixWord ++ tailWord_3805476).sum := by decide
  have hdescent : baseEnd_3805476 < baseStart_3805476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805502 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3805502 : Nat := 118140960795 + 3805502 * 2 ^ 59
def prefixEnd_3805502 : Nat := 4983230072969 + 3 ^ 40 * 3805502 * 2
def baseEnd_3805502 : Nat := 1954051657646275189623821

theorem tailTrace_3805502 : CollatzResearch.WordTrace tailWord_3805502 prefixEnd_3805502 1954051657646275189623821 := by
  unfold tailWord_3805502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17349757582415457105412345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92532040439549104562199173 17349757582415457105412345)
  ·
    refine ⟨13012318186811592829059259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17349757582415457105412345 13012318186811592829059259)
    ·
      refine ⟨19518477280217389243588889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13012318186811592829059259 19518477280217389243588889)
      ·
        refine ⟨14638857960163041932691667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19518477280217389243588889 14638857960163041932691667)
        ·
          refine ⟨21958286940244562899037501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14638857960163041932691667 21958286940244562899037501)
          ·
            refine ⟨8234357602591711087139063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21958286940244562899037501 8234357602591711087139063)
            ·
              refine ⟨12351536403887566630708595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234357602591711087139063 12351536403887566630708595)
              ·
                refine ⟨18527304605831349946062893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12351536403887566630708595 18527304605831349946062893)
                ·
                  refine ⟨6947739227186756229773585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18527304605831349946062893 6947739227186756229773585)
                  ·
                    refine ⟨5210804420390067172330189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6947739227186756229773585 5210804420390067172330189)
                    ·
                      refine ⟨1954051657646275189623821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210804420390067172330189 1954051657646275189623821)
                      ·
                        rfl

theorem cell23_3805502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3805502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805502 prefixEnd_3805502 := by exact prefixLift 3805502
  have htrace : WordTrace (prefixWord ++ tailWord_3805502) baseStart_3805502 baseEnd_3805502 := by
    simpa [prefixWord, tailWord_3805502, baseEnd_3805502] using wordTrace_append hprefix tailTrace_3805502
  have hstable : (prefixWord ++ tailWord_3805502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805502).length < 2 ^ (prefixWord ++ tailWord_3805502).sum := by decide
  have hdescent : baseEnd_3805502 < baseStart_3805502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805515 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 3]
def baseStart_3805515 : Nat := 118140960795 + 3805515 * 2 ^ 59
def prefixEnd_3805515 : Nat := 4983230072969 + 3 ^ 40 * 3805515 * 2
def baseEnd_3805515 : Nat := 1954058332894783638761261

theorem tailTrace_3805515 : CollatzResearch.WordTrace tailWord_3805515 prefixEnd_3805515 1954058332894783638761261 := by
  unfold tailWord_3805515
  simp only [CollatzResearch.WordTrace]
  refine ⟨138798534808276560063521999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92532356538851040042347999 138798534808276560063521999)
  ·
    refine ⟨208197802212414840095282999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138798534808276560063521999 208197802212414840095282999)
    ·
      refine ⟨312296703318622260142924499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208197802212414840095282999 312296703318622260142924499)
      ·
        refine ⟨468445054977933390214386749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312296703318622260142924499 468445054977933390214386749)
        ·
          refine ⟨175666895616725021330395031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468445054977933390214386749 175666895616725021330395031)
          ·
            refine ⟨263500343425087531995592547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175666895616725021330395031 263500343425087531995592547)
            ·
              refine ⟨395250515137631297993388821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263500343425087531995592547 395250515137631297993388821)
              ·
                refine ⟨18527367897076467093440101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 395250515137631297993388821 18527367897076467093440101)
                ·
                  refine ⟨3473881480701837580020019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18527367897076467093440101 3473881480701837580020019)
                  ·
                    refine ⟨5210822221052756370030029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473881480701837580020019 5210822221052756370030029)
                    ·
                      refine ⟨1954058332894783638761261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210822221052756370030029 1954058332894783638761261)
                      ·
                        rfl

theorem cell23_3805515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 3].length) (baseStart_3805515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805515 prefixEnd_3805515 := by exact prefixLift 3805515
  have htrace : WordTrace (prefixWord ++ tailWord_3805515) baseStart_3805515 baseEnd_3805515 := by
    simpa [prefixWord, tailWord_3805515, baseEnd_3805515] using wordTrace_append hprefix tailTrace_3805515
  have hstable : (prefixWord ++ tailWord_3805515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805515).length < 2 ^ (prefixWord ++ tailWord_3805515).sum := by decide
  have hdescent : baseEnd_3805515 < baseStart_3805515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805555 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 5, 4, 2]
def baseStart_3805555 : Nat := 118140960795 + 3805555 * 2 ^ 59
def prefixEnd_3805555 : Nat := 4983230072969 + 3 ^ 40 * 3805555 * 2
def baseEnd_3805555 : Nat := 1954078872120963482261077

theorem tailTrace_3805555 : CollatzResearch.WordTrace tailWord_3805555 prefixEnd_3805555 1954078872120963482261077 := by
  unfold tailWord_3805555
  simp only [CollatzResearch.WordTrace]
  refine ⟨138799993728131646894978119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92533329152087764596652079 138799993728131646894978119)
  ·
    refine ⟨208199990592197470342467179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138799993728131646894978119 208199990592197470342467179)
    ·
      refine ⟨312299985888296205513700769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208199990592197470342467179 312299985888296205513700769)
      ·
        refine ⟨234224989416222154135275577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312299985888296205513700769 234224989416222154135275577)
        ·
          refine ⟨175668742062166615601456683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234224989416222154135275577 175668742062166615601456683)
          ·
            refine ⟨263503113093249923402185025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175668742062166615601456683 263503113093249923402185025)
            ·
              refine ⟨197627334819937442551638769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263503113093249923402185025 197627334819937442551638769)
              ·
                refine ⟨148220501114953081913729077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197627334819937442551638769 148220501114953081913729077)
                ·
                  refine ⟨13895671979526851429412101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148220501114953081913729077 13895671979526851429412101)
                  ·
                    refine ⟨2605438496161284643014769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13895671979526851429412101 2605438496161284643014769)
                    ·
                      refine ⟨1954078872120963482261077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605438496161284643014769 1954078872120963482261077)
                      ·
                        rfl

theorem cell23_3805555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4, 2].length) (baseStart_3805555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805555 prefixEnd_3805555 := by exact prefixLift 3805555
  have htrace : WordTrace (prefixWord ++ tailWord_3805555) baseStart_3805555 baseEnd_3805555 := by
    simpa [prefixWord, tailWord_3805555, baseEnd_3805555] using wordTrace_append hprefix tailTrace_3805555
  have hstable : (prefixWord ++ tailWord_3805555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805555).length < 2 ^ (prefixWord ++ tailWord_3805555).sum := by decide
  have hdescent : baseEnd_3805555 < baseStart_3805555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805570 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3805570 : Nat := 118140960795 + 3805570 * 2 ^ 59
def prefixEnd_3805570 : Nat := 4983230072969 + 3 ^ 40 * 3805570 * 2
def baseEnd_3805570 : Nat := 1954086574330780923573509

theorem tailTrace_3805570 : CollatzResearch.WordTrace tailWord_3805570 prefixEnd_3805570 1954086574330780923573509 := by
  unfold tailWord_3805570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34700135205769326114193541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92533693882051536304516109 34700135205769326114193541)
  ·
    refine ⟨6506275351081748646411289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34700135205769326114193541 6506275351081748646411289)
    ·
      refine ⟨4879706513311311484808467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6506275351081748646411289 4879706513311311484808467)
      ·
        refine ⟨7319559769966967227212701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879706513311311484808467 7319559769966967227212701)
        ·
          refine ⟨2744834913737612710204763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7319559769966967227212701 2744834913737612710204763)
          ·
            refine ⟨4117252370606419065307145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744834913737612710204763 4117252370606419065307145)
            ·
              refine ⟨3087939277954814298980359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117252370606419065307145 3087939277954814298980359)
              ·
                refine ⟨4631908916932221448470539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087939277954814298980359 4631908916932221448470539)
                ·
                  refine ⟨6947863375398332172705809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631908916932221448470539 6947863375398332172705809)
                  ·
                    refine ⟨5210897531548749129529357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6947863375398332172705809 5210897531548749129529357)
                    ·
                      refine ⟨1954086574330780923573509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210897531548749129529357 1954086574330780923573509)
                      ·
                        rfl

theorem cell23_3805570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3805570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805570 prefixEnd_3805570 := by exact prefixLift 3805570
  have htrace : WordTrace (prefixWord ++ tailWord_3805570) baseStart_3805570 baseEnd_3805570 := by
    simpa [prefixWord, tailWord_3805570, baseEnd_3805570] using wordTrace_append hprefix tailTrace_3805570
  have hstable : (prefixWord ++ tailWord_3805570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805570).length < 2 ^ (prefixWord ++ tailWord_3805570).sum := by decide
  have hdescent : baseEnd_3805570 < baseStart_3805570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805572 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_3805572 : Nat := 118140960795 + 3805572 * 2 ^ 59
def prefixEnd_3805572 : Nat := 4983230072969 + 3 ^ 40 * 3805572 * 2
def baseEnd_3805572 : Nat := 1954087601292089915748499

theorem tailTrace_3805572 : CollatzResearch.WordTrace tailWord_3805572 prefixEnd_3805572 1954087601292089915748499 := by
  unfold tailWord_3805572
  simp only [CollatzResearch.WordTrace]
  refine ⟨69400306884535029399173485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92533742512713372532231313 69400306884535029399173485)
  ·
    refine ⟨26025115081700636024690057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69400306884535029399173485 26025115081700636024690057)
    ·
      refine ⟨19518836311275477018517543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26025115081700636024690057 19518836311275477018517543)
      ·
        refine ⟨29278254466913215527776315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518836311275477018517543 29278254466913215527776315)
        ·
          refine ⟨43917381700369823291664473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29278254466913215527776315 43917381700369823291664473)
          ·
            refine ⟨32938036275277367468748355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43917381700369823291664473 32938036275277367468748355)
            ·
              refine ⟨49407054412916051203122533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32938036275277367468748355 49407054412916051203122533)
              ·
                refine ⟨9263822702421759600585475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49407054412916051203122533 9263822702421759600585475)
                ·
                  refine ⟨13895734053632639400878213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263822702421759600585475 13895734053632639400878213)
                  ·
                    refine ⟨2605450135056119887664665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13895734053632639400878213 2605450135056119887664665)
                    ·
                      refine ⟨1954087601292089915748499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605450135056119887664665 1954087601292089915748499)
                      ·
                        rfl

theorem cell23_3805572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_3805572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805572 prefixEnd_3805572 := by exact prefixLift 3805572
  have htrace : WordTrace (prefixWord ++ tailWord_3805572) baseStart_3805572 baseEnd_3805572 := by
    simpa [prefixWord, tailWord_3805572, baseEnd_3805572] using wordTrace_append hprefix tailTrace_3805572
  have hstable : (prefixWord ++ tailWord_3805572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805572).length < 2 ^ (prefixWord ++ tailWord_3805572).sum := by decide
  have hdescent : baseEnd_3805572 < baseStart_3805572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805605 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_3805605 : Nat := 118140960795 + 3805605 * 2 ^ 59
def prefixEnd_3805605 : Nat := 4983230072969 + 3 ^ 40 * 3805605 * 2
def baseEnd_3805605 : Nat := 1954104546153688286635847

theorem tailTrace_3805605 : CollatzResearch.WordTrace tailWord_3805605 prefixEnd_3805605 1954104546153688286635847 := by
  unfold tailWord_3805605
  simp only [CollatzResearch.WordTrace]
  refine ⟨138801817377950505434298269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92534544918633670289532179 138801817377950505434298269)
  ·
    refine ⟨52050681516731439537861851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138801817377950505434298269 52050681516731439537861851)
    ·
      refine ⟨78076022275097159306792777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52050681516731439537861851 78076022275097159306792777)
      ·
        refine ⟨58557016706322869480094583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78076022275097159306792777 58557016706322869480094583)
        ·
          refine ⟨87835525059484304220141875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58557016706322869480094583 87835525059484304220141875)
          ·
            refine ⟨131753287589226456330212813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87835525059484304220141875 131753287589226456330212813)
            ·
              refine ⟨49407482845959921123829805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131753287589226456330212813 49407482845959921123829805)
              ·
                refine ⟨18527806067234970421436177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49407482845959921123829805 18527806067234970421436177)
                ·
                  refine ⟨13895854550426227816077133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18527806067234970421436177 13895854550426227816077133)
                  ·
                    refine ⟨5210945456409835431028925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13895854550426227816077133 5210945456409835431028925)
                    ·
                      refine ⟨1954104546153688286635847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5210945456409835431028925 1954104546153688286635847)
                      ·
                        rfl

theorem cell23_3805605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_3805605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805605 prefixEnd_3805605 := by exact prefixLift 3805605
  have htrace : WordTrace (prefixWord ++ tailWord_3805605) baseStart_3805605 baseEnd_3805605 := by
    simpa [prefixWord, tailWord_3805605, baseEnd_3805605] using wordTrace_append hprefix tailTrace_3805605
  have hstable : (prefixWord ++ tailWord_3805605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805605).length < 2 ^ (prefixWord ++ tailWord_3805605).sum := by decide
  have hdescent : baseEnd_3805605 < baseStart_3805605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805610 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3805610 : Nat := 118140960795 + 3805610 * 2 ^ 59
def prefixEnd_3805610 : Nat := 4983230072969 + 3 ^ 40 * 3805610 * 2
def baseEnd_3805610 : Nat := 1954107113556960767073325

theorem tailTrace_3805610 : CollatzResearch.WordTrace tailWord_3805610 prefixEnd_3805610 1954107113556960767073325 := by
  unfold tailWord_3805610
  simp only [CollatzResearch.WordTrace]
  refine ⟨34700499935733097822057571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92534666495288260858820189 34700499935733097822057571)
  ·
    refine ⟨52050749903599646733086357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34700499935733097822057571 52050749903599646733086357)
    ·
      refine ⟨2439878901731233440613423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52050749903599646733086357 2439878901731233440613423)
      ·
        refine ⟨3659818352596850160920135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439878901731233440613423 3659818352596850160920135)
        ·
          refine ⟨5489727528895275241380203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659818352596850160920135 5489727528895275241380203)
          ·
            refine ⟨8234591293342912862070305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489727528895275241380203 8234591293342912862070305)
            ·
              refine ⟨6175943470007184646552729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8234591293342912862070305 6175943470007184646552729)
              ·
                refine ⟨4631957602505388484914547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6175943470007184646552729 4631957602505388484914547)
                ·
                  refine ⟨6947936403758082727371821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631957602505388484914547 6947936403758082727371821)
                  ·
                    refine ⟨2605476151409281022764433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6947936403758082727371821 2605476151409281022764433)
                    ·
                      refine ⟨1954107113556960767073325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605476151409281022764433 1954107113556960767073325)
                      ·
                        rfl

theorem cell23_3805610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3805610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805610 prefixEnd_3805610 := by exact prefixLift 3805610
  have htrace : WordTrace (prefixWord ++ tailWord_3805610) baseStart_3805610 baseEnd_3805610 := by
    simpa [prefixWord, tailWord_3805610, baseEnd_3805610] using wordTrace_append hprefix tailTrace_3805610
  have hstable : (prefixWord ++ tailWord_3805610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805610).length < 2 ^ (prefixWord ++ tailWord_3805610).sum := by decide
  have hdescent : baseEnd_3805610 < baseStart_3805610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805625 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_3805625 : Nat := 118140960795 + 3805625 * 2 ^ 59
def prefixEnd_3805625 : Nat := 4983230072969 + 3 ^ 40 * 3805625 * 2
def baseEnd_3805625 : Nat := 651371605255592736128585

theorem tailTrace_3805625 : CollatzResearch.WordTrace tailWord_3805625 prefixEnd_3805625 651371605255592736128585 := by
  unfold tailWord_3805625
  simp only [CollatzResearch.WordTrace]
  refine ⟨138802546837878048850026329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92535031225252032566684219 138802546837878048850026329)
  ·
    refine ⟨104101910128408536637519747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138802546837878048850026329 104101910128408536637519747)
    ·
      refine ⟨156152865192612804956279621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104101910128408536637519747 156152865192612804956279621)
      ·
        refine ⟨29278662223614900929302429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156152865192612804956279621 29278662223614900929302429)
        ·
          refine ⟨10979498333855587848488411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29278662223614900929302429 10979498333855587848488411)
          ·
            refine ⟨16469247500783381772732617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979498333855587848488411 16469247500783381772732617)
            ·
              refine ⟨12351935625587536329549463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16469247500783381772732617 12351935625587536329549463)
              ·
                refine ⟨18527903438381304494324195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12351935625587536329549463 18527903438381304494324195)
                ·
                  refine ⟨27791855157571956741486293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527903438381304494324195 27791855157571956741486293)
                  ·
                    refine ⟨651371605255592736128585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27791855157571956741486293 651371605255592736128585)
                    ·
                      rfl

theorem cell23_3805625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_3805625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805625 prefixEnd_3805625 := by exact prefixLift 3805625
  have htrace : WordTrace (prefixWord ++ tailWord_3805625) baseStart_3805625 baseEnd_3805625 := by
    simpa [prefixWord, tailWord_3805625, baseEnd_3805625] using wordTrace_append hprefix tailTrace_3805625
  have hstable : (prefixWord ++ tailWord_3805625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805625).length < 2 ^ (prefixWord ++ tailWord_3805625).sum := by decide
  have hdescent : baseEnd_3805625 < baseStart_3805625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805629 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 5]
def baseStart_3805629 : Nat := 118140960795 + 3805629 * 2 ^ 59
def prefixEnd_3805629 : Nat := 4983230072969 + 3 ^ 40 * 3805629 * 2
def baseEnd_3805629 : Nat := 217124096632155132526193

theorem tailTrace_3805629 : CollatzResearch.WordTrace tailWord_3805629 prefixEnd_3805629 217124096632155132526193 := by
  unfold tailWord_3805629
  simp only [CollatzResearch.WordTrace]
  refine ⟨138802692729863557533171941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92535128486575705022114627 138802692729863557533171941)
  ·
    refine ⟨26025504886849417037469739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138802692729863557533171941 26025504886849417037469739)
    ·
      refine ⟨39038257330274125556204609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26025504886849417037469739 39038257330274125556204609)
      ·
        refine ⟨29278692997705594167153457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39038257330274125556204609 29278692997705594167153457)
        ·
          refine ⟨21959019748279195625365093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29278692997705594167153457 21959019748279195625365093)
          ·
            refine ⟨4117316202802349179755955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21959019748279195625365093 4117316202802349179755955)
            ·
              refine ⟨6175974304203523769633933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117316202802349179755955 6175974304203523769633933)
              ·
                refine ⟨2315990364076321413612725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6175974304203523769633933 2315990364076321413612725)
                ·
                  refine ⟨217124096632155132526193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2315990364076321413612725 217124096632155132526193)
                  ·
                    rfl

theorem cell23_3805629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_3805629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805629 prefixEnd_3805629 := by exact prefixLift 3805629
  have htrace : WordTrace (prefixWord ++ tailWord_3805629) baseStart_3805629 baseEnd_3805629 := by
    simpa [prefixWord, tailWord_3805629, baseEnd_3805629] using wordTrace_append hprefix tailTrace_3805629
  have hstable : (prefixWord ++ tailWord_3805629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805629).length < 2 ^ (prefixWord ++ tailWord_3805629).sum := by decide
  have hdescent : baseEnd_3805629 < baseStart_3805629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805652 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3805652 : Nat := 118140960795 + 3805652 * 2 ^ 59
def prefixEnd_3805652 : Nat := 4983230072969 + 3 ^ 40 * 3805652 * 2
def baseEnd_3805652 : Nat := 1954128679744449602748131

theorem tailTrace_3805652 : CollatzResearch.WordTrace tailWord_3805652 prefixEnd_3805652 1954128679744449602748131 := by
  unfold tailWord_3805652
  simp only [CollatzResearch.WordTrace]
  refine ⟨69401765804390116230629605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92535687739186821640839473 69401765804390116230629605)
  ·
    refine ⟨13012831088323146793243051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69401765804390116230629605 13012831088323146793243051)
    ·
      refine ⟨19519246632484720189864577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13012831088323146793243051 19519246632484720189864577)
      ·
        refine ⟨14639434974363540142398433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19519246632484720189864577 14639434974363540142398433)
        ·
          refine ⟨10979576230772655106798825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14639434974363540142398433 10979576230772655106798825)
          ·
            refine ⟨8234682173079491330099119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10979576230772655106798825 8234682173079491330099119)
            ·
              refine ⟨12352023259619236995148679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234682173079491330099119 12352023259619236995148679)
              ·
                refine ⟨18528034889428855492723019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12352023259619236995148679 18528034889428855492723019)
                ·
                  refine ⟨27792052334143283239084529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18528034889428855492723019 27792052334143283239084529)
                  ·
                    refine ⟨20844039250607462429313397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27792052334143283239084529 20844039250607462429313397)
                    ·
                      refine ⟨1954128679744449602748131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20844039250607462429313397 1954128679744449602748131)
                      ·
                        rfl

theorem cell23_3805652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3805652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805652 prefixEnd_3805652 := by exact prefixLift 3805652
  have htrace : WordTrace (prefixWord ++ tailWord_3805652) baseStart_3805652 baseEnd_3805652 := by
    simpa [prefixWord, tailWord_3805652, baseEnd_3805652] using wordTrace_append hprefix tailTrace_3805652
  have hstable : (prefixWord ++ tailWord_3805652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805652).length < 2 ^ (prefixWord ++ tailWord_3805652).sum := by decide
  have hdescent : baseEnd_3805652 < baseStart_3805652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805715 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 5, 5]
def baseStart_3805715 : Nat := 118140960795 + 3805715 * 2 ^ 59
def prefixEnd_3805715 : Nat := 4983230072969 + 3 ^ 40 * 3805715 * 2
def baseEnd_3805715 : Nat := 651387009675227618753447

theorem tailTrace_3805715 : CollatzResearch.WordTrace tailWord_3805715 prefixEnd_3805715 651387009675227618753447 := by
  unfold tailWord_3805715
  simp only [CollatzResearch.WordTrace]
  refine ⟨138805829407551994220802599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92537219605034662813868399 138805829407551994220802599)
  ·
    refine ⟨208208744111327991331203899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138805829407551994220802599 208208744111327991331203899)
    ·
      refine ⟨312313116166991986996805849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208208744111327991331203899 312313116166991986996805849)
      ·
        refine ⟨234234837125243990247604387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312313116166991986996805849 234234837125243990247604387)
        ·
          refine ⟨351352255687865985371406581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234234837125243990247604387 351352255687865985371406581)
          ·
            refine ⟨32939273970737436128569367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351352255687865985371406581 32939273970737436128569367)
            ·
              refine ⟨49408910956106154192854051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32939273970737436128569367 49408910956106154192854051)
              ·
                refine ⟨74113366434159231289281077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49408910956106154192854051 74113366434159231289281077)
                ·
                  refine ⟨6948128103202427933370101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74113366434159231289281077 6948128103202427933370101)
                  ·
                    refine ⟨651387009675227618753447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6948128103202427933370101 651387009675227618753447)
                    ·
                      rfl

theorem cell23_3805715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 5].length) (baseStart_3805715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805715 prefixEnd_3805715 := by exact prefixLift 3805715
  have htrace : WordTrace (prefixWord ++ tailWord_3805715) baseStart_3805715 baseEnd_3805715 := by
    simpa [prefixWord, tailWord_3805715, baseEnd_3805715] using wordTrace_append hprefix tailTrace_3805715
  have hstable : (prefixWord ++ tailWord_3805715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805715).length < 2 ^ (prefixWord ++ tailWord_3805715).sum := by decide
  have hdescent : baseEnd_3805715 < baseStart_3805715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805729 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3805729 : Nat := 118140960795 + 3805729 * 2 ^ 59
def prefixEnd_3805729 : Nat := 4983230072969 + 3 ^ 40 * 3805729 * 2
def baseEnd_3805729 : Nat := 1954168217754845801485277

theorem tailTrace_3805729 : CollatzResearch.WordTrace tailWord_3805729 prefixEnd_3805729 1954168217754845801485277 := by
  unfold tailWord_3805729
  simp only [CollatzResearch.WordTrace]
  refine ⟨138806340029501274611812241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92537560019667516407874827 138806340029501274611812241)
  ·
    refine ⟨104104755022125955958859181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138806340029501274611812241 104104755022125955958859181)
    ·
      refine ⟨39039283133297233484572193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104104755022125955958859181 39039283133297233484572193)
      ·
        refine ⟨29279462349972925113429145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39039283133297233484572193 29279462349972925113429145)
        ·
          refine ⟨21959596762479693835071859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29279462349972925113429145 21959596762479693835071859)
          ·
            refine ⟨32939395143719540752607789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21959596762479693835071859 32939395143719540752607789)
            ·
              refine ⟨12352273178894827782227921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32939395143719540752607789 12352273178894827782227921)
              ·
                refine ⟨9264204884171120836670941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12352273178894827782227921 9264204884171120836670941)
                ·
                  refine ⟨3474076831564170313751603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9264204884171120836670941 3474076831564170313751603)
                  ·
                    refine ⟨5211115247346255470627405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474076831564170313751603 5211115247346255470627405)
                    ·
                      refine ⟨1954168217754845801485277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211115247346255470627405 1954168217754845801485277)
                      ·
                        rfl

theorem cell23_3805729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3805729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805729 prefixEnd_3805729 := by exact prefixLift 3805729
  have htrace : WordTrace (prefixWord ++ tailWord_3805729) baseStart_3805729 baseEnd_3805729 := by
    simpa [prefixWord, tailWord_3805729, baseEnd_3805729] using wordTrace_append hprefix tailTrace_3805729
  have hstable : (prefixWord ++ tailWord_3805729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805729).length < 2 ^ (prefixWord ++ tailWord_3805729).sum := by decide
  have hdescent : baseEnd_3805729 < baseStart_3805729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805746 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_3805746 : Nat := 118140960795 + 3805746 * 2 ^ 59
def prefixEnd_3805746 : Nat := 4983230072969 + 3 ^ 40 * 3805746 * 2
def baseEnd_3805746 : Nat := 1954176946925972234972699

theorem tailTrace_3805746 : CollatzResearch.WordTrace tailWord_3805746 prefixEnd_3805746 1954176946925972234972699 := by
  unfold tailWord_3805746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34701740017609921628795273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92537973380293124343454061 34701740017609921628795273)
  ·
    refine ⟨26026305013207441221596455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34701740017609921628795273 26026305013207441221596455)
    ·
      refine ⟨39039457519811161832394683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26026305013207441221596455 39039457519811161832394683)
      ·
        refine ⟨58559186279716742748592025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39039457519811161832394683 58559186279716742748592025)
        ·
          refine ⟨43919389709787557061444019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58559186279716742748592025 43919389709787557061444019)
          ·
            refine ⟨65879084564681335592166029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43919389709787557061444019 65879084564681335592166029)
            ·
              refine ⟨24704656711755500847062261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65879084564681335592166029 24704656711755500847062261)
              ·
                refine ⟨2316061566727078204412087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24704656711755500847062261 2316061566727078204412087)
                ·
                  refine ⟨3474092350090617306618131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316061566727078204412087 3474092350090617306618131)
                  ·
                    refine ⟨5211138525135925959927197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474092350090617306618131 5211138525135925959927197)
                    ·
                      refine ⟨1954176946925972234972699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211138525135925959927197 1954176946925972234972699)
                      ·
                        rfl

theorem cell23_3805746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_3805746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805746 prefixEnd_3805746 := by exact prefixLift 3805746
  have htrace : WordTrace (prefixWord ++ tailWord_3805746) baseStart_3805746 baseEnd_3805746 := by
    simpa [prefixWord, tailWord_3805746, baseEnd_3805746] using wordTrace_append hprefix tailTrace_3805746
  have hstable : (prefixWord ++ tailWord_3805746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805746).length < 2 ^ (prefixWord ++ tailWord_3805746).sum := by decide
  have hdescent : baseEnd_3805746 < baseStart_3805746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805772 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3805772 : Nat := 118140960795 + 3805772 * 2 ^ 59
def prefixEnd_3805772 : Nat := 4983230072969 + 3 ^ 40 * 3805772 * 2
def baseEnd_3805772 : Nat := 1954190297422989133247579

theorem tailTrace_3805772 : CollatzResearch.WordTrace tailWord_3805772 prefixEnd_3805772 1954190297422989133247579 := by
  unfold tailWord_3805772
  simp only [CollatzResearch.WordTrace]
  refine ⟨69403954184172746477813785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92538605578896995303751713 69403954184172746477813785)
  ·
    refine ⟨52052965638129559858360339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69403954184172746477813785 52052965638129559858360339)
    ·
      refine ⟨78079448457194339787540509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52052965638129559858360339 78079448457194339787540509)
      ·
        refine ⟨29279793171447877420327691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78079448457194339787540509 29279793171447877420327691)
        ·
          refine ⟨43919689757171816130491537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29279793171447877420327691 43919689757171816130491537)
          ·
            refine ⟨32939767317878862097868653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43919689757171816130491537 32939767317878862097868653)
            ·
              refine ⟨12352412744204573286700745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32939767317878862097868653 12352412744204573286700745)
              ·
                refine ⟨9264309558153429965025559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12352412744204573286700745 9264309558153429965025559)
                ·
                  refine ⟨13896464337230144947538339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264309558153429965025559 13896464337230144947538339)
                  ·
                    refine ⟨20844696505845217421307509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13896464337230144947538339 20844696505845217421307509)
                    ·
                      refine ⟨1954190297422989133247579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20844696505845217421307509 1954190297422989133247579)
                      ·
                        rfl

theorem cell23_3805772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3805772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805772 prefixEnd_3805772 := by exact prefixLift 3805772
  have htrace : WordTrace (prefixWord ++ tailWord_3805772) baseStart_3805772 baseEnd_3805772 := by
    simpa [prefixWord, tailWord_3805772, baseEnd_3805772] using wordTrace_append hprefix tailTrace_3805772
  have hstable : (prefixWord ++ tailWord_3805772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805772).length < 2 ^ (prefixWord ++ tailWord_3805772).sum := by decide
  have hdescent : baseEnd_3805772 < baseStart_3805772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805792 : List Nat := [2, 1, 1, 3, 2, 1, 6, 7]
def baseStart_3805792 : Nat := 118140960795 + 3805792 * 2 ^ 59
def prefixEnd_3805792 : Nat := 4983230072969 + 3 ^ 40 * 3805792 * 2
def baseEnd_3805792 : Nat := 72377798779114039073981

theorem tailTrace_3805792 : CollatzResearch.WordTrace tailWord_3805792 prefixEnd_3805792 72377798779114039073981 := by
  unfold tailWord_3805792
  simp only [CollatzResearch.WordTrace]
  refine ⟨69404318914136518185677815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92539091885515357580903753 69404318914136518185677815)
  ·
    refine ⟨104106478371204777278516723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69404318914136518185677815 104106478371204777278516723)
    ·
      refine ⟨156159717556807165917775085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104106478371204777278516723 156159717556807165917775085)
      ·
        refine ⟨58559894083802687219165657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156159717556807165917775085 58559894083802687219165657)
        ·
          refine ⟨43919920562852015414374243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58559894083802687219165657 43919920562852015414374243)
          ·
            refine ⟨65879880844278023121561365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43919920562852015414374243 65879880844278023121561365)
            ·
              refine ⟨3088119414575532333823189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65879880844278023121561365 3088119414575532333823189)
              ·
                refine ⟨72377798779114039073981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3088119414575532333823189 72377798779114039073981)
                ·
                  rfl

theorem cell23_3805792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 7].length) (baseStart_3805792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805792 prefixEnd_3805792 := by exact prefixLift 3805792
  have htrace : WordTrace (prefixWord ++ tailWord_3805792) baseStart_3805792 baseEnd_3805792 := by
    simpa [prefixWord, tailWord_3805792, baseEnd_3805792] using wordTrace_append hprefix tailTrace_3805792
  have hstable : (prefixWord ++ tailWord_3805792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805792).length < 2 ^ (prefixWord ++ tailWord_3805792).sum := by decide
  have hdescent : baseEnd_3805792 < baseStart_3805792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805806 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3805806 : Nat := 118140960795 + 3805806 * 2 ^ 59
def prefixEnd_3805806 : Nat := 4983230072969 + 3 ^ 40 * 3805806 * 2
def baseEnd_3805806 : Nat := 1954207755765242000222423

theorem tailTrace_3805806 : CollatzResearch.WordTrace tailWord_3805806 prefixEnd_3805806 1954207755765242000222423 := by
  unfold tailWord_3805806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351143556277789595295659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92539432300148211174910181 17351143556277789595295659)
  ·
    refine ⟨26026715334416684392943489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17351143556277789595295659 26026715334416684392943489)
    ·
      refine ⟨19520036500812513294707617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26026715334416684392943489 19520036500812513294707617)
      ·
        refine ⟨14640027375609384971030713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19520036500812513294707617 14640027375609384971030713)
        ·
          refine ⟨10980020531707038728273035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14640027375609384971030713 10980020531707038728273035)
          ·
            refine ⟨16470030797560558092409553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10980020531707038728273035 16470030797560558092409553)
            ·
              refine ⟨12352523098170418569307165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16470030797560558092409553 12352523098170418569307165)
              ·
                refine ⟨4632196161813906963490187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12352523098170418569307165 4632196161813906963490187)
                ·
                  refine ⟨6948294242720860445235281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632196161813906963490187 6948294242720860445235281)
                  ·
                    refine ⟨5211220682040645333926461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6948294242720860445235281 5211220682040645333926461)
                    ·
                      refine ⟨1954207755765242000222423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211220682040645333926461 1954207755765242000222423)
                      ·
                        rfl

theorem cell23_3805806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3805806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805806 prefixEnd_3805806 := by exact prefixLift 3805806
  have htrace : WordTrace (prefixWord ++ tailWord_3805806) baseStart_3805806 baseEnd_3805806 := by
    simpa [prefixWord, tailWord_3805806, baseEnd_3805806] using wordTrace_append hprefix tailTrace_3805806
  have hstable : (prefixWord ++ tailWord_3805806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805806).length < 2 ^ (prefixWord ++ tailWord_3805806).sum := by decide
  have hdescent : baseEnd_3805806 < baseStart_3805806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805870 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3805870 : Nat := 118140960795 + 3805870 * 2 ^ 59
def prefixEnd_3805870 : Nat := 4983230072969 + 3 ^ 40 * 3805870 * 2
def baseEnd_3805870 : Nat := 1954240618527129749822129

theorem tailTrace_3805870 : CollatzResearch.WordTrace tailWord_3805870 prefixEnd_3805870 1954240618527129749822129 := by
  unfold tailWord_3805870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351435340248806961586883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92540988481326970461796709 17351435340248806961586883)
  ·
    refine ⟨26027153010373210442380325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17351435340248806961586883 26027153010373210442380325)
    ·
      refine ⟨4880091189444976957946311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26027153010373210442380325 4880091189444976957946311)
      ·
        refine ⟨7320136784167465436919467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880091189444976957946311 7320136784167465436919467)
        ·
          refine ⟨10980205176251198155379201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320136784167465436919467 10980205176251198155379201)
          ·
            refine ⟨8235153882188398616534401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10980205176251198155379201 8235153882188398616534401)
            ·
              refine ⟨6176365411641298962400801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235153882188398616534401 6176365411641298962400801)
              ·
                refine ⟨4632274058730974221800601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176365411641298962400801 4632274058730974221800601)
                ·
                  refine ⟨3474205544048230666350451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4632274058730974221800601 3474205544048230666350451)
                  ·
                    refine ⟨5211308316072345999525677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474205544048230666350451 5211308316072345999525677)
                    ·
                      refine ⟨1954240618527129749822129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211308316072345999525677 1954240618527129749822129)
                      ·
                        rfl

theorem cell23_3805870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3805870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805870 prefixEnd_3805870 := by exact prefixLift 3805870
  have htrace : WordTrace (prefixWord ++ tailWord_3805870) baseStart_3805870 baseEnd_3805870 := by
    simpa [prefixWord, tailWord_3805870, baseEnd_3805870] using wordTrace_append hprefix tailTrace_3805870
  have hstable : (prefixWord ++ tailWord_3805870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805870).length < 2 ^ (prefixWord ++ tailWord_3805870).sum := by decide
  have hdescent : baseEnd_3805870 < baseStart_3805870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805872 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_3805872 : Nat := 118140960795 + 3805872 * 2 ^ 59
def prefixEnd_3805872 : Nat := 4983230072969 + 3 ^ 40 * 3805872 * 2
def baseEnd_3805872 : Nat := 1954241645488438741997119

theorem tailTrace_3805872 : CollatzResearch.WordTrace tailWord_3805872 prefixEnd_3805872 1954241645488438741997119 := by
  unfold tailWord_3805872
  simp only [CollatzResearch.WordTrace]
  refine ⟨69405777833991605017133935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92541037111988806689511913 69405777833991605017133935)
  ·
    refine ⟨104108666750987407525700903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69405777833991605017133935 104108666750987407525700903)
    ·
      refine ⟨156163000126481111288551355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104108666750987407525700903 156163000126481111288551355)
      ·
        refine ⟨234244500189721666932827033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156163000126481111288551355 234244500189721666932827033)
        ·
          refine ⟨175683375142291250199620275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234244500189721666932827033 175683375142291250199620275)
          ·
            refine ⟨263525062713436875299430413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175683375142291250199620275 263525062713436875299430413)
            ·
              refine ⟨98821898517538828237286405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263525062713436875299430413 98821898517538828237286405)
              ·
                refine ⟨18529105972038530294491201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98821898517538828237286405 18529105972038530294491201)
                ·
                  refine ⟨13896829479028897720868401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18529105972038530294491201 13896829479028897720868401)
                  ·
                    refine ⟨10422622109271673290651301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13896829479028897720868401 10422622109271673290651301)
                    ·
                      refine ⟨1954241645488438741997119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10422622109271673290651301 1954241645488438741997119)
                      ·
                        rfl

theorem cell23_3805872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_3805872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805872 prefixEnd_3805872 := by exact prefixLift 3805872
  have htrace : WordTrace (prefixWord ++ tailWord_3805872) baseStart_3805872 baseEnd_3805872 := by
    simpa [prefixWord, tailWord_3805872, baseEnd_3805872] using wordTrace_append hprefix tailTrace_3805872
  have hstable : (prefixWord ++ tailWord_3805872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805872).length < 2 ^ (prefixWord ++ tailWord_3805872).sum := by decide
  have hdescent : baseEnd_3805872 < baseStart_3805872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805882 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_3805882 : Nat := 118140960795 + 3805882 * 2 ^ 59
def prefixEnd_3805882 : Nat := 4983230072969 + 3 ^ 40 * 3805882 * 2
def baseEnd_3805882 : Nat := 217138531143887078096897

theorem tailTrace_3805882 : CollatzResearch.WordTrace tailWord_3805882 prefixEnd_3805882 217138531143887078096897 := by
  unfold tailWord_3805882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34702980099486745435532975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92541280265297987828087933 34702980099486745435532975)
  ·
    refine ⟨52054470149230118153299463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34702980099486745435532975 52054470149230118153299463)
    ·
      refine ⟨78081705223845177229949195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52054470149230118153299463 78081705223845177229949195)
      ·
        refine ⟨117122557835767765844923793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78081705223845177229949195 117122557835767765844923793)
        ·
          refine ⟨87841918376825824383692845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117122557835767765844923793 87841918376825824383692845)
          ·
            refine ⟨32940719391309684143884817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87841918376825824383692845 32940719391309684143884817)
            ·
              refine ⟨24705539543482263107913613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32940719391309684143884817 24705539543482263107913613)
              ·
                refine ⟨9264577328805848665467605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24705539543482263107913613 9264577328805848665467605)
                ·
                  refine ⟨217138531143887078096897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9264577328805848665467605 217138531143887078096897)
                  ·
                    rfl

theorem cell23_3805882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_3805882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805882 prefixEnd_3805882 := by exact prefixLift 3805882
  have htrace : WordTrace (prefixWord ++ tailWord_3805882) baseStart_3805882 baseEnd_3805882 := by
    simpa [prefixWord, tailWord_3805882, baseEnd_3805882] using wordTrace_append hprefix tailTrace_3805882
  have hstable : (prefixWord ++ tailWord_3805882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805882).length < 2 ^ (prefixWord ++ tailWord_3805882).sum := by decide
  have hdescent : baseEnd_3805882 < baseStart_3805882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805969 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_3805969 : Nat := 118140960795 + 3805969 * 2 ^ 59
def prefixEnd_3805969 : Nat := 4983230072969 + 3 ^ 40 * 3805969 * 2
def baseEnd_3805969 : Nat := 1954291453111924862484173

theorem tailTrace_3805969 : CollatzResearch.WordTrace tailWord_3805969 prefixEnd_3805969 1954291453111924862484173 := by
  unfold tailWord_3805969
  simp only [CollatzResearch.WordTrace]
  refine ⟨138815093548631795600548961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92543395699087863733699307 138815093548631795600548961)
  ·
    refine ⟨104111320161473846700411721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138815093548631795600548961 104111320161473846700411721)
    ·
      refine ⟨78083490121105385025308791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104111320161473846700411721 78083490121105385025308791)
      ·
        refine ⟨117125235181658077537963187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78083490121105385025308791 117125235181658077537963187)
        ·
          refine ⟨175687852772487116306944781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117125235181658077537963187 175687852772487116306944781)
          ·
            refine ⟨65882944789682668615104293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175687852772487116306944781 65882944789682668615104293)
            ·
              refine ⟨12353052148065500365332055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65882944789682668615104293 12353052148065500365332055)
              ·
                refine ⟨18529578222098250547998083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12353052148065500365332055 18529578222098250547998083)
                ·
                  refine ⟨27794367333147375821997125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18529578222098250547998083 27794367333147375821997125)
                  ·
                    refine ⟨5211443874965132966624461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27794367333147375821997125 5211443874965132966624461)
                    ·
                      refine ⟨1954291453111924862484173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211443874965132966624461 1954291453111924862484173)
                      ·
                        rfl

theorem cell23_3805969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_3805969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805969 prefixEnd_3805969 := by exact prefixLift 3805969
  have htrace : WordTrace (prefixWord ++ tailWord_3805969) baseStart_3805969 baseEnd_3805969 := by
    simpa [prefixWord, tailWord_3805969, baseEnd_3805969] using wordTrace_append hprefix tailTrace_3805969
  have hstable : (prefixWord ++ tailWord_3805969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805969).length < 2 ^ (prefixWord ++ tailWord_3805969).sum := by decide
  have hdescent : baseEnd_3805969 < baseStart_3805969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805986 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_3805986 : Nat := 118140960795 + 3805986 * 2 ^ 59
def prefixEnd_3805986 : Nat := 4983230072969 + 3 ^ 40 * 3805986 * 2
def baseEnd_3805986 : Nat := 1954300182283051295971595

theorem tailTrace_3805986 : CollatzResearch.WordTrace tailWord_3805986 prefixEnd_3805986 1954300182283051295971595 := by
  unfold tailWord_3805986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34703928397392551875979453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92543809059713471669278541 34703928397392551875979453)
  ·
    refine ⟨13013973149022206953492295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34703928397392551875979453 13013973149022206953492295)
    ·
      refine ⟨19520959723533310430238443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13013973149022206953492295 19520959723533310430238443)
      ·
        refine ⟨29281439585299965645357665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19520959723533310430238443 29281439585299965645357665)
        ·
          refine ⟨21961079688974974234018249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29281439585299965645357665 21961079688974974234018249)
          ·
            refine ⟨16470809766731230675513687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21961079688974974234018249 16470809766731230675513687)
            ·
              refine ⟨24706214650096846013270531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16470809766731230675513687 24706214650096846013270531)
              ·
                refine ⟨37059321975145269019905797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24706214650096846013270531 37059321975145269019905797)
                ·
                  refine ⟨6948622870339737941232337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37059321975145269019905797 6948622870339737941232337)
                  ·
                    refine ⟨5211467152754803455924253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6948622870339737941232337 5211467152754803455924253)
                    ·
                      refine ⟨1954300182283051295971595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211467152754803455924253 1954300182283051295971595)
                      ·
                        rfl

theorem cell23_3805986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_3805986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805986 prefixEnd_3805986 := by exact prefixLift 3805986
  have htrace : WordTrace (prefixWord ++ tailWord_3805986) baseStart_3805986 baseEnd_3805986 := by
    simpa [prefixWord, tailWord_3805986, baseEnd_3805986] using wordTrace_append hprefix tailTrace_3805986
  have hstable : (prefixWord ++ tailWord_3805986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805986).length < 2 ^ (prefixWord ++ tailWord_3805986).sum := by decide
  have hdescent : baseEnd_3805986 < baseStart_3805986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805989 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 6]
def baseStart_3805989 : Nat := 118140960795 + 3805989 * 2 ^ 59
def prefixEnd_3805989 : Nat := 4983230072969 + 3 ^ 40 * 3805989 * 2
def baseEnd_3805989 : Nat := 217144635858334976026009

theorem tailTrace_3805989 : CollatzResearch.WordTrace tailWord_3805989 prefixEnd_3805989 217144635858334976026009 := by
  unfold tailWord_3805989
  simp only [CollatzResearch.WordTrace]
  refine ⟨138815823008559339016277021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92543882005706226010851347 138815823008559339016277021)
  ·
    refine ⟨52055933628209752131103883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138815823008559339016277021 52055933628209752131103883)
    ·
      refine ⟨78083900442314628196655825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52055933628209752131103883 78083900442314628196655825)
      ·
        refine ⟨58562925331735971147491869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78083900442314628196655825 58562925331735971147491869)
        ·
          refine ⟨21961096999400989180309451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58562925331735971147491869 21961096999400989180309451)
          ·
            refine ⟨32941645499101483770464177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21961096999400989180309451 32941645499101483770464177)
            ·
              refine ⟨24706234124326112827848133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32941645499101483770464177 24706234124326112827848133)
              ·
                refine ⟨4632418898311146155221525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24706234124326112827848133 4632418898311146155221525)
                ·
                  refine ⟨217144635858334976026009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4632418898311146155221525 217144635858334976026009)
                  ·
                    rfl

theorem cell23_3805989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_3805989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3805989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3805989 prefixEnd_3805989 := by exact prefixLift 3805989
  have htrace : WordTrace (prefixWord ++ tailWord_3805989) baseStart_3805989 baseEnd_3805989 := by
    simpa [prefixWord, tailWord_3805989, baseEnd_3805989] using wordTrace_append hprefix tailTrace_3805989
  have hstable : (prefixWord ++ tailWord_3805989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805989).length < 2 ^ (prefixWord ++ tailWord_3805989).sum := by decide
  have hdescent : baseEnd_3805989 < baseStart_3805989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806016 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 3, 1, 3]
def baseStart_3806016 : Nat := 118140960795 + 3806016 * 2 ^ 59
def prefixEnd_3806016 : Nat := 4983230072969 + 3 ^ 40 * 3806016 * 2
def baseEnd_3806016 : Nat := 1954315586702686178596457

theorem tailTrace_3806016 : CollatzResearch.WordTrace tailWord_3806016 prefixEnd_3806016 1954315586702686178596457 := by
  unfold tailWord_3806016
  simp only [CollatzResearch.WordTrace]
  refine ⟨69408403889730761313754951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92544538519641015085006601 69408403889730761313754951)
  ·
    refine ⟨104112605834596141970632427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69408403889730761313754951 104112605834596141970632427)
    ·
      refine ⟨156168908751894212955948641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104112605834596141970632427 156168908751894212955948641)
      ·
        refine ⟨117126681563920659716961481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156168908751894212955948641 117126681563920659716961481)
        ·
          refine ⟨87845011172940494787721111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117126681563920659716961481 87845011172940494787721111)
          ·
            refine ⟨131767516759410742181581667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87845011172940494787721111 131767516759410742181581667)
            ·
              refine ⟨197651275139116113272372501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131767516759410742181581667 197651275139116113272372501)
              ·
                refine ⟨9264903522146067809642461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197651275139116113272372501 9264903522146067809642461)
                ·
                  refine ⟨3474338820804775428615923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9264903522146067809642461 3474338820804775428615923)
                  ·
                    refine ⟨5211508231207163142923885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474338820804775428615923 5211508231207163142923885)
                    ·
                      refine ⟨1954315586702686178596457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211508231207163142923885 1954315586702686178596457)
                      ·
                        rfl

theorem cell23_3806016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_3806016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806016 prefixEnd_3806016 := by exact prefixLift 3806016
  have htrace : WordTrace (prefixWord ++ tailWord_3806016) baseStart_3806016 baseEnd_3806016 := by
    simpa [prefixWord, tailWord_3806016, baseEnd_3806016] using wordTrace_append hprefix tailTrace_3806016
  have hstable : (prefixWord ++ tailWord_3806016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806016).length < 2 ^ (prefixWord ++ tailWord_3806016).sum := by decide
  have hdescent : baseEnd_3806016 < baseStart_3806016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806019 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 3, 5]
def baseStart_3806019 : Nat := 118140960795 + 3806019 * 2 ^ 59
def prefixEnd_3806019 : Nat := 4983230072969 + 3 ^ 40 * 3806019 * 2
def baseEnd_3806019 : Nat := 651439042381549888952981

theorem tailTrace_3806019 : CollatzResearch.WordTrace tailWord_3806019 prefixEnd_3806019 651439042381549888952981 := by
  unfold tailWord_3806019
  simp only [CollatzResearch.WordTrace]
  refine ⟨138816917198450654139869111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92544611465633769426579407 138816917198450654139869111)
  ·
    refine ⟨208225375797675981209803667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138816917198450654139869111 208225375797675981209803667)
    ·
      refine ⟨312338063696513971814705501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208225375797675981209803667 312338063696513971814705501)
      ·
        refine ⟨117126773886192739430514563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312338063696513971814705501 117126773886192739430514563)
        ·
          refine ⟨175690160829289109145771845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117126773886192739430514563 175690160829289109145771845)
          ·
            refine ⟨32941905155491707964832221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175690160829289109145771845 32941905155491707964832221)
            ·
              refine ⟨12353214433309390486812083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32941905155491707964832221 12353214433309390486812083)
              ·
                refine ⟨18529821649964085730218125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12353214433309390486812083 18529821649964085730218125)
                ·
                  refine ⟨6948683118736532148831797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18529821649964085730218125 6948683118736532148831797)
                  ·
                    refine ⟨651439042381549888952981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6948683118736532148831797 651439042381549888952981)
                    ·
                      rfl

theorem cell23_3806019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 5].length) (baseStart_3806019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806019 prefixEnd_3806019 := by exact prefixLift 3806019
  have htrace : WordTrace (prefixWord ++ tailWord_3806019) baseStart_3806019 baseEnd_3806019 := by
    simpa [prefixWord, tailWord_3806019, baseEnd_3806019] using wordTrace_append hprefix tailTrace_3806019
  have hstable : (prefixWord ++ tailWord_3806019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806019).length < 2 ^ (prefixWord ++ tailWord_3806019).sum := by decide
  have hdescent : baseEnd_3806019 < baseStart_3806019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806056 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3806056 : Nat := 118140960795 + 3806056 * 2 ^ 59
def prefixEnd_3806056 : Nat := 4983230072969 + 3 ^ 40 * 3806056 * 2
def baseEnd_3806056 : Nat := 1954336125928866022096273

theorem tailTrace_3806056 : CollatzResearch.WordTrace tailWord_3806056 prefixEnd_3806056 1954336125928866022096273 := by
  unfold tailWord_3806056
  simp only [CollatzResearch.WordTrace]
  refine ⟨69409133349658304729483011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92545511132877739639310681 69409133349658304729483011)
  ·
    refine ⟨104113700024487457094224517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69409133349658304729483011 104113700024487457094224517)
    ·
      refine ⟨19521318754591398205167097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104113700024487457094224517 19521318754591398205167097)
      ·
        refine ⟨14640989065943548653875323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19521318754591398205167097 14640989065943548653875323)
        ·
          refine ⟨21961483598915322980812985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14640989065943548653875323 21961483598915322980812985)
          ·
            refine ⟨16471112699186492235609739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21961483598915322980812985 16471112699186492235609739)
            ·
              refine ⟨24706669048779738353414609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16471112699186492235609739 24706669048779738353414609)
              ·
                refine ⟨18530001786584803765060957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24706669048779738353414609 18530001786584803765060957)
                ·
                  refine ⟨6948750669969301411897859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18530001786584803765060957 6948750669969301411897859)
                  ·
                    refine ⟨10423126004953952117846789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948750669969301411897859 10423126004953952117846789)
                    ·
                      refine ⟨1954336125928866022096273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10423126004953952117846789 1954336125928866022096273)
                      ·
                        rfl

theorem cell23_3806056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3806056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806056 prefixEnd_3806056 := by exact prefixLift 3806056
  have htrace : WordTrace (prefixWord ++ tailWord_3806056) baseStart_3806056 baseEnd_3806056 := by
    simpa [prefixWord, tailWord_3806056, baseEnd_3806056] using wordTrace_append hprefix tailTrace_3806056
  have hstable : (prefixWord ++ tailWord_3806056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806056).length < 2 ^ (prefixWord ++ tailWord_3806056).sum := by decide
  have hdescent : baseEnd_3806056 < baseStart_3806056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806059 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5]
def baseStart_3806059 : Nat := 118140960795 + 3806059 * 2 ^ 59
def prefixEnd_3806059 : Nat := 4983230072969 + 3 ^ 40 * 3806059 * 2
def baseEnd_3806059 : Nat := 1954337666370829510358759

theorem tailTrace_3806059 : CollatzResearch.WordTrace tailWord_3806059 prefixEnd_3806059 1954337666370829510358759 := by
  unfold tailWord_3806059
  simp only [CollatzResearch.WordTrace]
  refine ⟨138818376118305740971325231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92545584078870493980883487 138818376118305740971325231)
  ·
    refine ⟨208227564177458611456987847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138818376118305740971325231 208227564177458611456987847)
    ·
      refine ⟨312341346266187917185481771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208227564177458611456987847 312341346266187917185481771)
      ·
        refine ⟨468512019399281875778222657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312341346266187917185481771 468512019399281875778222657)
        ·
          refine ⟨351384014549461406833666993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468512019399281875778222657 351384014549461406833666993)
          ·
            refine ⟨263538010912096055125250245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351384014549461406833666993 263538010912096055125250245)
            ·
              refine ⟨49413377046018010335984421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263538010912096055125250245 49413377046018010335984421)
              ·
                refine ⟨9265008196128376937997079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49413377046018010335984421 9265008196128376937997079)
                ·
                  refine ⟨13897512294192565406995619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9265008196128376937997079 13897512294192565406995619)
                  ·
                    refine ⟨20846268441288848110493429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13897512294192565406995619 20846268441288848110493429)
                    ·
                      refine ⟨1954337666370829510358759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20846268441288848110493429 1954337666370829510358759)
                      ·
                        rfl

theorem cell23_3806059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].length) (baseStart_3806059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806059 prefixEnd_3806059 := by exact prefixLift 3806059
  have htrace : WordTrace (prefixWord ++ tailWord_3806059) baseStart_3806059 baseEnd_3806059 := by
    simpa [prefixWord, tailWord_3806059, baseEnd_3806059] using wordTrace_append hprefix tailTrace_3806059
  have hstable : (prefixWord ++ tailWord_3806059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806059).length < 2 ^ (prefixWord ++ tailWord_3806059).sum := by decide
  have hdescent : baseEnd_3806059 < baseStart_3806059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806073 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 5, 2, 2]
def baseStart_3806073 : Nat := 118140960795 + 3806073 * 2 ^ 59
def prefixEnd_3806073 : Nat := 4983230072969 + 3 ^ 40 * 3806073 * 2
def baseEnd_3806073 : Nat := 1954344855099992455583695

theorem tailTrace_3806073 : CollatzResearch.WordTrace tailWord_3806073 prefixEnd_3806073 1954344855099992455583695 := by
  unfold tailWord_3806073
  simp only [CollatzResearch.WordTrace]
  refine ⟨138818886740255021362334873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92545924493503347574889915 138818886740255021362334873)
  ·
    refine ⟨104114165055191266021751155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138818886740255021362334873 104114165055191266021751155)
    ·
      refine ⟨156171247582786899032626733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104114165055191266021751155 156171247582786899032626733)
      ·
        refine ⟨58564217843545087137235025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156171247582786899032626733 58564217843545087137235025)
        ·
          refine ⟨43923163382658815352926269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58564217843545087137235025 43923163382658815352926269)
          ·
            refine ⟨16471186268497055757347351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43923163382658815352926269 16471186268497055757347351)
            ·
              refine ⟨24706779402745583636021027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16471186268497055757347351 24706779402745583636021027)
              ·
                refine ⟨37060169104118375454031541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24706779402745583636021027 37060169104118375454031541)
                ·
                  refine ⟨3474390853511097698815457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37060169104118375454031541 3474390853511097698815457)
                  ·
                    refine ⟨2605793140133323274111593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3474390853511097698815457 2605793140133323274111593)
                    ·
                      refine ⟨1954344855099992455583695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605793140133323274111593 1954344855099992455583695)
                      ·
                        rfl

theorem cell23_3806073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_3806073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806073 prefixEnd_3806073 := by exact prefixLift 3806073
  have htrace : WordTrace (prefixWord ++ tailWord_3806073) baseStart_3806073 baseEnd_3806073 := by
    simpa [prefixWord, tailWord_3806073, baseEnd_3806073] using wordTrace_append hprefix tailTrace_3806073
  have hstable : (prefixWord ++ tailWord_3806073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806073).length < 2 ^ (prefixWord ++ tailWord_3806073).sum := by decide
  have hdescent : baseEnd_3806073 < baseStart_3806073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806090 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_3806090 : Nat := 118140960795 + 3806090 * 2 ^ 59
def prefixEnd_3806090 : Nat := 4983230072969 + 3 ^ 40 * 3806090 * 2
def baseEnd_3806090 : Nat := 1954353584271118889071117

theorem tailTrace_3806090 : CollatzResearch.WordTrace tailWord_3806090 prefixEnd_3806090 1954353584271118889071117 := by
  unfold tailWord_3806090
  simp only [CollatzResearch.WordTrace]
  refine ⟨34704876695298358316425931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92546337854128955510469149 34704876695298358316425931)
  ·
    refine ⟨52057315042947537474638897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34704876695298358316425931 52057315042947537474638897)
    ·
      refine ⟨39042986282210653105979173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52057315042947537474638897 39042986282210653105979173)
      ·
        refine ⟨7320559927914497457371095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39042986282210653105979173 7320559927914497457371095)
        ·
          refine ⟨10980839891871746186056643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320559927914497457371095 10980839891871746186056643)
          ·
            refine ⟨16471259837807619279084965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10980839891871746186056643 16471259837807619279084965)
            ·
              refine ⟨3088361219588928614828431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16471259837807619279084965 3088361219588928614828431)
              ·
                refine ⟨4632541829383392922242647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088361219588928614828431 4632541829383392922242647)
                ·
                  refine ⟨6948812744075089383363971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632541829383392922242647 6948812744075089383363971)
                  ·
                    refine ⟨10423219116112634075045957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948812744075089383363971 10423219116112634075045957)
                    ·
                      refine ⟨1954353584271118889071117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10423219116112634075045957 1954353584271118889071117)
                      ·
                        rfl

theorem cell23_3806090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_3806090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806090 prefixEnd_3806090 := by exact prefixLift 3806090
  have htrace : WordTrace (prefixWord ++ tailWord_3806090) baseStart_3806090 baseEnd_3806090 := by
    simpa [prefixWord, tailWord_3806090, baseEnd_3806090] using wordTrace_append hprefix tailTrace_3806090
  have hstable : (prefixWord ++ tailWord_3806090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806090).length < 2 ^ (prefixWord ++ tailWord_3806090).sum := by decide
  have hdescent : baseEnd_3806090 < baseStart_3806090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806141 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_3806141 : Nat := 118140960795 + 3806141 * 2 ^ 59
def prefixEnd_3806141 : Nat := 4983230072969 + 3 ^ 40 * 3806141 * 2
def baseEnd_3806141 : Nat := 1954379771784498189533383

theorem tailTrace_3806141 : CollatzResearch.WordTrace tailWord_3806141 prefixEnd_3806141 1954379771784498189533383 := by
  unfold tailWord_3806141
  simp only [CollatzResearch.WordTrace]
  refine ⟨138821366904008668975810277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92547577936005779317206851 138821366904008668975810277)
  ·
    refine ⟨26029006294501625432964427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138821366904008668975810277 26029006294501625432964427)
    ·
      refine ⟨39043509441752438149446641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26029006294501625432964427 39043509441752438149446641)
      ·
        refine ⟨29282632081314328612084981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39043509441752438149446641 29282632081314328612084981)
        ·
          refine ⟨2745246757623218307382967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29282632081314328612084981 2745246757623218307382967)
          ·
            refine ⟨4117870136434827461074451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745246757623218307382967 4117870136434827461074451)
            ·
              refine ⟨6176805204652241191611677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117870136434827461074451 6176805204652241191611677)
              ·
                refine ⟨2316301951744590446854379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6176805204652241191611677 2316301951744590446854379)
                ·
                  refine ⟨3474452927616885670281569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316301951744590446854379 3474452927616885670281569)
                  ·
                    refine ⟨2605839695712664252711177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3474452927616885670281569 2605839695712664252711177)
                    ·
                      refine ⟨1954379771784498189533383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2605839695712664252711177 1954379771784498189533383)
                      ·
                        rfl

theorem cell23_3806141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_3806141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806141 prefixEnd_3806141 := by exact prefixLift 3806141
  have htrace : WordTrace (prefixWord ++ tailWord_3806141) baseStart_3806141 baseEnd_3806141 := by
    simpa [prefixWord, tailWord_3806141, baseEnd_3806141] using wordTrace_append hprefix tailTrace_3806141
  have hstable : (prefixWord ++ tailWord_3806141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806141).length < 2 ^ (prefixWord ++ tailWord_3806141).sum := by decide
  have hdescent : baseEnd_3806141 < baseStart_3806141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806220 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 5]
def baseStart_3806220 : Nat := 118140960795 + 3806220 * 2 ^ 59
def prefixEnd_3806220 : Nat := 4983230072969 + 3 ^ 40 * 3806220 * 2
def baseEnd_3806220 : Nat := 217157815195133708938391

theorem tailTrace_3806220 : CollatzResearch.WordTrace tailWord_3806220 prefixEnd_3806220 217157815195133708938391 := by
  unfold tailWord_3806220
  simp only [CollatzResearch.WordTrace]
  refine ⟨69412124135361232733968057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92549498847148310311957409 69412124135361232733968057)
  ·
    refine ⟨52059093101520924550476043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69412124135361232733968057 52059093101520924550476043)
    ·
      refine ⟨78088639652281386825714065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52059093101520924550476043 78088639652281386825714065)
      ·
        refine ⟨58566479739211040119285549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78088639652281386825714065 58566479739211040119285549)
        ·
          refine ⟨21962429902204140044732081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58566479739211040119285549 21962429902204140044732081)
          ·
            refine ⟨16471822426653105033549061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21962429902204140044732081 16471822426653105033549061)
            ·
              refine ⟨3088466704997457193790449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16471822426653105033549061 3088466704997457193790449)
              ·
                refine ⟨2316350028748092895342837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088466704997457193790449 2316350028748092895342837)
                ·
                  refine ⟨217157815195133708938391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2316350028748092895342837 217157815195133708938391)
                  ·
                    rfl

theorem cell23_3806220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_3806220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806220 prefixEnd_3806220 := by exact prefixLift 3806220
  have htrace : WordTrace (prefixWord ++ tailWord_3806220) baseStart_3806220 baseEnd_3806220 := by
    simpa [prefixWord, tailWord_3806220, baseEnd_3806220] using wordTrace_append hprefix tailTrace_3806220
  have hstable : (prefixWord ++ tailWord_3806220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806220).length < 2 ^ (prefixWord ++ tailWord_3806220).sum := by decide
  have hdescent : baseEnd_3806220 < baseStart_3806220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806266 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_3806266 : Nat := 118140960795 + 3806266 * 2 ^ 59
def prefixEnd_3806266 : Nat := 4983230072969 + 3 ^ 40 * 3806266 * 2
def baseEnd_3806266 : Nat := 1954443956866310200470307

theorem tailTrace_3806266 : CollatzResearch.WordTrace tailWord_3806266 prefixEnd_3806266 1954443956866310200470307 := by
  unfold tailWord_3806266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34706481507138953831027663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92550617352370543549407101 34706481507138953831027663)
  ·
    refine ⟨52059722260708430746541495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34706481507138953831027663 52059722260708430746541495)
    ·
      refine ⟨78089583391062646119812243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52059722260708430746541495 78089583391062646119812243)
      ·
        refine ⟨117134375086593969179718365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78089583391062646119812243 117134375086593969179718365)
        ·
          refine ⟨43925390657472738442394387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117134375086593969179718365 43925390657472738442394387)
          ·
            refine ⟨65888085986209107663591581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43925390657472738442394387 65888085986209107663591581)
            ·
              refine ⟨24708032244828415373846843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65888085986209107663591581 24708032244828415373846843)
              ·
                refine ⟨37062048367242623060770265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24708032244828415373846843 37062048367242623060770265)
                ·
                  refine ⟨27796536275431967295577699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37062048367242623060770265 27796536275431967295577699)
                  ·
                    refine ⟨41694804413147950943366549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27796536275431967295577699 41694804413147950943366549)
                    ·
                      refine ⟨1954443956866310200470307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41694804413147950943366549 1954443956866310200470307)
                      ·
                        rfl

theorem cell23_3806266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_3806266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806266 prefixEnd_3806266 := by exact prefixLift 3806266
  have htrace : WordTrace (prefixWord ++ tailWord_3806266) baseStart_3806266 baseEnd_3806266 := by
    simpa [prefixWord, tailWord_3806266, baseEnd_3806266] using wordTrace_append hprefix tailTrace_3806266
  have hstable : (prefixWord ++ tailWord_3806266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806266).length < 2 ^ (prefixWord ++ tailWord_3806266).sum := by decide
  have hdescent : baseEnd_3806266 < baseStart_3806266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806280 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 1, 4]
def baseStart_3806280 : Nat := 118140960795 + 3806280 * 2 ^ 59
def prefixEnd_3806280 : Nat := 4983230072969 + 3 ^ 40 * 3806280 * 2
def baseEnd_3806280 : Nat := 651483715198491048565081

theorem tailTrace_3806280 : CollatzResearch.WordTrace tailWord_3806280 prefixEnd_3806280 651483715198491048565081 := by
  unfold tailWord_3806280
  simp only [CollatzResearch.WordTrace]
  refine ⟨69413218325252547857560147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92550957767003397143413529 69413218325252547857560147)
  ·
    refine ⟨104119827487878821786340221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69413218325252547857560147 104119827487878821786340221)
    ·
      refine ⟨39044935307954558169877583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104119827487878821786340221 39044935307954558169877583)
      ·
        refine ⟨58567402961931837254816375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39044935307954558169877583 58567402961931837254816375)
        ·
          refine ⟨87851104442897755882224563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58567402961931837254816375 87851104442897755882224563)
          ·
            refine ⟨131776656664346633823336845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87851104442897755882224563 131776656664346633823336845)
            ·
              refine ⟨49416246249129987683751317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131776656664346633823336845 49416246249129987683751317)
              ·
                refine ⟨2316386542927968172675843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49416246249129987683751317 2316386542927968172675843)
                ·
                  refine ⟨3474579814391952259013765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316386542927968172675843 3474579814391952259013765)
                  ·
                    refine ⟨651483715198491048565081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474579814391952259013765 651483715198491048565081)
                    ·
                      rfl

theorem cell23_3806280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_3806280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806280 prefixEnd_3806280 := by exact prefixLift 3806280
  have htrace : WordTrace (prefixWord ++ tailWord_3806280) baseStart_3806280 baseEnd_3806280 := by
    simpa [prefixWord, tailWord_3806280, baseEnd_3806280] using wordTrace_append hprefix tailTrace_3806280
  have hstable : (prefixWord ++ tailWord_3806280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806280).length < 2 ^ (prefixWord ++ tailWord_3806280).sum := by decide
  have hdescent : baseEnd_3806280 < baseStart_3806280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806296 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3806296 : Nat := 118140960795 + 3806296 * 2 ^ 59
def prefixEnd_3806296 : Nat := 4983230072969 + 3 ^ 40 * 3806296 * 2
def baseEnd_3806296 : Nat := 1954459361285945083095169

theorem tailTrace_3806296 : CollatzResearch.WordTrace tailWord_3806296 prefixEnd_3806296 1954459361285945083095169 := by
  unfold tailWord_3806296
  simp only [CollatzResearch.WordTrace]
  refine ⟨69413510109223565223851371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92551346812298086965135161 69413510109223565223851371)
  ·
    refine ⟨104120265163835347835777057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69413510109223565223851371 104120265163835347835777057)
    ·
      refine ⟨78090198872876510876832793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104120265163835347835777057 78090198872876510876832793)
      ·
        refine ⟨58567649154657383157624595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78090198872876510876832793 58567649154657383157624595)
        ·
          refine ⟨87851473731986074736436893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58567649154657383157624595 87851473731986074736436893)
          ·
            refine ⟨32944302649494778026163835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87851473731986074736436893 32944302649494778026163835)
            ·
              refine ⟨49416453974242167039245753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32944302649494778026163835 49416453974242167039245753)
              ·
                refine ⟨37062340480681625279434315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49416453974242167039245753 37062340480681625279434315)
                ·
                  refine ⟨55593510721022437919151473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37062340480681625279434315 55593510721022437919151473)
                  ·
                    refine ⟨41695133040766828439363605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55593510721022437919151473 41695133040766828439363605)
                    ·
                      refine ⟨1954459361285945083095169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41695133040766828439363605 1954459361285945083095169)
                      ·
                        rfl

theorem cell23_3806296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3806296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806296 prefixEnd_3806296 := by exact prefixLift 3806296
  have htrace : WordTrace (prefixWord ++ tailWord_3806296) baseStart_3806296 baseEnd_3806296 := by
    simpa [prefixWord, tailWord_3806296, baseEnd_3806296] using wordTrace_append hprefix tailTrace_3806296
  have hstable : (prefixWord ++ tailWord_3806296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806296).length < 2 ^ (prefixWord ++ tailWord_3806296).sum := by decide
  have hdescent : baseEnd_3806296 < baseStart_3806296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806314 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3806314 : Nat := 118140960795 + 3806314 * 2 ^ 59
def prefixEnd_3806314 : Nat := 4983230072969 + 3 ^ 40 * 3806314 * 2
def baseEnd_3806314 : Nat := 651489534645908670890029

theorem tailTrace_3806314 : CollatzResearch.WordTrace tailWord_3806314 prefixEnd_3806314 651489534645908670890029 := by
  unfold tailWord_3806314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34706919183095479880464499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92551784488254613014571997 34706919183095479880464499)
  ·
    refine ⟨52060378774643219820696749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34706919183095479880464499 52060378774643219820696749)
    ·
      refine ⟨19522642040491207432761281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52060378774643219820696749 19522642040491207432761281)
      ·
        refine ⟨14641981530368405574570961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19522642040491207432761281 14641981530368405574570961)
        ·
          refine ⟨10981486147776304180928221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14641981530368405574570961 10981486147776304180928221)
          ·
            refine ⟨4118057305416114067848083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10981486147776304180928221 4118057305416114067848083)
            ·
              refine ⟨6177085958124171101772125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118057305416114067848083 6177085958124171101772125)
              ·
                refine ⟨2316407234296564163164547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6177085958124171101772125 2316407234296564163164547)
                ·
                  refine ⟨3474610851444846244746821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316407234296564163164547 3474610851444846244746821)
                  ·
                    refine ⟨651489534645908670890029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474610851444846244746821 651489534645908670890029)
                    ·
                      rfl

theorem cell23_3806314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3806314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806314 prefixEnd_3806314 := by exact prefixLift 3806314
  have htrace : WordTrace (prefixWord ++ tailWord_3806314) baseStart_3806314 baseEnd_3806314 := by
    simpa [prefixWord, tailWord_3806314, baseEnd_3806314] using wordTrace_append hprefix tailTrace_3806314
  have hstable : (prefixWord ++ tailWord_3806314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806314).length < 2 ^ (prefixWord ++ tailWord_3806314).sum := by decide
  have hdescent : baseEnd_3806314 < baseStart_3806314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806337 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3806337 : Nat := 118140960795 + 3806337 * 2 ^ 59
def prefixEnd_3806337 : Nat := 4983230072969 + 3 ^ 40 * 3806337 * 2
def baseEnd_3806337 : Nat := 1954480413992779422682481

theorem tailTrace_3806337 : CollatzResearch.WordTrace tailWord_3806337 prefixEnd_3806337 1954480413992779422682481 := by
  unfold tailWord_3806337
  simp only [CollatzResearch.WordTrace]
  refine ⟨138828515611298594449945265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92552343740865729633296843 138828515611298594449945265)
  ·
    refine ⟨104121386708473945837458949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138828515611298594449945265 104121386708473945837458949)
    ·
      refine ⟨19522760007838864844523553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104121386708473945837458949 19522760007838864844523553)
      ·
        refine ⟨14642070005879148633392665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19522760007838864844523553 14642070005879148633392665)
        ·
          refine ⟨10981552504409361475044499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14642070005879148633392665 10981552504409361475044499)
          ·
            refine ⟨16472328756614042212566749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10981552504409361475044499 16472328756614042212566749)
            ·
              refine ⟨6177123283730265829712531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16472328756614042212566749 6177123283730265829712531)
              ·
                refine ⟨9265684925595398744568797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177123283730265829712531 9265684925595398744568797)
                ·
                  refine ⟨3474631847098274529213299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9265684925595398744568797 3474631847098274529213299)
                  ·
                    refine ⟨5211947770647411793819949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474631847098274529213299 5211947770647411793819949)
                    ·
                      refine ⟨1954480413992779422682481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5211947770647411793819949 1954480413992779422682481)
                      ·
                        rfl

theorem cell23_3806337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3806337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806337 prefixEnd_3806337 := by exact prefixLift 3806337
  have htrace : WordTrace (prefixWord ++ tailWord_3806337) baseStart_3806337 baseEnd_3806337 := by
    simpa [prefixWord, tailWord_3806337, baseEnd_3806337] using wordTrace_append hprefix tailTrace_3806337
  have hstable : (prefixWord ++ tailWord_3806337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806337).length < 2 ^ (prefixWord ++ tailWord_3806337).sum := by decide
  have hdescent : baseEnd_3806337 < baseStart_3806337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806343 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3806343 : Nat := 118140960795 + 3806343 * 2 ^ 59
def prefixEnd_3806343 : Nat := 4983230072969 + 3 ^ 40 * 3806343 * 2
def baseEnd_3806343 : Nat := 1954483494876706399207453

theorem tailTrace_3806343 : CollatzResearch.WordTrace tailWord_3806343 prefixEnd_3806343 1954483494876706399207453 := by
  unfold tailWord_3806343
  simp only [CollatzResearch.WordTrace]
  refine ⟨138828734449276857474663683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92552489632851238316442455 138828734449276857474663683)
  ·
    refine ⟨208243101673915286211995525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138828734449276857474663683 208243101673915286211995525)
    ·
      refine ⟨39045581563859116164749161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208243101673915286211995525 39045581563859116164749161)
      ·
        refine ⟨29284186172894337123561871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39045581563859116164749161 29284186172894337123561871)
        ·
          refine ⟨43926279259341505685342807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29284186172894337123561871 43926279259341505685342807)
          ·
            refine ⟨65889418889012258528014211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43926279259341505685342807 65889418889012258528014211)
            ·
              refine ⟨98834128333518387792021317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65889418889012258528014211 98834128333518387792021317)
              ·
                refine ⟨18531399062534697711003997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98834128333518387792021317 18531399062534697711003997)
                ·
                  refine ⟨6949274648450511641626499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18531399062534697711003997 6949274648450511641626499)
                  ·
                    refine ⟨10423911972675767462439749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949274648450511641626499 10423911972675767462439749)
                    ·
                      refine ⟨1954483494876706399207453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10423911972675767462439749 1954483494876706399207453)
                      ·
                        rfl

theorem cell23_3806343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3806343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806343 prefixEnd_3806343 := by exact prefixLift 3806343
  have htrace : WordTrace (prefixWord ++ tailWord_3806343) baseStart_3806343 baseEnd_3806343 := by
    simpa [prefixWord, tailWord_3806343, baseEnd_3806343] using wordTrace_append hprefix tailTrace_3806343
  have hstable : (prefixWord ++ tailWord_3806343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806343).length < 2 ^ (prefixWord ++ tailWord_3806343).sum := by decide
  have hdescent : baseEnd_3806343 < baseStart_3806343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806344 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 6]
def baseStart_3806344 : Nat := 118140960795 + 3806344 * 2 ^ 59
def prefixEnd_3806344 : Nat := 4983230072969 + 3 ^ 40 * 3806344 * 2
def baseEnd_3806344 : Nat := 217164889817484543921661

theorem tailTrace_3806344 : CollatzResearch.WordTrace tailWord_3806344 prefixEnd_3806344 217164889817484543921661 := by
  unfold tailWord_3806344
  simp only [CollatzResearch.WordTrace]
  refine ⟨69414385461136617322725043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92552513948182156430300057 69414385461136617322725043)
  ·
    refine ⟨104121578191704925984087565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69414385461136617322725043 104121578191704925984087565)
    ·
      refine ⟨39045591821889347244032837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104121578191704925984087565 39045591821889347244032837)
      ·
        refine ⟨7321048466604252608256157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39045591821889347244032837 7321048466604252608256157)
        ·
          refine ⟨2745393174976594728096059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7321048466604252608256157 2745393174976594728096059)
          ·
            refine ⟨4118089762464892092144089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745393174976594728096059 4118089762464892092144089)
            ·
              refine ⟨3088567321848669069108067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118089762464892092144089 3088567321848669069108067)
              ·
                refine ⟨4632850982773003603662101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088567321848669069108067 4632850982773003603662101)
                ·
                  refine ⟨217164889817484543921661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4632850982773003603662101 217164889817484543921661)
                  ·
                    rfl

theorem cell23_3806344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 6].length) (baseStart_3806344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806344 prefixEnd_3806344 := by exact prefixLift 3806344
  have htrace : WordTrace (prefixWord ++ tailWord_3806344) baseStart_3806344 baseEnd_3806344 := by
    simpa [prefixWord, tailWord_3806344, baseEnd_3806344] using wordTrace_append hprefix tailTrace_3806344
  have hstable : (prefixWord ++ tailWord_3806344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806344).length < 2 ^ (prefixWord ++ tailWord_3806344).sum := by decide
  have hdescent : baseEnd_3806344 < baseStart_3806344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806360 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3806360 : Nat := 118140960795 + 3806360 * 2 ^ 59
def prefixEnd_3806360 : Nat := 4983230072969 + 3 ^ 40 * 3806360 * 2
def baseEnd_3806360 : Nat := 1954492224047832832694875

theorem tailTrace_3806360 : CollatzResearch.WordTrace tailWord_3806360 prefixEnd_3806360 1954492224047832832694875 := by
  unfold tailWord_3806360
  simp only [CollatzResearch.WordTrace]
  refine ⟨69414677245107634689016267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92552902993476846252021689 69414677245107634689016267)
  ·
    refine ⟨104122015867661452033524401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69414677245107634689016267 104122015867661452033524401)
    ·
      refine ⟨78091511900746089025143301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104122015867661452033524401 78091511900746089025143301)
      ·
        refine ⟨14642158481389891692214369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78091511900746089025143301 14642158481389891692214369)
        ·
          refine ⟨10981618861042418769160777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14642158481389891692214369 10981618861042418769160777)
          ·
            refine ⟨8236214145781814076870583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10981618861042418769160777 8236214145781814076870583)
            ·
              refine ⟨12354321218672721115305875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236214145781814076870583 12354321218672721115305875)
              ·
                refine ⟨18531481828009081672958813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12354321218672721115305875 18531481828009081672958813)
                ·
                  refine ⟨6949305685503405627359555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18531481828009081672958813 6949305685503405627359555)
                  ·
                    refine ⟨10423958528255108441039333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949305685503405627359555 10423958528255108441039333)
                    ·
                      refine ⟨1954492224047832832694875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10423958528255108441039333 1954492224047832832694875)
                      ·
                        rfl

theorem cell23_3806360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3806360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806360 prefixEnd_3806360 := by exact prefixLift 3806360
  have htrace : WordTrace (prefixWord ++ tailWord_3806360) baseStart_3806360 baseEnd_3806360 := by
    simpa [prefixWord, tailWord_3806360, baseEnd_3806360] using wordTrace_append hprefix tailTrace_3806360
  have hstable : (prefixWord ++ tailWord_3806360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806360).length < 2 ^ (prefixWord ++ tailWord_3806360).sum := by decide
  have hdescent : baseEnd_3806360 < baseStart_3806360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806373 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3806373 : Nat := 118140960795 + 3806373 * 2 ^ 59
def prefixEnd_3806373 : Nat := 4983230072969 + 3 ^ 40 * 3806373 * 2
def baseEnd_3806373 : Nat := 1954498899296341281832315

theorem tailTrace_3806373 : CollatzResearch.WordTrace tailWord_3806373 prefixEnd_3806373 1954498899296341281832315 := by
  unfold tailWord_3806373
  simp only [CollatzResearch.WordTrace]
  refine ⟨138829828639168172598255773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92553219092778781732170515 138829828639168172598255773)
  ·
    refine ⟨52061185739688064724345915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138829828639168172598255773 52061185739688064724345915)
    ·
      refine ⟨78091778609532097086518873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52061185739688064724345915 78091778609532097086518873)
      ·
        refine ⟨58568833957149072814889155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78091778609532097086518873 58568833957149072814889155)
        ·
          refine ⟨87853250935723609222333733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58568833957149072814889155 87853250935723609222333733)
          ·
            refine ⟨16472484550448176729187575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87853250935723609222333733 16472484550448176729187575)
            ·
              refine ⟨24708726825672265093781363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472484550448176729187575 24708726825672265093781363)
              ·
                refine ⟨37063090238508397640672045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24708726825672265093781363 37063090238508397640672045)
                ·
                  refine ⟨13898658839440649115252017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37063090238508397640672045 13898658839440649115252017)
                  ·
                    refine ⟨10423994129580486836439013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13898658839440649115252017 10423994129580486836439013)
                    ·
                      refine ⟨1954498899296341281832315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10423994129580486836439013 1954498899296341281832315)
                      ·
                        rfl

theorem cell23_3806373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3806373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806373 prefixEnd_3806373 := by exact prefixLift 3806373
  have htrace : WordTrace (prefixWord ++ tailWord_3806373) baseStart_3806373 baseEnd_3806373 := by
    simpa [prefixWord, tailWord_3806373, baseEnd_3806373] using wordTrace_append hprefix tailTrace_3806373
  have hstable : (prefixWord ++ tailWord_3806373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806373).length < 2 ^ (prefixWord ++ tailWord_3806373).sum := by decide
  have hdescent : baseEnd_3806373 < baseStart_3806373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806400 : List Nat := [2, 1, 1, 2, 6, 2, 1, 8]
def baseStart_3806400 : Nat := 118140960795 + 3806400 * 2 ^ 59
def prefixEnd_3806400 : Nat := 4983230072969 + 3 ^ 40 * 3806400 * 2
def baseEnd_3806400 : Nat := 72389361602741210229433

theorem tailTrace_3806400 : CollatzResearch.WordTrace tailWord_3806400 prefixEnd_3806400 72389361602741210229433 := by
  unfold tailWord_3806400
  simp only [CollatzResearch.WordTrace]
  refine ⟨69415406705035178104744327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92553875606713570806325769 69415406705035178104744327)
  ·
    refine ⟨104123110057552767157116491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69415406705035178104744327 104123110057552767157116491)
    ·
      refine ⟨156184665086329150735674737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104123110057552767157116491 156184665086329150735674737)
      ·
        refine ⟨117138498814746863051756053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156184665086329150735674737 117138498814746863051756053)
        ·
          refine ⟨5490867131941259205551065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117138498814746863051756053 5490867131941259205551065)
          ·
            refine ⟨4118150348955944404163299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5490867131941259205551065 4118150348955944404163299)
            ·
              refine ⟨6177225523433916606244949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118150348955944404163299 6177225523433916606244949)
              ·
                refine ⟨72389361602741210229433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6177225523433916606244949 72389361602741210229433)
                ·
                  rfl

theorem cell23_3806400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 8].length) (baseStart_3806400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806400 prefixEnd_3806400 := by exact prefixLift 3806400
  have htrace : WordTrace (prefixWord ++ tailWord_3806400) baseStart_3806400 baseEnd_3806400 := by
    simpa [prefixWord, tailWord_3806400, baseEnd_3806400] using wordTrace_append hprefix tailTrace_3806400
  have hstable : (prefixWord ++ tailWord_3806400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806400).length < 2 ^ (prefixWord ++ tailWord_3806400).sum := by decide
  have hdescent : baseEnd_3806400 < baseStart_3806400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806410 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_3806410 : Nat := 118140960795 + 3806410 * 2 ^ 59
def prefixEnd_3806410 : Nat := 4983230072969 + 3 ^ 40 * 3806410 * 2
def baseEnd_3806410 : Nat := 1954517898080557637069645

theorem tailTrace_3806410 : CollatzResearch.WordTrace tailWord_3806410 prefixEnd_3806410 1954517898080557637069645 := by
  unfold tailWord_3806410
  simp only [CollatzResearch.WordTrace]
  refine ⟨34707794535008531979338171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92554118760022751944901789 34707794535008531979338171)
  ·
    refine ⟨52061691802512797969007257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34707794535008531979338171 52061691802512797969007257)
    ·
      refine ⟨39046268851884598476755443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52061691802512797969007257 39046268851884598476755443)
      ·
        refine ⟨58569403277826897715133165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39046268851884598476755443 58569403277826897715133165)
        ·
          refine ⟨21963526229185086643174937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58569403277826897715133165 21963526229185086643174937)
          ·
            refine ⟨16472644671888814982381203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21963526229185086643174937 16472644671888814982381203)
            ·
              refine ⟨24708967007833222473571805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472644671888814982381203 24708967007833222473571805)
              ·
                refine ⟨9265862627937458427589427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24708967007833222473571805 9265862627937458427589427)
                ·
                  refine ⟨13898793941906187641384141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9265862627937458427589427 13898793941906187641384141)
                  ·
                    refine ⟨5212047728214820365519053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13898793941906187641384141 5212047728214820365519053)
                    ·
                      refine ⟨1954517898080557637069645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212047728214820365519053 1954517898080557637069645)
                      ·
                        rfl

theorem cell23_3806410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_3806410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806410 prefixEnd_3806410 := by exact prefixLift 3806410
  have htrace : WordTrace (prefixWord ++ tailWord_3806410) baseStart_3806410 baseEnd_3806410 := by
    simpa [prefixWord, tailWord_3806410, baseEnd_3806410] using wordTrace_append hprefix tailTrace_3806410
  have hstable : (prefixWord ++ tailWord_3806410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806410).length < 2 ^ (prefixWord ++ tailWord_3806410).sum := by decide
  have hdescent : baseEnd_3806410 < baseStart_3806410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806443 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 2, 6]
def baseStart_3806443 : Nat := 118140960795 + 3806443 * 2 ^ 59
def prefixEnd_3806443 : Nat := 4983230072969 + 3 ^ 40 * 3806443 * 2
def baseEnd_3806443 : Nat := 651511614314052002652331

theorem tailTrace_3806443 : CollatzResearch.WordTrace tailWord_3806443 prefixEnd_3806443 651511614314052002652331 := by
  unfold tailWord_3806443
  simp only [CollatzResearch.WordTrace]
  refine ⟨138832381748914574553303983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92554921165943049702202655 138832381748914574553303983)
  ·
    refine ⟨208248572623371861829955975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138832381748914574553303983 208248572623371861829955975)
    ·
      refine ⟨312372858935057792744933963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208248572623371861829955975 312372858935057792744933963)
      ·
        refine ⟨468559288402586689117400945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312372858935057792744933963 468559288402586689117400945)
        ·
          refine ⟨351419466301940016838050709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468559288402586689117400945 351419466301940016838050709)
          ·
            refine ⟨16472787482903438289283627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351419466301940016838050709 16472787482903438289283627)
            ·
              refine ⟨24709181224355157433925441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472787482903438289283627 24709181224355157433925441)
              ·
                refine ⟨18531885918266368075444081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24709181224355157433925441 18531885918266368075444081)
                ·
                  refine ⟨13898914438699776056583061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18531885918266368075444081 13898914438699776056583061)
                  ·
                    refine ⟨651511614314052002652331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13898914438699776056583061 651511614314052002652331)
                    ·
                      rfl

theorem cell23_3806443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_3806443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806443 prefixEnd_3806443 := by exact prefixLift 3806443
  have htrace : WordTrace (prefixWord ++ tailWord_3806443) baseStart_3806443 baseEnd_3806443 := by
    simpa [prefixWord, tailWord_3806443, baseEnd_3806443] using wordTrace_append hprefix tailTrace_3806443
  have hstable : (prefixWord ++ tailWord_3806443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806443).length < 2 ^ (prefixWord ++ tailWord_3806443).sum := by decide
  have hdescent : baseEnd_3806443 < baseStart_3806443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806444 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_3806444 : Nat := 118140960795 + 3806444 * 2 ^ 59
def prefixEnd_3806444 : Nat := 4983230072969 + 3 ^ 40 * 3806444 * 2
def baseEnd_3806444 : Nat := 1954535356422810504044489

theorem tailTrace_3806444 : CollatzResearch.WordTrace tailWord_3806444 prefixEnd_3806444 1954535356422810504044489 := by
  unfold tailWord_3806444
  simp only [CollatzResearch.WordTrace]
  refine ⟨69416209110955475862045193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92554945481273967816060257 69416209110955475862045193)
  ·
    refine ⟨52062156833216606896533895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69416209110955475862045193 52062156833216606896533895)
    ·
      refine ⟨78093235249824910344800843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52062156833216606896533895 78093235249824910344800843)
      ·
        refine ⟨117139852874737365517201265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78093235249824910344800843 117139852874737365517201265)
        ·
          refine ⟨87854889656053024137900949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117139852874737365517201265 87854889656053024137900949)
          ·
            refine ⟨4118197952627485506464107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87854889656053024137900949 4118197952627485506464107)
            ·
              refine ⟨6177296928941228259696161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118197952627485506464107 6177296928941228259696161)
              ·
                refine ⟨4632972696705921194772121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177296928941228259696161 4632972696705921194772121)
                ·
                  refine ⟨3474729522529440896079091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4632972696705921194772121 3474729522529440896079091)
                  ·
                    refine ⟨5212094283794161344118637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474729522529440896079091 5212094283794161344118637)
                    ·
                      refine ⟨1954535356422810504044489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212094283794161344118637 1954535356422810504044489)
                      ·
                        rfl

theorem cell23_3806444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_3806444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806444 prefixEnd_3806444 := by exact prefixLift 3806444
  have htrace : WordTrace (prefixWord ++ tailWord_3806444) baseStart_3806444 baseEnd_3806444 := by
    simpa [prefixWord, tailWord_3806444, baseEnd_3806444] using wordTrace_append hprefix tailTrace_3806444
  have hstable : (prefixWord ++ tailWord_3806444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806444).length < 2 ^ (prefixWord ++ tailWord_3806444).sum := by decide
  have hdescent : baseEnd_3806444 < baseStart_3806444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806467 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 1, 4, 2]
def baseStart_3806467 : Nat := 118140960795 + 3806467 * 2 ^ 59
def prefixEnd_3806467 : Nat := 4983230072969 + 3 ^ 40 * 3806467 * 2
def baseEnd_3806467 : Nat := 1954547166477863914056883

theorem tailTrace_3806467 : CollatzResearch.WordTrace tailWord_3806467 prefixEnd_3806467 1954547166477863914056883 := by
  unfold tailWord_3806467
  simp only [CollatzResearch.WordTrace]
  refine ⟨138833257100827626652177655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92555504733885084434785103 138833257100827626652177655)
  ·
    refine ⟨208249885651241439978266483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138833257100827626652177655 208249885651241439978266483)
    ·
      refine ⟨312374828476862159967399725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208249885651241439978266483 312374828476862159967399725)
      ·
        refine ⟨117140560678823309987774897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312374828476862159967399725 117140560678823309987774897)
        ·
          refine ⟨87855420509117482490831173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117140560678823309987774897 87855420509117482490831173)
          ·
            refine ⟨16472891345459527967030845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87855420509117482490831173 16472891345459527967030845)
            ·
              refine ⟨6177334254547322987636567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16472891345459527967030845 6177334254547322987636567)
              ·
                refine ⟨9266001381820984481454851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177334254547322987636567 9266001381820984481454851)
                ·
                  refine ⟨13899002072731476722182277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266001381820984481454851 13899002072731476722182277)
                  ·
                    refine ⟨2606062888637151885409177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13899002072731476722182277 2606062888637151885409177)
                    ·
                      refine ⟨1954547166477863914056883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606062888637151885409177 1954547166477863914056883)
                      ·
                        rfl

theorem cell23_3806467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_3806467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806467 prefixEnd_3806467 := by exact prefixLift 3806467
  have htrace : WordTrace (prefixWord ++ tailWord_3806467) baseStart_3806467 baseEnd_3806467 := by
    simpa [prefixWord, tailWord_3806467, baseEnd_3806467] using wordTrace_append hprefix tailTrace_3806467
  have hstable : (prefixWord ++ tailWord_3806467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806467).length < 2 ^ (prefixWord ++ tailWord_3806467).sum := by decide
  have hdescent : baseEnd_3806467 < baseStart_3806467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806473 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 7]
def baseStart_3806473 : Nat := 118140960795 + 3806473 * 2 ^ 59
def prefixEnd_3806473 : Nat := 4983230072969 + 3 ^ 40 * 3806473 * 2
def baseEnd_3806473 : Nat := 217172249706865654509095

theorem tailTrace_3806473 : CollatzResearch.WordTrace tailWord_3806473 prefixEnd_3806473 217172249706865654509095 := by
  unfold tailWord_3806473
  simp only [CollatzResearch.WordTrace]
  refine ⟨138833475938805889676896073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92555650625870593117930715 138833475938805889676896073)
  ·
    refine ⟨104125106954104417257672055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138833475938805889676896073 104125106954104417257672055)
    ·
      refine ⟨156187660431156625886508083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104125106954104417257672055 156187660431156625886508083)
      ·
        refine ⟨234281490646734938829762125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156187660431156625886508083 234281490646734938829762125)
        ·
          refine ⟨87855558992525602061160797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234281490646734938829762125 87855558992525602061160797)
          ·
            refine ⟨32945834622197100772935299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87855558992525602061160797 32945834622197100772935299)
            ·
              refine ⟨49418751933295651159402949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32945834622197100772935299 49418751933295651159402949)
              ·
                refine ⟨9266015987492934592388053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49418751933295651159402949 9266015987492934592388053)
                ·
                  refine ⟨217172249706865654509095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9266015987492934592388053 217172249706865654509095)
                  ·
                    rfl

theorem cell23_3806473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_3806473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806473 prefixEnd_3806473 := by exact prefixLift 3806473
  have htrace : WordTrace (prefixWord ++ tailWord_3806473) baseStart_3806473 baseEnd_3806473 := by
    simpa [prefixWord, tailWord_3806473, baseEnd_3806473] using wordTrace_append hprefix tailTrace_3806473
  have hstable : (prefixWord ++ tailWord_3806473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806473).length < 2 ^ (prefixWord ++ tailWord_3806473).sum := by decide
  have hdescent : baseEnd_3806473 < baseStart_3806473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806533 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3806533 : Nat := 118140960795 + 3806533 * 2 ^ 59
def prefixEnd_3806533 : Nat := 4983230072969 + 3 ^ 40 * 3806533 * 2
def baseEnd_3806533 : Nat := 651527018733686885277193

theorem tailTrace_3806533 : CollatzResearch.WordTrace tailWord_3806533 prefixEnd_3806533 651527018733686885277193 := by
  unfold tailWord_3806533
  simp only [CollatzResearch.WordTrace]
  refine ⟨138835664318588519924080253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92557109545725679949386835 138835664318588519924080253)
  ·
    refine ⟨52063374119470694971530095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138835664318588519924080253 52063374119470694971530095)
    ·
      refine ⟨78095061179206042457295143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52063374119470694971530095 78095061179206042457295143)
      ·
        refine ⟨117142591768809063685942715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78095061179206042457295143 117142591768809063685942715)
        ·
          refine ⟨175713887653213595528914073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117142591768809063685942715 175713887653213595528914073)
          ·
            refine ⟨131785415739910196646685555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175713887653213595528914073 131785415739910196646685555)
            ·
              refine ⟨197678123609865294970028333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131785415739910196646685555 197678123609865294970028333)
              ·
                refine ⟨74129296353699485613760625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197678123609865294970028333 74129296353699485613760625)
                ·
                  refine ⟨55596972265274614210320469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74129296353699485613760625 55596972265274614210320469)
                  ·
                    refine ⟨651527018733686885277193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55596972265274614210320469 651527018733686885277193)
                    ·
                      rfl

theorem cell23_3806533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3806533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806533 prefixEnd_3806533 := by exact prefixLift 3806533
  have htrace : WordTrace (prefixWord ++ tailWord_3806533) baseStart_3806533 baseEnd_3806533 := by
    simpa [prefixWord, tailWord_3806533, baseEnd_3806533] using wordTrace_append hprefix tailTrace_3806533
  have hstable : (prefixWord ++ tailWord_3806533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806533).length < 2 ^ (prefixWord ++ tailWord_3806533).sum := by decide
  have hdescent : baseEnd_3806533 < baseStart_3806533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806601 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 1, 4]
def baseStart_3806601 : Nat := 118140960795 + 3806601 * 2 ^ 59
def prefixEnd_3806601 : Nat := 4983230072969 + 3 ^ 40 * 3806601 * 2
def baseEnd_3806601 : Nat := 651538657628522129927089

theorem tailTrace_3806601 : CollatzResearch.WordTrace tailWord_3806601 prefixEnd_3806601 651538657628522129927089 := by
  unfold tailWord_3806601
  simp only [CollatzResearch.WordTrace]
  refine ⟨138838144482342167537555657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92558762988228111691703771 138838144482342167537555657)
  ·
    refine ⟨104128608361756625653166743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138838144482342167537555657 104128608361756625653166743)
    ·
      refine ⟨156192912542634938479750115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104128608361756625653166743 156192912542634938479750115)
      ·
        refine ⟨234289368813952407719625173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156192912542634938479750115 234289368813952407719625173)
        ·
          refine ⟨5491157081577009555928715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 234289368813952407719625173 5491157081577009555928715)
          ·
            refine ⟨8236735622365514333893073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491157081577009555928715 8236735622365514333893073)
            ·
              refine ⟨6177551716774135750419805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8236735622365514333893073 6177551716774135750419805)
              ·
                refine ⟨2316581893790300906407427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6177551716774135750419805 2316581893790300906407427)
                ·
                  refine ⟨3474872840685451359611141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316581893790300906407427 3474872840685451359611141)
                  ·
                    refine ⟨651538657628522129927089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474872840685451359611141 651538657628522129927089)
                    ·
                      rfl

theorem cell23_3806601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 4].length) (baseStart_3806601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806601 prefixEnd_3806601 := by exact prefixLift 3806601
  have htrace : WordTrace (prefixWord ++ tailWord_3806601) baseStart_3806601 baseEnd_3806601 := by
    simpa [prefixWord, tailWord_3806601, baseEnd_3806601] using wordTrace_append hprefix tailTrace_3806601
  have hstable : (prefixWord ++ tailWord_3806601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806601).length < 2 ^ (prefixWord ++ tailWord_3806601).sum := by decide
  have hdescent : baseEnd_3806601 < baseStart_3806601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806624 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 3, 1, 3]
def baseStart_3806624 : Nat := 118140960795 + 3806624 * 2 ^ 59
def prefixEnd_3806624 : Nat := 4983230072969 + 3 ^ 40 * 3806624 * 2
def baseEnd_3806624 : Nat := 1954627782940619799793661

theorem tailTrace_3806624 : CollatzResearch.WordTrace tailWord_3806624 prefixEnd_3806624 1954627782940619799793661 := by
  unfold tailWord_3806624
  simp only [CollatzResearch.WordTrace]
  refine ⟨69419491680629421232821463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92559322240839228310428617 69419491680629421232821463)
  ·
    refine ⟨104129237520944131849232195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69419491680629421232821463 104129237520944131849232195)
    ·
      refine ⟨156193856281416197773848293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104129237520944131849232195 156193856281416197773848293)
      ·
        refine ⟨29286348052765537082596555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156193856281416197773848293 29286348052765537082596555)
        ·
          refine ⟨43929522079148305623894833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29286348052765537082596555 43929522079148305623894833)
          ·
            refine ⟨32947141559361229217921125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43929522079148305623894833 32947141559361229217921125)
            ·
              refine ⟨6177589042380230478360211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32947141559361229217921125 6177589042380230478360211)
              ·
                refine ⟨9266383563570345717540317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177589042380230478360211 9266383563570345717540317)
                ·
                  refine ⟨3474893836338879644077619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9266383563570345717540317 3474893836338879644077619)
                  ·
                    refine ⟨5212340754508319466116429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474893836338879644077619 5212340754508319466116429)
                    ·
                      refine ⟨1954627782940619799793661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212340754508319466116429 1954627782940619799793661)
                      ·
                        rfl

theorem cell23_3806624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_3806624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806624 prefixEnd_3806624 := by exact prefixLift 3806624
  have htrace : WordTrace (prefixWord ++ tailWord_3806624) baseStart_3806624 baseEnd_3806624 := by
    simpa [prefixWord, tailWord_3806624, baseEnd_3806624] using wordTrace_append hprefix tailTrace_3806624
  have hstable : (prefixWord ++ tailWord_3806624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806624).length < 2 ^ (prefixWord ++ tailWord_3806624).sum := by decide
  have hdescent : baseEnd_3806624 < baseStart_3806624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806640 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_3806640 : Nat := 118140960795 + 3806640 * 2 ^ 59
def prefixEnd_3806640 : Nat := 4983230072969 + 3 ^ 40 * 3806640 * 2
def baseEnd_3806640 : Nat := 651545332877030579064529

theorem tailTrace_3806640 : CollatzResearch.WordTrace tailWord_3806640 prefixEnd_3806640 651545332877030579064529 := by
  unfold tailWord_3806640
  simp only [CollatzResearch.WordTrace]
  refine ⟨69419783464600438599112687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92559711286133918132150249 69419783464600438599112687)
  ·
    refine ⟨104129675196900657898669031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69419783464600438599112687 104129675196900657898669031)
    ·
      refine ⟨156194512795350986848003547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104129675196900657898669031 156194512795350986848003547)
      ·
        refine ⟨234291769193026480272005321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156194512795350986848003547 234291769193026480272005321)
        ·
          refine ⟨175718826894769860204003991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234291769193026480272005321 175718826894769860204003991)
          ·
            refine ⟨263578240342154790306005987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175718826894769860204003991 263578240342154790306005987)
            ·
              refine ⟨395367360513232185459008981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263578240342154790306005987 395367360513232185459008981)
              ·
                refine ⟨9266422512028879346695523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 395367360513232185459008981 9266422512028879346695523)
                ·
                  refine ⟨13899633768043319020043285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266422512028879346695523 13899633768043319020043285)
                  ·
                    refine ⟨651545332877030579064529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13899633768043319020043285 651545332877030579064529)
                    ·
                      rfl

theorem cell23_3806640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_3806640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806640 prefixEnd_3806640 := by exact prefixLift 3806640
  have htrace : WordTrace (prefixWord ++ tailWord_3806640) baseStart_3806640 baseEnd_3806640 := by
    simpa [prefixWord, tailWord_3806640, baseEnd_3806640] using wordTrace_append hprefix tailTrace_3806640
  have hstable : (prefixWord ++ tailWord_3806640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806640).length < 2 ^ (prefixWord ++ tailWord_3806640).sum := by decide
  have hdescent : baseEnd_3806640 < baseStart_3806640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806647 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 6, 2]
def baseStart_3806647 : Nat := 118140960795 + 3806647 * 2 ^ 59
def prefixEnd_3806647 : Nat := 4983230072969 + 3 ^ 40 * 3806647 * 2
def baseEnd_3806647 : Nat := 1954639592995673209806055

theorem tailTrace_3806647 : CollatzResearch.WordTrace tailWord_3806647 prefixEnd_3806647 1954639592995673209806055 := by
  unfold tailWord_3806647
  simp only [CollatzResearch.WordTrace]
  refine ⟨138839822240175517393730195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92559881493450344929153463 138839822240175517393730195)
  ·
    refine ⟨208259733360263276090595293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138839822240175517393730195 208259733360263276090595293)
    ·
      refine ⟨78097400010098728533973235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208259733360263276090595293 78097400010098728533973235)
      ·
        refine ⟨117146100015148092800959853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78097400010098728533973235 117146100015148092800959853)
        ·
          refine ⟨43929787505680534800359945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117146100015148092800959853 43929787505680534800359945)
          ·
            refine ⟨32947340629260401100269959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43929787505680534800359945 32947340629260401100269959)
            ·
              refine ⟨49421010943890601650404939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32947340629260401100269959 49421010943890601650404939)
              ·
                refine ⟨74131516415835902475607409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49421010943890601650404939 74131516415835902475607409)
                ·
                  refine ⟨55598637311876926856705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74131516415835902475607409 55598637311876926856705557)
                  ·
                    refine ⟨2606186123994230946408073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55598637311876926856705557 2606186123994230946408073)
                    ·
                      refine ⟨1954639592995673209806055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606186123994230946408073 1954639592995673209806055)
                      ·
                        rfl

theorem cell23_3806647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_3806647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806647 prefixEnd_3806647 := by exact prefixLift 3806647
  have htrace : WordTrace (prefixWord ++ tailWord_3806647) baseStart_3806647 baseEnd_3806647 := by
    simpa [prefixWord, tailWord_3806647, baseEnd_3806647] using wordTrace_append hprefix tailTrace_3806647
  have hstable : (prefixWord ++ tailWord_3806647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806647).length < 2 ^ (prefixWord ++ tailWord_3806647).sum := by decide
  have hdescent : baseEnd_3806647 < baseStart_3806647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806670 : List Nat := [4, 1, 1, 1, 2, 1, 13]
def baseStart_3806670 : Nat := 118140960795 + 3806670 * 2 ^ 59
def prefixEnd_3806670 : Nat := 4983230072969 + 3 ^ 40 * 3806670 * 2
def baseEnd_3806670 : Nat := 24131498803095390368129

theorem tailTrace_3806670 : CollatzResearch.WordTrace tailWord_3806670 prefixEnd_3806670 24131498803095390368129 := by
  unfold tailWord_3806670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355082639886524040227183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92560440746061461547878309 17355082639886524040227183)
  ·
    refine ⟨26032623959829786060340775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17355082639886524040227183 26032623959829786060340775)
    ·
      refine ⟨39048935939744679090511163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26032623959829786060340775 39048935939744679090511163)
      ·
        refine ⟨58573403909617018635766745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39048935939744679090511163 58573403909617018635766745)
        ·
          refine ⟨43930052932212763976825059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58573403909617018635766745 43930052932212763976825059)
          ·
            refine ⟨65895079398319145965237589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43930052932212763976825059 65895079398319145965237589)
            ·
              refine ⟨24131498803095390368129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 65895079398319145965237589 24131498803095390368129)
              ·
                rfl

theorem cell23_3806670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 13].length) (baseStart_3806670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806670 prefixEnd_3806670 := by exact prefixLift 3806670
  have htrace : WordTrace (prefixWord ++ tailWord_3806670) baseStart_3806670 baseEnd_3806670 := by
    simpa [prefixWord, tailWord_3806670, baseEnd_3806670] using wordTrace_append hprefix tailTrace_3806670
  have hstable : (prefixWord ++ tailWord_3806670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806670).length < 2 ^ (prefixWord ++ tailWord_3806670).sum := by decide
  have hdescent : baseEnd_3806670 < baseStart_3806670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806681 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 3, 2, 2]
def baseStart_3806681 : Nat := 118140960795 + 3806681 * 2 ^ 59
def prefixEnd_3806681 : Nat := 4983230072969 + 3 ^ 40 * 3806681 * 2
def baseEnd_3806681 : Nat := 1954657051337926076780899

theorem tailTrace_3806681 : CollatzResearch.WordTrace tailWord_3806681 prefixEnd_3806681 1954657051337926076780899 := by
  unfold tailWord_3806681
  simp only [CollatzResearch.WordTrace]
  refine ⟨138841062322052341200467897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92560708214701560800311931 138841062322052341200467897)
  ·
    refine ⟨104130796741539255900350923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138841062322052341200467897 104130796741539255900350923)
    ·
      refine ⟨156196195112308883850526385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104130796741539255900350923 156196195112308883850526385)
      ·
        refine ⟨117147146334231662887894789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156196195112308883850526385 117147146334231662887894789)
        ·
          refine ⟨21965089937668436791480273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117147146334231662887894789 21965089937668436791480273)
          ·
            refine ⟨16473817453251327593610205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21965089937668436791480273 16473817453251327593610205)
            ·
              refine ⟨6177681544969247847603827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16473817453251327593610205 6177681544969247847603827)
              ·
                refine ⟨9266522317453871771405741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177681544969247847603827 9266522317453871771405741)
                ·
                  refine ⟨3474945869045201914277153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9266522317453871771405741 3474945869045201914277153)
                  ·
                    refine ⟨2606209401783901435707865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3474945869045201914277153 2606209401783901435707865)
                    ·
                      refine ⟨1954657051337926076780899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606209401783901435707865 1954657051337926076780899)
                      ·
                        rfl

theorem cell23_3806681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_3806681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806681 prefixEnd_3806681 := by exact prefixLift 3806681
  have htrace : WordTrace (prefixWord ++ tailWord_3806681) baseStart_3806681 baseEnd_3806681 := by
    simpa [prefixWord, tailWord_3806681, baseEnd_3806681] using wordTrace_append hprefix tailTrace_3806681
  have hstable : (prefixWord ++ tailWord_3806681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806681).length < 2 ^ (prefixWord ++ tailWord_3806681).sum := by decide
  have hdescent : baseEnd_3806681 < baseStart_3806681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806691 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 2, 4]
def baseStart_3806691 : Nat := 118140960795 + 3806691 * 2 ^ 59
def prefixEnd_3806691 : Nat := 4983230072969 + 3 ^ 40 * 3806691 * 2
def baseEnd_3806691 : Nat := 651554062048157012551951

theorem tailTrace_3806691 : CollatzResearch.WordTrace tailWord_3806691 prefixEnd_3806691 651554062048157012551951 := by
  unfold tailWord_3806691
  simp only [CollatzResearch.WordTrace]
  refine ⟨138841427052016112908331927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92560951368010741938887951 138841427052016112908331927)
  ·
    refine ⟨208262140578024169362497891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138841427052016112908331927 208262140578024169362497891)
    ·
      refine ⟨312393210867036254043746837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208262140578024169362497891 312393210867036254043746837)
      ·
        refine ⟨14643431759392324408300633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312393210867036254043746837 14643431759392324408300633)
        ·
          refine ⟨10982573819544243306225475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14643431759392324408300633 10982573819544243306225475)
          ·
            refine ⟨16473860729316364959338213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982573819544243306225475 16473860729316364959338213)
            ·
              refine ⟨3088848886746818429875915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16473860729316364959338213 3088848886746818429875915)
              ·
                refine ⟨4633273330120227644813873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088848886746818429875915 4633273330120227644813873)
                ·
                  refine ⟨3474954997590170733610405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4633273330120227644813873 3474954997590170733610405)
                  ·
                    refine ⟨651554062048157012551951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474954997590170733610405 651554062048157012551951)
                    ·
                      rfl

theorem cell23_3806691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 4].length) (baseStart_3806691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806691 prefixEnd_3806691 := by exact prefixLift 3806691
  have htrace : WordTrace (prefixWord ++ tailWord_3806691) baseStart_3806691 baseEnd_3806691 := by
    simpa [prefixWord, tailWord_3806691, baseEnd_3806691] using wordTrace_append hprefix tailTrace_3806691
  have hstable : (prefixWord ++ tailWord_3806691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806691).length < 2 ^ (prefixWord ++ tailWord_3806691).sum := by decide
  have hdescent : baseEnd_3806691 < baseStart_3806691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806698 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_3806698 : Nat := 118140960795 + 3806698 * 2 ^ 59
def prefixEnd_3806698 : Nat := 4983230072969 + 3 ^ 40 * 3806698 * 2
def baseEnd_3806698 : Nat := 1954665780509052510268321

theorem tailTrace_3806698 : CollatzResearch.WordTrace tailWord_3806698 prefixEnd_3806698 1954665780509052510268321 := by
  unfold tailWord_3806698
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710420590747688275959187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92561121575327168735891165 34710420590747688275959187)
  ·
    refine ⟨52065630886121532413938781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34710420590747688275959187 52065630886121532413938781)
    ·
      refine ⟨19524611582295574655227043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52065630886121532413938781 19524611582295574655227043)
      ·
        refine ⟨29286917373443361982840565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19524611582295574655227043 29286917373443361982840565)
        ·
          refine ⟨2745648503760315185891303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29286917373443361982840565 2745648503760315185891303)
          ·
            refine ⟨4118472755640472778836955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745648503760315185891303 4118472755640472778836955)
            ·
              refine ⟨6177709133460709168255433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118472755640472778836955 6177709133460709168255433)
              ·
                refine ⟨4633281850095531876191575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177709133460709168255433 4633281850095531876191575)
                ·
                  refine ⟨6949922775143297814287363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633281850095531876191575 6949922775143297814287363)
                  ·
                    refine ⟨10424884162714946721431045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6949922775143297814287363 10424884162714946721431045)
                    ·
                      refine ⟨1954665780509052510268321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10424884162714946721431045 1954665780509052510268321)
                      ·
                        rfl

theorem cell23_3806698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_3806698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806698 prefixEnd_3806698 := by exact prefixLift 3806698
  have htrace : WordTrace (prefixWord ++ tailWord_3806698) baseStart_3806698 baseEnd_3806698 := by
    simpa [prefixWord, tailWord_3806698, baseEnd_3806698] using wordTrace_append hprefix tailTrace_3806698
  have hstable : (prefixWord ++ tailWord_3806698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806698).length < 2 ^ (prefixWord ++ tailWord_3806698).sum := by decide
  have hdescent : baseEnd_3806698 < baseStart_3806698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806700 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_3806700 : Nat := 118140960795 + 3806700 * 2 ^ 59
def prefixEnd_3806700 : Nat := 4983230072969 + 3 ^ 40 * 3806700 * 2
def baseEnd_3806700 : Nat := 651555602490120500814437

theorem tailTrace_3806700 : CollatzResearch.WordTrace tailWord_3806700 prefixEnd_3806700 651555602490120500814437 := by
  unfold tailWord_3806700
  simp only [CollatzResearch.WordTrace]
  refine ⟨69420877654491753722704777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92561170205989004963606369 69420877654491753722704777)
  ·
    refine ⟨52065658240868815292028583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69420877654491753722704777 52065658240868815292028583)
    ·
      refine ⟨78098487361303222938042875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52065658240868815292028583 78098487361303222938042875)
      ·
        refine ⟨117147731041954834407064313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78098487361303222938042875 117147731041954834407064313)
        ·
          refine ⟨87860798281466125805298235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117147731041954834407064313 87860798281466125805298235)
          ·
            refine ⟨131791197422199188707947353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87860798281466125805298235 131791197422199188707947353)
            ·
              refine ⟨98843398066649391530960515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131791197422199188707947353 98843398066649391530960515)
              ·
                refine ⟨148265097099974087296440773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98843398066649391530960515 148265097099974087296440773)
                ·
                  refine ⟨27799705706245141368082645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148265097099974087296440773 27799705706245141368082645)
                  ·
                    refine ⟨651555602490120500814437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27799705706245141368082645 651555602490120500814437)
                    ·
                      rfl

theorem cell23_3806700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_3806700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806700 prefixEnd_3806700 := by exact prefixLift 3806700
  have htrace : WordTrace (prefixWord ++ tailWord_3806700) baseStart_3806700 baseEnd_3806700 := by
    simpa [prefixWord, tailWord_3806700, baseEnd_3806700] using wordTrace_append hprefix tailTrace_3806700
  have hstable : (prefixWord ++ tailWord_3806700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806700).length < 2 ^ (prefixWord ++ tailWord_3806700).sum := by decide
  have hdescent : baseEnd_3806700 < baseStart_3806700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806701 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3806701 : Nat := 118140960795 + 3806701 * 2 ^ 59
def prefixEnd_3806701 : Nat := 4983230072969 + 3 ^ 40 * 3806701 * 2
def baseEnd_3806701 : Nat := 1954667320951015998530807

theorem tailTrace_3806701 : CollatzResearch.WordTrace tailWord_3806701 prefixEnd_3806701 1954667320951015998530807 := by
  unfold tailWord_3806701
  simp only [CollatzResearch.WordTrace]
  refine ⟨138841791781979884616195957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92561194521319923077463971 138841791781979884616195957)
  ·
    refine ⟨13016417979560614182768371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138841791781979884616195957 13016417979560614182768371)
    ·
      refine ⟨19524626969340921274152557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016417979560614182768371 19524626969340921274152557)
      ·
        refine ⟨7321735113502845477807209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19524626969340921274152557 7321735113502845477807209)
        ·
          refine ⟨5491301335127134108355407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7321735113502845477807209 5491301335127134108355407)
          ·
            refine ⟨8236952002690701162533111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491301335127134108355407 8236952002690701162533111)
            ·
              refine ⟨12355428004036051743799667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236952002690701162533111 12355428004036051743799667)
              ·
                refine ⟨18533142006054077615699501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355428004036051743799667 18533142006054077615699501)
                ·
                  refine ⟨6949928252270279105887313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18533142006054077615699501 6949928252270279105887313)
                  ·
                    refine ⟨5212446189202709329415485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6949928252270279105887313 5212446189202709329415485)
                    ·
                      refine ⟨1954667320951015998530807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212446189202709329415485 1954667320951015998530807)
                      ·
                        rfl

theorem cell23_3806701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3806701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806701 prefixEnd_3806701 := by exact prefixLift 3806701
  have htrace : WordTrace (prefixWord ++ tailWord_3806701) baseStart_3806701 baseEnd_3806701 := by
    simpa [prefixWord, tailWord_3806701, baseEnd_3806701] using wordTrace_append hprefix tailTrace_3806701
  have hstable : (prefixWord ++ tailWord_3806701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806701).length < 2 ^ (prefixWord ++ tailWord_3806701).sum := by decide
  have hdescent : baseEnd_3806701 < baseStart_3806701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806718 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3806718 : Nat := 118140960795 + 3806718 * 2 ^ 59
def prefixEnd_3806718 : Nat := 4983230072969 + 3 ^ 40 * 3806718 * 2
def baseEnd_3806718 : Nat := 1954676050122142432018229

theorem tailTrace_3806718 : CollatzResearch.WordTrace tailWord_3806718 prefixEnd_3806718 1954676050122142432018229 := by
  unfold tailWord_3806718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355301477864787064945601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92561607881945531013043205 17355301477864787064945601)
  ·
    refine ⟨13016476108398590298709201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17355301477864787064945601 13016476108398590298709201)
    ·
      refine ⟨9762357081298942724031901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13016476108398590298709201 9762357081298942724031901)
      ·
        refine ⟨3660883905487103521511963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9762357081298942724031901 3660883905487103521511963)
        ·
          refine ⟨5491325858230655282267945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660883905487103521511963 5491325858230655282267945)
          ·
            refine ⟨4118494393672991461700959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5491325858230655282267945 4118494393672991461700959)
            ·
              refine ⟨6177741590509487192551439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118494393672991461700959 6177741590509487192551439)
              ·
                refine ⟨9266612385764230788827159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177741590509487192551439 9266612385764230788827159)
                ·
                  refine ⟨13899918578646346183240739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266612385764230788827159 13899918578646346183240739)
                  ·
                    refine ⟨20849877867969519274861109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13899918578646346183240739 20849877867969519274861109)
                    ·
                      refine ⟨1954676050122142432018229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20849877867969519274861109 1954676050122142432018229)
                      ·
                        rfl

theorem cell23_3806718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3806718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806718 prefixEnd_3806718 := by exact prefixLift 3806718
  have htrace : WordTrace (prefixWord ++ tailWord_3806718) baseStart_3806718 baseEnd_3806718 := by
    simpa [prefixWord, tailWord_3806718, baseEnd_3806718] using wordTrace_append hprefix tailTrace_3806718
  have hstable : (prefixWord ++ tailWord_3806718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806718).length < 2 ^ (prefixWord ++ tailWord_3806718).sum := by decide
  have hdescent : baseEnd_3806718 < baseStart_3806718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806726 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3806726 : Nat := 118140960795 + 3806726 * 2 ^ 59
def prefixEnd_3806726 : Nat := 4983230072969 + 3 ^ 40 * 3806726 * 2
def baseEnd_3806726 : Nat := 1954680157967378400718193

theorem tailTrace_3806726 : CollatzResearch.WordTrace tailWord_3806726 prefixEnd_3806726 1954680157967378400718193 := by
  unfold tailWord_3806726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338834487715291058933001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92561802404592875923904021 4338834487715291058933001)
  ·
    refine ⟨3254125865786468294199751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4338834487715291058933001 3254125865786468294199751)
    ·
      refine ⟨4881188798679702441299627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254125865786468294199751 4881188798679702441299627)
      ·
        refine ⟨7321783198019553661949441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881188798679702441299627 7321783198019553661949441)
        ·
          refine ⟨5491337398514665246462081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7321783198019553661949441 5491337398514665246462081)
          ·
            refine ⟨4118503048885998934846561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5491337398514665246462081 4118503048885998934846561)
            ·
              refine ⟨3088877286664499201134921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118503048885998934846561 3088877286664499201134921)
              ·
                refine ⟨2316657964998374400851191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088877286664499201134921 2316657964998374400851191)
                ·
                  refine ⟨3474986947497561601276787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316657964998374400851191 3474986947497561601276787)
                  ·
                    refine ⟨5212480421246342401915181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474986947497561601276787 5212480421246342401915181)
                    ·
                      refine ⟨1954680157967378400718193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212480421246342401915181 1954680157967378400718193)
                      ·
                        rfl

theorem cell23_3806726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3806726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806726 prefixEnd_3806726 := by exact prefixLift 3806726
  have htrace : WordTrace (prefixWord ++ tailWord_3806726) baseStart_3806726 baseEnd_3806726 := by
    simpa [prefixWord, tailWord_3806726, baseEnd_3806726] using wordTrace_append hprefix tailTrace_3806726
  have hstable : (prefixWord ++ tailWord_3806726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806726).length < 2 ^ (prefixWord ++ tailWord_3806726).sum := by decide
  have hdescent : baseEnd_3806726 < baseStart_3806726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806732 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 1, 2, 2]
def baseStart_3806732 : Nat := 118140960795 + 3806732 * 2 ^ 59
def prefixEnd_3806732 : Nat := 4983230072969 + 3 ^ 40 * 3806732 * 2
def baseEnd_3806732 : Nat := 1954683238851305377243165

theorem tailTrace_3806732 : CollatzResearch.WordTrace tailWord_3806732 prefixEnd_3806732 1954683238851305377243165 := by
  unfold tailWord_3806732
  simp only [CollatzResearch.WordTrace]
  refine ⟨69421461222433788455287225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92561948296578384607049633 69421461222433788455287225)
  ·
    refine ⟨52066095916825341341465419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69421461222433788455287225 52066095916825341341465419)
    ·
      refine ⟨78099143875238012012198129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52066095916825341341465419 78099143875238012012198129)
      ·
        refine ⟨58574357906428509009148597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78099143875238012012198129 58574357906428509009148597)
        ·
          refine ⟨5491346053727672719607681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58574357906428509009148597 5491346053727672719607681)
          ·
            refine ⟨4118509540295754539705761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5491346053727672719607681 4118509540295754539705761)
            ·
              refine ⟨3088882155221815904779321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118509540295754539705761 3088882155221815904779321)
              ·
                refine ⟨2316661616416361928584491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088882155221815904779321 2316661616416361928584491)
                ·
                  refine ⟨3474992424624542892876737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316661616416361928584491 3474992424624542892876737)
                  ·
                    refine ⟨2606244318468407169657553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3474992424624542892876737 2606244318468407169657553)
                    ·
                      refine ⟨1954683238851305377243165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606244318468407169657553 1954683238851305377243165)
                      ·
                        rfl

theorem cell23_3806732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_3806732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806732 prefixEnd_3806732 := by exact prefixLift 3806732
  have htrace : WordTrace (prefixWord ++ tailWord_3806732) baseStart_3806732 baseEnd_3806732 := by
    simpa [prefixWord, tailWord_3806732, baseEnd_3806732] using wordTrace_append hprefix tailTrace_3806732
  have hstable : (prefixWord ++ tailWord_3806732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806732).length < 2 ^ (prefixWord ++ tailWord_3806732).sum := by decide
  have hdescent : baseEnd_3806732 < baseStart_3806732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806757 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_3806757 : Nat := 118140960795 + 3806757 * 2 ^ 59
def prefixEnd_3806757 : Nat := 4983230072969 + 3 ^ 40 * 3806757 * 2
def baseEnd_3806757 : Nat := 1954696075867667779430549

theorem tailTrace_3806757 : CollatzResearch.WordTrace tailWord_3806757 prefixEnd_3806757 1954696075867667779430549 := by
  unfold tailWord_3806757
  simp only [CollatzResearch.WordTrace]
  refine ⟨138843834269777006180234525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92562556179851337453489683 138843834269777006180234525)
  ·
    refine ⟨52066437851166377317587947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138843834269777006180234525 52066437851166377317587947)
    ·
      refine ⟨78099656776749565976381921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52066437851166377317587947 78099656776749565976381921)
      ·
        refine ⟨58574742582562174482286441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78099656776749565976381921 58574742582562174482286441)
        ·
          refine ⟨43931056936921630861714831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58574742582562174482286441 43931056936921630861714831)
          ·
            refine ⟨65896585405382446292572247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43931056936921630861714831 65896585405382446292572247)
            ·
              refine ⟨98844878108073669438858371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65896585405382446292572247 98844878108073669438858371)
              ·
                refine ⟨148267317162110504158287557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98844878108073669438858371 148267317162110504158287557)
                ·
                  refine ⟨27800121967895719529678917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148267317162110504158287557 27800121967895719529678917)
                  ·
                    refine ⟨5212522868980447411814797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27800121967895719529678917 5212522868980447411814797)
                    ·
                      refine ⟨1954696075867667779430549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212522868980447411814797 1954696075867667779430549)
                      ·
                        rfl

theorem cell23_3806757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_3806757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806757 prefixEnd_3806757 := by exact prefixLift 3806757
  have htrace : WordTrace (prefixWord ++ tailWord_3806757) baseStart_3806757 baseEnd_3806757 := by
    simpa [prefixWord, tailWord_3806757, baseEnd_3806757] using wordTrace_append hprefix tailTrace_3806757
  have hstable : (prefixWord ++ tailWord_3806757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806757).length < 2 ^ (prefixWord ++ tailWord_3806757).sum := by decide
  have hdescent : baseEnd_3806757 < baseStart_3806757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806794 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_3806794 : Nat := 118140960795 + 3806794 * 2 ^ 59
def prefixEnd_3806794 : Nat := 4983230072969 + 3 ^ 40 * 3806794 * 2
def baseEnd_3806794 : Nat := 217190563850209348296431

theorem tailTrace_3806794 : CollatzResearch.WordTrace tailWord_3806794 prefixEnd_3806794 217190563850209348296431 := by
  unfold tailWord_3806794
  simp only [CollatzResearch.WordTrace]
  refine ⟨34711295942660740374832859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92563455847095307666220957 34711295942660740374832859)
  ·
    refine ⟨52066943913991110562249289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34711295942660740374832859 52066943913991110562249289)
    ·
      refine ⟨39050207935493332921686967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52066943913991110562249289 39050207935493332921686967)
      ·
        refine ⟨58575311903239999382530451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39050207935493332921686967 58575311903239999382530451)
        ·
          refine ⟨87862967854859999073795677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58575311903239999382530451 87862967854859999073795677)
          ·
            refine ⟨32948612945572499652673379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87862967854859999073795677 32948612945572499652673379)
            ·
              refine ⟨49422919418358749479010069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32948612945572499652673379 49422919418358749479010069)
              ·
                refine ⟨2316699347735566381828597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49422919418358749479010069 2316699347735566381828597)
                ·
                  refine ⟨217190563850209348296431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2316699347735566381828597 217190563850209348296431)
                  ·
                    rfl

theorem cell23_3806794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_3806794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806794 prefixEnd_3806794 := by exact prefixLift 3806794
  have htrace : WordTrace (prefixWord ++ tailWord_3806794) baseStart_3806794 baseEnd_3806794 := by
    simpa [prefixWord, tailWord_3806794, baseEnd_3806794] using wordTrace_append hprefix tailTrace_3806794
  have hstable : (prefixWord ++ tailWord_3806794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806794).length < 2 ^ (prefixWord ++ tailWord_3806794).sum := by decide
  have hdescent : baseEnd_3806794 < baseStart_3806794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806804 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_3806804 : Nat := 118140960795 + 3806804 * 2 ^ 59
def prefixEnd_3806804 : Nat := 4983230072969 + 3 ^ 40 * 3806804 * 2
def baseEnd_3806804 : Nat := 1954720209458429095542833

theorem tailTrace_3806804 : CollatzResearch.WordTrace tailWord_3806804 prefixEnd_3806804 1954720209458429095542833 := by
  unfold tailWord_3806804
  simp only [CollatzResearch.WordTrace]
  refine ⟨69422774250303366603597733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92563699000404488804796977 69422774250303366603597733)
  ·
    refine ⟨13016770171931881238174575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69422774250303366603597733 13016770171931881238174575)
    ·
      refine ⟨19525155257897821857261863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016770171931881238174575 19525155257897821857261863)
      ·
        refine ⟨29287732886846732785892795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19525155257897821857261863 29287732886846732785892795)
        ·
          refine ⟨43931599330270099178839193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29287732886846732785892795 43931599330270099178839193)
          ·
            refine ⟨32948699497702574384129395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43931599330270099178839193 32948699497702574384129395)
            ·
              refine ⟨49423049246553861576194093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32948699497702574384129395 49423049246553861576194093)
              ·
                refine ⟨18533643467457698091072785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49423049246553861576194093 18533643467457698091072785)
                ·
                  refine ⟨13900232600593273568304589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18533643467457698091072785 13900232600593273568304589)
                  ·
                    refine ⟨5212587225222477588114221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13900232600593273568304589 5212587225222477588114221)
                    ·
                      refine ⟨1954720209458429095542833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212587225222477588114221 1954720209458429095542833)
                      ·
                        rfl

theorem cell23_3806804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_3806804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806804 prefixEnd_3806804 := by exact prefixLift 3806804
  have htrace : WordTrace (prefixWord ++ tailWord_3806804) baseStart_3806804 baseEnd_3806804 := by
    simpa [prefixWord, tailWord_3806804, baseEnd_3806804] using wordTrace_append hprefix tailTrace_3806804
  have hstable : (prefixWord ++ tailWord_3806804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806804).length < 2 ^ (prefixWord ++ tailWord_3806804).sum := by decide
  have hdescent : baseEnd_3806804 < baseStart_3806804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806807 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 1, 7]
def baseStart_3806807 : Nat := 118140960795 + 3806807 * 2 ^ 59
def prefixEnd_3806807 : Nat := 4983230072969 + 3 ^ 40 * 3806807 * 2
def baseEnd_3806807 : Nat := 651573916633464194601773

theorem tailTrace_3806807 : CollatzResearch.WordTrace tailWord_3806807 prefixEnd_3806807 651573916633464194601773 := by
  unfold tailWord_3806807
  simp only [CollatzResearch.WordTrace]
  refine ⟨138845657919595864719554675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92563771946397243146369783 138845657919595864719554675)
  ·
    refine ⟨208268486879393797079332013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138845657919595864719554675 208268486879393797079332013)
    ·
      refine ⟨78100682579772673904749505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208268486879393797079332013 78100682579772673904749505)
      ·
        refine ⟨58575511934829505428562129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78100682579772673904749505 58575511934829505428562129)
        ·
          refine ⟨43931633951122129071421597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58575511934829505428562129 43931633951122129071421597)
          ·
            refine ⟨16474362731670798401783099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43931633951122129071421597 16474362731670798401783099)
            ·
              refine ⟨24711544097506197602674649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474362731670798401783099 24711544097506197602674649)
              ·
                refine ⟨18533658073129648202005987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24711544097506197602674649 18533658073129648202005987)
                ·
                  refine ⟨27800487109694472303008981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18533658073129648202005987 27800487109694472303008981)
                  ·
                    refine ⟨651573916633464194601773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27800487109694472303008981 651573916633464194601773)
                    ·
                      rfl

theorem cell23_3806807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_3806807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806807 prefixEnd_3806807 := by exact prefixLift 3806807
  have htrace : WordTrace (prefixWord ++ tailWord_3806807) baseStart_3806807 baseEnd_3806807 := by
    simpa [prefixWord, tailWord_3806807, baseEnd_3806807] using wordTrace_append hprefix tailTrace_3806807
  have hstable : (prefixWord ++ tailWord_3806807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806807).length < 2 ^ (prefixWord ++ tailWord_3806807).sum := by decide
  have hdescent : baseEnd_3806807 < baseStart_3806807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806824 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3806824 : Nat := 118140960795 + 3806824 * 2 ^ 59
def prefixEnd_3806824 : Nat := 4983230072969 + 3 ^ 40 * 3806824 * 2
def baseEnd_3806824 : Nat := 651576826357173005764247

theorem tailTrace_3806824 : CollatzResearch.WordTrace tailWord_3806824 prefixEnd_3806824 651576826357173005764247 := by
  unfold tailWord_3806824
  simp only [CollatzResearch.WordTrace]
  refine ⟨69423138980267138311461763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92564185307022851081949017 69423138980267138311461763)
  ·
    refine ⟨104134708470400707467192645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69423138980267138311461763 104134708470400707467192645)
    ·
      refine ⟨19525257838200132650098621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104134708470400707467192645 19525257838200132650098621)
      ·
        refine ⟨7321971689325049743786983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19525257838200132650098621 7321971689325049743786983)
        ·
          refine ⟨10982957533987574615680475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321971689325049743786983 10982957533987574615680475)
          ·
            refine ⟨16474436300981361923520713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982957533987574615680475 16474436300981361923520713)
            ·
              refine ⟨12355827225736021442640535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16474436300981361923520713 12355827225736021442640535)
              ·
                refine ⟨18533740838604032163960803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355827225736021442640535 18533740838604032163960803)
                ·
                  refine ⟨27800611257906048245941205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18533740838604032163960803 27800611257906048245941205)
                  ·
                    refine ⟨651576826357173005764247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27800611257906048245941205 651576826357173005764247)
                    ·
                      rfl

theorem cell23_3806824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3806824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806824 prefixEnd_3806824 := by exact prefixLift 3806824
  have htrace : WordTrace (prefixWord ++ tailWord_3806824) baseStart_3806824 baseEnd_3806824 := by
    simpa [prefixWord, tailWord_3806824, baseEnd_3806824] using wordTrace_append hprefix tailTrace_3806824
  have hstable : (prefixWord ++ tailWord_3806824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806824).length < 2 ^ (prefixWord ++ tailWord_3806824).sum := by decide
  have hdescent : baseEnd_3806824 < baseStart_3806824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806857 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_3806857 : Nat := 118140960795 + 3806857 * 2 ^ 59
def prefixEnd_3806857 : Nat := 4983230072969 + 3 ^ 40 * 3806857 * 2
def baseEnd_3806857 : Nat := 1954747423933117388180089

theorem tailTrace_3806857 : CollatzResearch.WordTrace tailWord_3806857 prefixEnd_3806857 1954747423933117388180089 := by
  unfold tailWord_3806857
  simp only [CollatzResearch.WordTrace]
  refine ⟨138847481569414723258874825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92564987712943148839249883 138847481569414723258874825)
  ·
    refine ⟨104135611177061042444156119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138847481569414723258874825 104135611177061042444156119)
    ·
      refine ⟨156203416765591563666234179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104135611177061042444156119 156203416765591563666234179)
      ·
        refine ⟨234305125148387345499351269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156203416765591563666234179 234305125148387345499351269)
        ·
          refine ⟨43932210965322627281128363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234305125148387345499351269 43932210965322627281128363)
          ·
            refine ⟨65898316447983940921692545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43932210965322627281128363 65898316447983940921692545)
            ·
              refine ⟨49423737335987955691269409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65898316447983940921692545 49423737335987955691269409)
              ·
                refine ⟨37067803001990966768452057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49423737335987955691269409 37067803001990966768452057)
                ·
                  refine ⟨27800852251493225076339043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37067803001990966768452057 27800852251493225076339043)
                  ·
                    refine ⟨41701278377239837614508565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27800852251493225076339043 41701278377239837614508565)
                    ·
                      refine ⟨1954747423933117388180089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41701278377239837614508565 1954747423933117388180089)
                      ·
                        rfl

theorem cell23_3806857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_3806857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806857 prefixEnd_3806857 := by exact prefixLift 3806857
  have htrace : WordTrace (prefixWord ++ tailWord_3806857) baseStart_3806857 baseEnd_3806857 := by
    simpa [prefixWord, tailWord_3806857, baseEnd_3806857] using wordTrace_append hprefix tailTrace_3806857
  have hstable : (prefixWord ++ tailWord_3806857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806857).length < 2 ^ (prefixWord ++ tailWord_3806857).sum := by decide
  have hdescent : baseEnd_3806857 < baseStart_3806857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806878 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3806878 : Nat := 118140960795 + 3806878 * 2 ^ 59
def prefixEnd_3806878 : Nat := 4983230072969 + 3 ^ 40 * 3806878 * 2
def baseEnd_3806878 : Nat := 1954758207026861806017493

theorem tailTrace_3806878 : CollatzResearch.WordTrace tailWord_3806878 prefixEnd_3806878 1954758207026861806017493 := by
  unfold tailWord_3806878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17356030937792330480673661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92565498334892429230259525 17356030937792330480673661)
  ·
    refine ⟨6508511601672123930252623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17356030937792330480673661 6508511601672123930252623)
    ·
      refine ⟨9762767402508185895378935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508511601672123930252623 9762767402508185895378935)
      ·
        refine ⟨14644151103762278843068403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762767402508185895378935 14644151103762278843068403)
        ·
          refine ⟨21966226655643418264602605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14644151103762278843068403 21966226655643418264602605)
          ·
            refine ⟨8237334995866281849225977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21966226655643418264602605 8237334995866281849225977)
            ·
              refine ⟨6178001246899711386919483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8237334995866281849225977 6178001246899711386919483)
              ·
                refine ⟨9267001870349567080379225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6178001246899711386919483 9267001870349567080379225)
                ·
                  refine ⟨6950251402762175310284419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9267001870349567080379225 6950251402762175310284419)
                  ·
                    refine ⟨10425377104143262965426629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6950251402762175310284419 10425377104143262965426629)
                    ·
                      refine ⟨1954758207026861806017493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10425377104143262965426629 1954758207026861806017493)
                      ·
                        rfl

theorem cell23_3806878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3806878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806878 prefixEnd_3806878 := by exact prefixLift 3806878
  have htrace : WordTrace (prefixWord ++ tailWord_3806878) baseStart_3806878 baseEnd_3806878 := by
    simpa [prefixWord, tailWord_3806878, baseEnd_3806878] using wordTrace_append hprefix tailTrace_3806878
  have hstable : (prefixWord ++ tailWord_3806878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806878).length < 2 ^ (prefixWord ++ tailWord_3806878).sum := by decide
  have hdescent : baseEnd_3806878 < baseStart_3806878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806881 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3806881 : Nat := 118140960795 + 3806881 * 2 ^ 59
def prefixEnd_3806881 : Nat := 4983230072969 + 3 ^ 40 * 3806881 * 2
def baseEnd_3806881 : Nat := 1954759747468825294279979

theorem tailTrace_3806881 : CollatzResearch.WordTrace tailWord_3806881 prefixEnd_3806881 1954759747468825294279979 := by
  unfold tailWord_3806881
  simp only [CollatzResearch.WordTrace]
  refine ⟨138848356921327775357748497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92565571280885183571832331 138848356921327775357748497)
  ·
    refine ⟨104136267690995831518311373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138848356921327775357748497 104136267690995831518311373)
    ·
      refine ⟨39051100384123436819366765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104136267690995831518311373 39051100384123436819366765)
      ·
        refine ⟨14644162644046288807262537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39051100384123436819366765 14644162644046288807262537)
        ·
          refine ⟨10983121983034716605446903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14644162644046288807262537 10983121983034716605446903)
          ·
            refine ⟨16474682974552074908170355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983121983034716605446903 16474682974552074908170355)
            ·
              refine ⟨24712024461828112362255533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16474682974552074908170355 24712024461828112362255533)
              ·
                refine ⟨9267009173185542135845825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24712024461828112362255533 9267009173185542135845825)
                ·
                  refine ⟨6950256879889156601884369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9267009173185542135845825 6950256879889156601884369)
                  ·
                    refine ⟨5212692659916867451413277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6950256879889156601884369 5212692659916867451413277)
                    ·
                      refine ⟨1954759747468825294279979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212692659916867451413277 1954759747468825294279979)
                      ·
                        rfl

theorem cell23_3806881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3806881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806881 prefixEnd_3806881 := by exact prefixLift 3806881
  have htrace : WordTrace (prefixWord ++ tailWord_3806881) baseStart_3806881 baseEnd_3806881 := by
    simpa [prefixWord, tailWord_3806881, baseEnd_3806881] using wordTrace_append hprefix tailTrace_3806881
  have hstable : (prefixWord ++ tailWord_3806881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806881).length < 2 ^ (prefixWord ++ tailWord_3806881).sum := by decide
  have hdescent : baseEnd_3806881 < baseStart_3806881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806907 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_3806907 : Nat := 118140960795 + 3806907 * 2 ^ 59
def prefixEnd_3806907 : Nat := 4983230072969 + 3 ^ 40 * 3806907 * 2
def baseEnd_3806907 : Nat := 1954773097965842192554859

theorem tailTrace_3806907 : CollatzResearch.WordTrace tailWord_3806907 prefixEnd_3806907 1954773097965842192554859 := by
  unfold tailWord_3806907
  simp only [CollatzResearch.WordTrace]
  refine ⟨138849305219233581798194975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92566203479489054532129983 138849305219233581798194975)
  ·
    refine ⟨208273957828850372697292463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138849305219233581798194975 208273957828850372697292463)
    ·
      refine ⟨312410936743275559045938695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208273957828850372697292463 312410936743275559045938695)
      ·
        refine ⟨468616405114913338568908043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312410936743275559045938695 468616405114913338568908043)
        ·
          refine ⟨702924607672370007853362065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468616405114913338568908043 702924607672370007853362065)
          ·
            refine ⟨527193455754277505890021549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702924607672370007853362065 527193455754277505890021549)
            ·
              refine ⟨197697545907854064708758081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527193455754277505890021549 197697545907854064708758081)
              ·
                refine ⟨148273159430890548531568561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197697545907854064708758081 148273159430890548531568561)
                ·
                  refine ⟨111204869573167911398676421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148273159430890548531568561 111204869573167911398676421)
                  ·
                    refine ⟨20850913044968983387251829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111204869573167911398676421 20850913044968983387251829)
                    ·
                      refine ⟨1954773097965842192554859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20850913044968983387251829 1954773097965842192554859)
                      ·
                        rfl

theorem cell23_3806907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_3806907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806907 prefixEnd_3806907 := by exact prefixLift 3806907
  have htrace : WordTrace (prefixWord ++ tailWord_3806907) baseStart_3806907 baseEnd_3806907 := by
    simpa [prefixWord, tailWord_3806907, baseEnd_3806907] using wordTrace_append hprefix tailTrace_3806907
  have hstable : (prefixWord ++ tailWord_3806907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806907).length < 2 ^ (prefixWord ++ tailWord_3806907).sum := by decide
  have hdescent : baseEnd_3806907 < baseStart_3806907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806911 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 3]
def baseStart_3806911 : Nat := 118140960795 + 3806911 * 2 ^ 59
def prefixEnd_3806911 : Nat := 4983230072969 + 3 ^ 40 * 3806911 * 2
def baseEnd_3806911 : Nat := 1954775151888460176904841

theorem tailTrace_3806911 : CollatzResearch.WordTrace tailWord_3806911 prefixEnd_3806911 1954775151888460176904841 := by
  unfold tailWord_3806911
  simp only [CollatzResearch.WordTrace]
  refine ⟨138849451111219090481340587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92566300740812726987560391 138849451111219090481340587)
  ·
    refine ⟨208274176666828635722010881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138849451111219090481340587 208274176666828635722010881)
    ·
      refine ⟨156205632500121476791508161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208274176666828635722010881 156205632500121476791508161)
      ·
        refine ⟨117154224375091107593631121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156205632500121476791508161 117154224375091107593631121)
        ·
          refine ⟨87865668281318330695223341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117154224375091107593631121 87865668281318330695223341)
          ·
            refine ⟨32949625605494374010708753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87865668281318330695223341 32949625605494374010708753)
            ·
              refine ⟨24712219204120780508031565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32949625605494374010708753 24712219204120780508031565)
              ·
                refine ⟨9267082201545292690511837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24712219204120780508031565 9267082201545292690511837)
                ·
                  refine ⟨3475155825579484758941939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9267082201545292690511837 3475155825579484758941939)
                  ·
                    refine ⟨5212733738369227138412909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3475155825579484758941939 5212733738369227138412909)
                    ·
                      refine ⟨1954775151888460176904841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5212733738369227138412909 1954775151888460176904841)
                      ·
                        rfl

theorem cell23_3806911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_3806911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806911 prefixEnd_3806911 := by exact prefixLift 3806911
  have htrace : WordTrace (prefixWord ++ tailWord_3806911) baseStart_3806911 baseEnd_3806911 := by
    simpa [prefixWord, tailWord_3806911, baseEnd_3806911] using wordTrace_append hprefix tailTrace_3806911
  have hstable : (prefixWord ++ tailWord_3806911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806911).length < 2 ^ (prefixWord ++ tailWord_3806911).sum := by decide
  have hdescent : baseEnd_3806911 < baseStart_3806911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806938 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2]
def baseStart_3806938 : Nat := 118140960795 + 3806938 * 2 ^ 59
def prefixEnd_3806938 : Nat := 4983230072969 + 3 ^ 40 * 3806938 * 2
def baseEnd_3806938 : Nat := 1954789015866131571267217

theorem tailTrace_3806938 : CollatzResearch.WordTrace tailWord_3806938 prefixEnd_3806938 1954789015866131571267217 := by
  unfold tailWord_3806938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34712608970530318523143367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92566957254747516061715645 34712608970530318523143367)
  ·
    refine ⟨52068913455795477784715051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34712608970530318523143367 52068913455795477784715051)
    ·
      refine ⟨78103370183693216677072577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52068913455795477784715051 78103370183693216677072577)
      ·
        refine ⟨58577527637769912507804433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78103370183693216677072577 58577527637769912507804433)
        ·
          refine ⟨43933145728327434380853325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58577527637769912507804433 43933145728327434380853325)
          ·
            refine ⟨16474929648122787892819997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43933145728327434380853325 16474929648122787892819997)
            ·
              refine ⟨6178098618046045459807499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16474929648122787892819997 6178098618046045459807499)
              ·
                refine ⟨9267147927069068189711249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6178098618046045459807499 9267147927069068189711249)
                ·
                  refine ⟨6950360945301801142283437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9267147927069068189711249 6950360945301801142283437)
                  ·
                    refine ⟨2606385354488175428356289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6950360945301801142283437 2606385354488175428356289)
                    ·
                      refine ⟨1954789015866131571267217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606385354488175428356289 1954789015866131571267217)
                      ·
                        rfl

theorem cell23_3806938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_3806938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806938 prefixEnd_3806938 := by exact prefixLift 3806938
  have htrace : WordTrace (prefixWord ++ tailWord_3806938) baseStart_3806938 baseEnd_3806938 := by
    simpa [prefixWord, tailWord_3806938, baseEnd_3806938] using wordTrace_append hprefix tailTrace_3806938
  have hstable : (prefixWord ++ tailWord_3806938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806938).length < 2 ^ (prefixWord ++ tailWord_3806938).sum := by decide
  have hdescent : baseEnd_3806938 < baseStart_3806938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806944 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_3806944 : Nat := 118140960795 + 3806944 * 2 ^ 59
def prefixEnd_3806944 : Nat := 4983230072969 + 3 ^ 40 * 3806944 * 2
def baseEnd_3806944 : Nat := 651597365583352849264063

theorem tailTrace_3806944 : CollatzResearch.WordTrace tailWord_3806944 prefixEnd_3806944 651597365583352849264063 := by
  unfold tailWord_3806944
  simp only [CollatzResearch.WordTrace]
  refine ⟨69425327360049768558645943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92567103146733024744861257 69425327360049768558645943)
  ·
    refine ⟨104137991040074652837968915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69425327360049768558645943 104137991040074652837968915)
    ·
      refine ⟨156206986560111979256953373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104137991040074652837968915 156206986560111979256953373)
      ·
        refine ⟨58577619960041992221357515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156206986560111979256953373 58577619960041992221357515)
        ·
          refine ⟨87866429940062988332036273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58577619960041992221357515 87866429940062988332036273)
          ·
            refine ⟨65899822455047241249027205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87866429940062988332036273 65899822455047241249027205)
            ·
              refine ⟨12356216710321357734192601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65899822455047241249027205 12356216710321357734192601)
              ·
                refine ⟨9267162532741018300644451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12356216710321357734192601 9267162532741018300644451)
                ·
                  refine ⟨13900743799111527450966677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267162532741018300644451 13900743799111527450966677)
                  ·
                    refine ⟨651597365583352849264063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13900743799111527450966677 651597365583352849264063)
                    ·
                      rfl

theorem cell23_3806944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_3806944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806944 prefixEnd_3806944 := by exact prefixLift 3806944
  have htrace : WordTrace (prefixWord ++ tailWord_3806944) baseStart_3806944 baseEnd_3806944 := by
    simpa [prefixWord, tailWord_3806944, baseEnd_3806944] using wordTrace_append hprefix tailTrace_3806944
  have hstable : (prefixWord ++ tailWord_3806944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806944).length < 2 ^ (prefixWord ++ tailWord_3806944).sum := by decide
  have hdescent : baseEnd_3806944 < baseStart_3806944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806961 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 4, 4]
def baseStart_3806961 : Nat := 118140960795 + 3806961 * 2 ^ 59
def prefixEnd_3806961 : Nat := 4983230072969 + 3 ^ 40 * 3806961 * 2
def baseEnd_3806961 : Nat := 651600275307061660426537

theorem tailTrace_3806961 : CollatzResearch.WordTrace tailWord_3806961 prefixEnd_3806961 651600275307061660426537 := by
  unfold tailWord_3806961
  simp only [CollatzResearch.WordTrace]
  refine ⟨138851274761037949020660737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92567516507358632680440491 138851274761037949020660737)
  ·
    refine ⟨104138456070778461765495553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138851274761037949020660737 104138456070778461765495553)
    ·
      refine ⟨78103842053083846324121665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104138456070778461765495553 78103842053083846324121665)
      ·
        refine ⟨58577881539812884743091249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78103842053083846324121665 58577881539812884743091249)
        ·
          refine ⟨43933411154859663557318437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58577881539812884743091249 43933411154859663557318437)
          ·
            refine ⟨8237514591536186916997207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43933411154859663557318437 8237514591536186916997207)
            ·
              refine ⟨12356271887304280375495811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237514591536186916997207 12356271887304280375495811)
              ·
                refine ⟨18534407830956420563243717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12356271887304280375495811 18534407830956420563243717)
                ·
                  refine ⟨3475201468304328855608197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18534407830956420563243717 3475201468304328855608197)
                  ·
                    refine ⟨651600275307061660426537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3475201468304328855608197 651600275307061660426537)
                    ·
                      rfl

theorem cell23_3806961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_3806961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3806961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3806961 prefixEnd_3806961 := by exact prefixLift 3806961
  have htrace : WordTrace (prefixWord ++ tailWord_3806961) baseStart_3806961 baseEnd_3806961 := by
    simpa [prefixWord, tailWord_3806961, baseEnd_3806961] using wordTrace_append hprefix tailTrace_3806961
  have hstable : (prefixWord ++ tailWord_3806961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806961).length < 2 ^ (prefixWord ++ tailWord_3806961).sum := by decide
  have hdescent : baseEnd_3806961 < baseStart_3806961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807002 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2]
def baseStart_3807002 : Nat := 118140960795 + 3807002 * 2 ^ 59
def prefixEnd_3807002 : Nat := 4983230072969 + 3 ^ 40 * 3807002 * 2
def baseEnd_3807002 : Nat := 1954821878628019320866923

theorem tailTrace_3807002 : CollatzResearch.WordTrace tailWord_3807002 prefixEnd_3807002 1954821878628019320866923 := by
  unfold tailWord_3807002
  simp only [CollatzResearch.WordTrace]
  refine ⟨34713192538472353255725815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92568513435926275348602173 34713192538472353255725815)
  ·
    refine ⟨52069788807708529883588723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34713192538472353255725815 52069788807708529883588723)
    ·
      refine ⟨78104683211562794825383085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52069788807708529883588723 78104683211562794825383085)
      ·
        refine ⟨29289256204336048059518657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78104683211562794825383085 29289256204336048059518657)
        ·
          refine ⟨21966942153252036044638993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29289256204336048059518657 21966942153252036044638993)
          ·
            refine ⟨16475206614939027033479245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21966942153252036044638993 16475206614939027033479245)
            ·
              refine ⟨6178202480602135137554717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16475206614939027033479245 6178202480602135137554717)
              ·
                refine ⟨2316825930225800676583019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6178202480602135137554717 2316825930225800676583019)
                ·
                  refine ⟨3475238895338701014874529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316825930225800676583019 3475238895338701014874529)
                  ·
                    refine ⟨2606429171504025761155897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3475238895338701014874529 2606429171504025761155897)
                    ·
                      refine ⟨1954821878628019320866923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606429171504025761155897 1954821878628019320866923)
                      ·
                        rfl

theorem cell23_3807002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_3807002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807002 prefixEnd_3807002 := by exact prefixLift 3807002
  have htrace : WordTrace (prefixWord ++ tailWord_3807002) baseStart_3807002 baseEnd_3807002 := by
    simpa [prefixWord, tailWord_3807002, baseEnd_3807002] using wordTrace_append hprefix tailTrace_3807002
  have hstable : (prefixWord ++ tailWord_3807002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807002).length < 2 ^ (prefixWord ++ tailWord_3807002).sum := by decide
  have hdescent : baseEnd_3807002 < baseStart_3807002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807058 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_3807058 : Nat := 118140960795 + 3807058 * 2 ^ 59
def prefixEnd_3807058 : Nat := 4983230072969 + 3 ^ 40 * 3807058 * 2
def baseEnd_3807058 : Nat := 1954850633544671101766665

theorem tailTrace_3807058 : CollatzResearch.WordTrace tailWord_3807058 prefixEnd_3807058 1954850633544671101766665 := by
  unfold tailWord_3807058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34713703160421633646735457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92569875094457689724627885 34713703160421633646735457)
  ·
    refine ⟨26035277370316225235051593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34713703160421633646735457 26035277370316225235051593)
    ·
      refine ⟨19526458027737168926288695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26035277370316225235051593 19526458027737168926288695)
      ·
        refine ⟨29289687041605753389433043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19526458027737168926288695 29289687041605753389433043)
        ·
          refine ⟨43934530562408630084149565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29289687041605753389433043 43934530562408630084149565)
          ·
            refine ⟨16475448960903236281556087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43934530562408630084149565 16475448960903236281556087)
            ·
              refine ⟨24713173441354854422334131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16475448960903236281556087 24713173441354854422334131)
              ·
                refine ⟨37069760162032281633501197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24713173441354854422334131 37069760162032281633501197)
                ·
                  refine ⟨13901160060762105612562949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37069760162032281633501197 13901160060762105612562949)
                  ·
                    refine ⟨2606467511392894802355553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13901160060762105612562949 2606467511392894802355553)
                    ·
                      refine ⟨1954850633544671101766665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606467511392894802355553 1954850633544671101766665)
                      ·
                        rfl

theorem cell23_3807058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_3807058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807058 prefixEnd_3807058 := by exact prefixLift 3807058
  have htrace : WordTrace (prefixWord ++ tailWord_3807058) baseStart_3807058 baseEnd_3807058 := by
    simpa [prefixWord, tailWord_3807058, baseEnd_3807058] using wordTrace_append hprefix tailTrace_3807058
  have hstable : (prefixWord ++ tailWord_3807058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807058).length < 2 ^ (prefixWord ++ tailWord_3807058).sum := by decide
  have hdescent : baseEnd_3807058 < baseStart_3807058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807061 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3807061 : Nat := 118140960795 + 3807061 * 2 ^ 59
def prefixEnd_3807061 : Nat := 4983230072969 + 3 ^ 40 * 3807061 * 2
def baseEnd_3807061 : Nat := 1954852173986634590029151

theorem tailTrace_3807061 : CollatzResearch.WordTrace tailWord_3807061 prefixEnd_3807061 1954852173986634590029151 := by
  unfold tailWord_3807061
  simp only [CollatzResearch.WordTrace]
  refine ⟨138854922060675666099301037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92569948040450444066200691 138854922060675666099301037)
  ·
    refine ⟨52070595772753374787237889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138854922060675666099301037 52070595772753374787237889)
    ·
      refine ⟨39052946829565031090428417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52070595772753374787237889 39052946829565031090428417)
      ·
        refine ⟨29289710122173773317821313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39052946829565031090428417 29289710122173773317821313)
        ·
          refine ⟨21967282591630329988365985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29289710122173773317821313 21967282591630329988365985)
          ·
            refine ⟨16475461943722747491274489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21967282591630329988365985 16475461943722747491274489)
            ·
              refine ⟨12356596457792060618455867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16475461943722747491274489 12356596457792060618455867)
              ·
                refine ⟨18534894686688090927683801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12356596457792060618455867 18534894686688090927683801)
                ·
                  refine ⟨13901171015016068195762851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18534894686688090927683801 13901171015016068195762851)
                  ·
                    refine ⟨20851756522524102293644277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13901171015016068195762851 20851756522524102293644277)
                    ·
                      refine ⟨1954852173986634590029151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20851756522524102293644277 1954852173986634590029151)
                      ·
                        rfl

theorem cell23_3807061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3807061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807061 prefixEnd_3807061 := by exact prefixLift 3807061
  have htrace : WordTrace (prefixWord ++ tailWord_3807061) baseStart_3807061 baseEnd_3807061 := by
    simpa [prefixWord, tailWord_3807061, baseEnd_3807061] using wordTrace_append hprefix tailTrace_3807061
  have hstable : (prefixWord ++ tailWord_3807061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807061).length < 2 ^ (prefixWord ++ tailWord_3807061).sum := by decide
  have hdescent : baseEnd_3807061 < baseStart_3807061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807126 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3807126 : Nat := 118140960795 + 3807126 * 2 ^ 59
def prefixEnd_3807126 : Nat := 4983230072969 + 3 ^ 40 * 3807126 * 2
def baseEnd_3807126 : Nat := 1954885550229176835716353

theorem tailTrace_3807126 : CollatzResearch.WordTrace tailWord_3807126 prefixEnd_3807126 1954885550229176835716353 := by
  unfold tailWord_3807126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678580800340011387526077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92571528536960121466944821 8678580800340011387526077)
  ·
    refine ⟨3254467800127504270322279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8678580800340011387526077 3254467800127504270322279)
    ·
      refine ⟨4881701700191256405483419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254467800127504270322279 4881701700191256405483419)
      ·
        refine ⟨7322552550286884608225129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881701700191256405483419 7322552550286884608225129)
        ·
          refine ⟨5491914412715163456168847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7322552550286884608225129 5491914412715163456168847)
          ·
            refine ⟨8237871619072745184253271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491914412715163456168847 8237871619072745184253271)
            ·
              refine ⟨12356807428609117776379907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237871619072745184253271 12356807428609117776379907)
              ·
                refine ⟨18535211142913676664569861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12356807428609117776379907 18535211142913676664569861)
                ·
                  refine ⟨3475352089296314374606849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18535211142913676664569861 3475352089296314374606849)
                  ·
                    refine ⟨2606514066972235780955137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3475352089296314374606849 2606514066972235780955137)
                    ·
                      refine ⟨1954885550229176835716353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606514066972235780955137 1954885550229176835716353)
                      ·
                        rfl

theorem cell23_3807126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3807126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807126 prefixEnd_3807126 := by exact prefixLift 3807126
  have htrace : WordTrace (prefixWord ++ tailWord_3807126) baseStart_3807126 baseEnd_3807126 := by
    simpa [prefixWord, tailWord_3807126, baseEnd_3807126] using wordTrace_append hprefix tailTrace_3807126
  have hstable : (prefixWord ++ tailWord_3807126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807126).length < 2 ^ (prefixWord ++ tailWord_3807126).sum := by decide
  have hdescent : baseEnd_3807126 < baseStart_3807126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807151 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_3807151 : Nat := 118140960795 + 3807151 * 2 ^ 59
def prefixEnd_3807151 : Nat := 4983230072969 + 3 ^ 40 * 3807151 * 2
def baseEnd_3807151 : Nat := 1954898387245539237903737

theorem tailTrace_3807151 : CollatzResearch.WordTrace tailWord_3807151 prefixEnd_3807151 1954898387245539237903737 := by
  unfold tailWord_3807151
  simp only [CollatzResearch.WordTrace]
  refine ⟨138858204630349611470077307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92572136420233074313384871 138858204630349611470077307)
  ·
    refine ⟨208287306945524417205115961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138858204630349611470077307 208287306945524417205115961)
    ·
      refine ⟨156215480209143312903836971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208287306945524417205115961 156215480209143312903836971)
      ·
        refine ⟨234323220313714969355755457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156215480209143312903836971 234323220313714969355755457)
        ·
          refine ⟨175742415235286227016816593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234323220313714969355755457 175742415235286227016816593)
          ·
            refine ⟨131806811426464670262612445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175742415235286227016816593 131806811426464670262612445)
            ·
              refine ⟨49427554284924251348479667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131806811426464670262612445 49427554284924251348479667)
              ·
                refine ⟨74141331427386377022719501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49427554284924251348479667 74141331427386377022719501)
                ·
                  refine ⟨27802999285269891383519813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74141331427386377022719501 27802999285269891383519813)
                  ·
                    refine ⟨5213062365988104634409965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27802999285269891383519813 5213062365988104634409965)
                    ·
                      refine ⟨1954898387245539237903737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5213062365988104634409965 1954898387245539237903737)
                      ·
                        rfl

theorem cell23_3807151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_3807151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807151 prefixEnd_3807151 := by exact prefixLift 3807151
  have htrace : WordTrace (prefixWord ++ tailWord_3807151) baseStart_3807151 baseEnd_3807151 := by
    simpa [prefixWord, tailWord_3807151, baseEnd_3807151] using wordTrace_append hprefix tailTrace_3807151
  have hstable : (prefixWord ++ tailWord_3807151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807151).length < 2 ^ (prefixWord ++ tailWord_3807151).sum := by decide
  have hdescent : baseEnd_3807151 < baseStart_3807151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807161 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3807161 : Nat := 118140960795 + 3807161 * 2 ^ 59
def prefixEnd_3807161 : Nat := 4983230072969 + 3 ^ 40 * 3807161 * 2
def baseEnd_3807161 : Nat := 1954903522052084198778691

theorem tailTrace_3807161 : CollatzResearch.WordTrace tailWord_3807161 prefixEnd_3807161 1954903522052084198778691 := by
  unfold tailWord_3807161
  simp only [CollatzResearch.WordTrace]
  refine ⟨138858569360313383177941337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92572379573542255451960891 138858569360313383177941337)
  ·
    refine ⟨104143927020235037383456003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138858569360313383177941337 104143927020235037383456003)
    ·
      refine ⟨156215890530352556075184005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104143927020235037383456003 156215890530352556075184005)
      ·
        refine ⟨29290479474441104264097001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156215890530352556075184005 29290479474441104264097001)
        ·
          refine ⟨21967859605830828198072751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29290479474441104264097001 21967859605830828198072751)
          ·
            refine ⟨32951789408746242297109127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21967859605830828198072751 32951789408746242297109127)
            ·
              refine ⟨49427684113119363445663691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32951789408746242297109127 49427684113119363445663691)
              ·
                refine ⟨74141526169679045168495537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49427684113119363445663691 74141526169679045168495537)
                ·
                  refine ⟨55606144627259283876371653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74141526169679045168495537 55606144627259283876371653)
                  ·
                    refine ⟨10426152117611115726819685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55606144627259283876371653 10426152117611115726819685)
                    ·
                      refine ⟨1954903522052084198778691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10426152117611115726819685 1954903522052084198778691)
                      ·
                        rfl

theorem cell23_3807161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3807161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807161 prefixEnd_3807161 := by exact prefixLift 3807161
  have htrace : WordTrace (prefixWord ++ tailWord_3807161) baseStart_3807161 baseEnd_3807161 := by
    simpa [prefixWord, tailWord_3807161, baseEnd_3807161] using wordTrace_append hprefix tailTrace_3807161
  have hstable : (prefixWord ++ tailWord_3807161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807161).length < 2 ^ (prefixWord ++ tailWord_3807161).sum := by decide
  have hdescent : baseEnd_3807161 < baseStart_3807161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807168 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_3807168 : Nat := 118140960795 + 3807168 * 2 ^ 59
def prefixEnd_3807168 : Nat := 4983230072969 + 3 ^ 40 * 3807168 * 2
def baseEnd_3807168 : Nat := 1954907116416665671391159

theorem tailTrace_3807168 : CollatzResearch.WordTrace tailWord_3807168 prefixEnd_3807168 1954907116416665671391159 := by
  unfold tailWord_3807168
  simp only [CollatzResearch.WordTrace]
  refine ⟨69429412335644011686723079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92572549780858682248964105 69429412335644011686723079)
  ·
    refine ⟨104144118503466017530084619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69429412335644011686723079 104144118503466017530084619)
    ·
      refine ⟨156216177755199026295126929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104144118503466017530084619 156216177755199026295126929)
      ·
        refine ⟨117162133316399269721345197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156216177755199026295126929 117162133316399269721345197)
        ·
          refine ⟨43935799993649726145504449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117162133316399269721345197 43935799993649726145504449)
          ·
            refine ⟨32951849995237294609128337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43935799993649726145504449 32951849995237294609128337)
            ·
              refine ⟨24713887496427970956846253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32951849995237294609128337 24713887496427970956846253)
              ·
                refine ⟨9267707811160489108817345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24713887496427970956846253 9267707811160489108817345)
                ·
                  refine ⟨6950780858370366831613009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9267707811160489108817345 6950780858370366831613009)
                  ·
                    refine ⟨5213085643777775123709757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6950780858370366831613009 5213085643777775123709757)
                    ·
                      refine ⟨1954907116416665671391159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5213085643777775123709757 1954907116416665671391159)
                      ·
                        rfl

theorem cell23_3807168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_3807168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807168 prefixEnd_3807168 := by exact prefixLift 3807168
  have htrace : WordTrace (prefixWord ++ tailWord_3807168) baseStart_3807168 baseEnd_3807168 := by
    simpa [prefixWord, tailWord_3807168, baseEnd_3807168] using wordTrace_append hprefix tailTrace_3807168
  have hstable : (prefixWord ++ tailWord_3807168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807168).length < 2 ^ (prefixWord ++ tailWord_3807168).sum := by decide
  have hdescent : baseEnd_3807168 < baseStart_3807168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807188 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 6]
def baseStart_3807188 : Nat := 118140960795 + 3807188 * 2 ^ 59
def prefixEnd_3807188 : Nat := 4983230072969 + 3 ^ 40 * 3807188 * 2
def baseEnd_3807188 : Nat := 217213042892195065904563

theorem tailTrace_3807188 : CollatzResearch.WordTrace tailWord_3807188 prefixEnd_3807188 217213042892195065904563 := by
  unfold tailWord_3807188
  simp only [CollatzResearch.WordTrace]
  refine ⟨69429777065607783394587109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92573036087477044526116145 69429777065607783394587109)
  ·
    refine ⟨13018083199801459386485083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69429777065607783394587109 13018083199801459386485083)
    ·
      refine ⟨19527124799702189079727625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13018083199801459386485083 19527124799702189079727625)
      ·
        refine ⟨14645343599776641809795719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19527124799702189079727625 14645343599776641809795719)
        ·
          refine ⟨21968015399664962714693579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14645343599776641809795719 21968015399664962714693579)
          ·
            refine ⟨32952023099497444072040369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21968015399664962714693579 32952023099497444072040369)
            ·
              refine ⟨24714017324623083054030277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32952023099497444072040369 24714017324623083054030277)
              ·
                refine ⟨4633878248366828072630677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24714017324623083054030277 4633878248366828072630677)
                ·
                  refine ⟨217213042892195065904563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4633878248366828072630677 217213042892195065904563)
                  ·
                    rfl

theorem cell23_3807188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_3807188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807188 prefixEnd_3807188 := by exact prefixLift 3807188
  have htrace : WordTrace (prefixWord ++ tailWord_3807188) baseStart_3807188 baseEnd_3807188 := by
    simpa [prefixWord, tailWord_3807188, baseEnd_3807188] using wordTrace_append hprefix tailTrace_3807188
  have hstable : (prefixWord ++ tailWord_3807188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807188).length < 2 ^ (prefixWord ++ tailWord_3807188).sum := by decide
  have hdescent : baseEnd_3807188 < baseStart_3807188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807192 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 1, 4]
def baseStart_3807192 : Nat := 118140960795 + 3807192 * 2 ^ 59
def prefixEnd_3807192 : Nat := 4983230072969 + 3 ^ 40 * 3807192 * 2
def baseEnd_3807192 : Nat := 651639813317457859163683

theorem tailTrace_3807192 : CollatzResearch.WordTrace tailWord_3807192 prefixEnd_3807192 651639813317457859163683 := by
  unfold tailWord_3807192
  simp only [CollatzResearch.WordTrace]
  refine ⟨69429850011600537736159915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92573133348800716981546553 69429850011600537736159915)
  ·
    refine ⟨104144775017400806604239873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69429850011600537736159915 104144775017400806604239873)
    ·
      refine ⟨78108581263050604953179905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104144775017400806604239873 78108581263050604953179905)
      ·
        refine ⟨58581435947287953714884929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78108581263050604953179905 58581435947287953714884929)
        ·
          refine ⟨43936076960465965286163697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58581435947287953714884929 43936076960465965286163697)
          ·
            refine ⟨32952057720349473964622773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43936076960465965286163697 32952057720349473964622773)
            ·
              refine ⟨3089255411282763184183385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32952057720349473964622773 3089255411282763184183385)
              ·
                refine ⟨2316941558462072388137539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089255411282763184183385 2316941558462072388137539)
                ·
                  refine ⟨3475412337693108582206309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316941558462072388137539 3475412337693108582206309)
                  ·
                    refine ⟨651639813317457859163683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3475412337693108582206309 651639813317457859163683)
                    ·
                      rfl

theorem cell23_3807192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_3807192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807192 prefixEnd_3807192 := by exact prefixLift 3807192
  have htrace : WordTrace (prefixWord ++ tailWord_3807192) baseStart_3807192 baseEnd_3807192 := by
    simpa [prefixWord, tailWord_3807192, baseEnd_3807192] using wordTrace_append hprefix tailTrace_3807192
  have hstable : (prefixWord ++ tailWord_3807192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807192).length < 2 ^ (prefixWord ++ tailWord_3807192).sum := by decide
  have hdescent : baseEnd_3807192 < baseStart_3807192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807225 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 2, 3, 2]
def baseStart_3807225 : Nat := 118140960795 + 3807225 * 2 ^ 59
def prefixEnd_3807225 : Nat := 4983230072969 + 3 ^ 40 * 3807225 * 2
def baseEnd_3807225 : Nat := 1954936384813971948378397

theorem tailTrace_3807225 : CollatzResearch.WordTrace tailWord_3807225 prefixEnd_3807225 1954936384813971948378397 := by
  unfold tailWord_3807225
  simp only [CollatzResearch.WordTrace]
  refine ⟨138860903632081522108271129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92573935754721014738847419 138860903632081522108271129)
  ·
    refine ⟨104145677724061141581203347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138860903632081522108271129 104145677724061141581203347)
    ·
      refine ⟨156218516586091712371805021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104145677724061141581203347 156218516586091712371805021)
      ·
        refine ⟨58581943719784392139426883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156218516586091712371805021 58581943719784392139426883)
        ·
          refine ⟨87872915579676588209140325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58581943719784392139426883 87872915579676588209140325)
          ·
            refine ⟨16476171671189360289213811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87872915579676588209140325 16476171671189360289213811)
            ·
              refine ⟨24714257506784040433820717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16476171671189360289213811 24714257506784040433820717)
              ·
                refine ⟨9267846565044015162682769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24714257506784040433820717 9267846565044015162682769)
                ·
                  refine ⟨6950884923783011372012077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9267846565044015162682769 6950884923783011372012077)
                  ·
                    refine ⟨2606581846418629264504529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6950884923783011372012077 2606581846418629264504529)
                    ·
                      refine ⟨1954936384813971948378397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606581846418629264504529 1954936384813971948378397)
                      ·
                        rfl

theorem cell23_3807225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_3807225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807225 prefixEnd_3807225 := by exact prefixLift 3807225
  have htrace : WordTrace (prefixWord ++ tailWord_3807225) baseStart_3807225 baseEnd_3807225 := by
    simpa [prefixWord, tailWord_3807225, baseEnd_3807225] using wordTrace_append hprefix tailTrace_3807225
  have hstable : (prefixWord ++ tailWord_3807225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807225).length < 2 ^ (prefixWord ++ tailWord_3807225).sum := by decide
  have hdescent : baseEnd_3807225 < baseStart_3807225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807251 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_3807251 : Nat := 118140960795 + 3807251 * 2 ^ 59
def prefixEnd_3807251 : Nat := 4983230072969 + 3 ^ 40 * 3807251 * 2
def baseEnd_3807251 : Nat := 1954949735310988846653277

theorem tailTrace_3807251 : CollatzResearch.WordTrace tailWord_3807251 prefixEnd_3807251 1954949735310988846653277 := by
  unfold tailWord_3807251
  simp only [CollatzResearch.WordTrace]
  refine ⟨138861851929987328548717607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92574567953324885699145071 138861851929987328548717607)
  ·
    refine ⟨208292777894980992823076411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138861851929987328548717607 208292777894980992823076411)
    ·
      refine ⟨312439166842471489234614617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208292777894980992823076411 312439166842471489234614617)
      ·
        refine ⟨234329375131853616925960963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312439166842471489234614617 234329375131853616925960963)
        ·
          refine ⟨351494062697780425388941445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234329375131853616925960963 351494062697780425388941445)
          ·
            refine ⟨65905136755833829760426521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351494062697780425388941445 65905136755833829760426521)
            ·
              refine ⟨49428852566875372320319891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65905136755833829760426521 49428852566875372320319891)
              ·
                refine ⟨74143278850313058480479837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49428852566875372320319891 74143278850313058480479837)
                ·
                  refine ⟨27803729568867396930179939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74143278850313058480479837 27803729568867396930179939)
                  ·
                    refine ⟨41705594353301095395269909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27803729568867396930179939 41705594353301095395269909)
                    ·
                      refine ⟨1954949735310988846653277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41705594353301095395269909 1954949735310988846653277)
                      ·
                        rfl

theorem cell23_3807251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_3807251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807251 prefixEnd_3807251 := by exact prefixLift 3807251
  have htrace : WordTrace (prefixWord ++ tailWord_3807251) baseStart_3807251 baseEnd_3807251 := by
    simpa [prefixWord, tailWord_3807251, baseEnd_3807251] using wordTrace_append hprefix tailTrace_3807251
  have hstable : (prefixWord ++ tailWord_3807251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807251).length < 2 ^ (prefixWord ++ tailWord_3807251).sum := by decide
  have hdescent : baseEnd_3807251 < baseStart_3807251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807265 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 1, 6]
def baseStart_3807265 : Nat := 118140960795 + 3807265 * 2 ^ 59
def prefixEnd_3807265 : Nat := 4983230072969 + 3 ^ 40 * 3807265 * 2
def baseEnd_3807265 : Nat := 651652308013383930626071

theorem tailTrace_3807265 : CollatzResearch.WordTrace tailWord_3807265 prefixEnd_3807265 651652308013383930626071 := by
  unfold tailWord_3807265
  simp only [CollatzResearch.WordTrace]
  refine ⟨138862362551936608939727249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92574908367957739293151499 138862362551936608939727249)
  ·
    refine ⟨104146771913952456704795437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138862362551936608939727249 104146771913952456704795437)
    ·
      refine ⟨39055039467732171264298289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104146771913952456704795437 39055039467732171264298289)
      ·
        refine ⟨29291279600799128448223717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39055039467732171264298289 29291279600799128448223717)
        ·
          refine ⟨5492114925149836584041947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29291279600799128448223717 5492114925149836584041947)
          ·
            refine ⟨8238172387724754876062921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492114925149836584041947 8238172387724754876062921)
            ·
              refine ⟨6178629290793566157047191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8238172387724754876062921 6178629290793566157047191)
              ·
                refine ⟨9267943936190349235570787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6178629290793566157047191 9267943936190349235570787)
                ·
                  refine ⟨13901915904285523853356181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9267943936190349235570787 13901915904285523853356181)
                  ·
                    refine ⟨651652308013383930626071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13901915904285523853356181 651652308013383930626071)
                    ·
                      rfl

theorem cell23_3807265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_3807265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807265 prefixEnd_3807265 := by exact prefixLift 3807265
  have htrace : WordTrace (prefixWord ++ tailWord_3807265) baseStart_3807265 baseEnd_3807265 := by
    simpa [prefixWord, tailWord_3807265, baseEnd_3807265] using wordTrace_append hprefix tailTrace_3807265
  have hstable : (prefixWord ++ tailWord_3807265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807265).length < 2 ^ (prefixWord ++ tailWord_3807265).sum := by decide
  have hdescent : baseEnd_3807265 < baseStart_3807265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807289 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3807289 : Nat := 118140960795 + 3807289 * 2 ^ 59
def prefixEnd_3807289 : Nat := 4983230072969 + 3 ^ 40 * 3807289 * 2
def baseEnd_3807289 : Nat := 1954969247575859697978103

theorem tailTrace_3807289 : CollatzResearch.WordTrace tailWord_3807289 prefixEnd_3807289 1954969247575859697978103 := by
  unfold tailWord_3807289
  simp only [CollatzResearch.WordTrace]
  refine ⟨138863237903849661038600921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92575491935899774025733947 138863237903849661038600921)
  ·
    refine ⟨104147428427887245778950691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138863237903849661038600921 104147428427887245778950691)
    ·
      refine ⟨156221142641830868668426037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104147428427887245778950691 156221142641830868668426037)
      ·
        refine ⟨14645732122671643937664941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156221142641830868668426037 14645732122671643937664941)
        ·
          refine ⟨5492149546001866476624353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14645732122671643937664941 5492149546001866476624353)
          ·
            refine ⟨4119112159501399857468265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492149546001866476624353 4119112159501399857468265)
            ·
              refine ⟨3089334119626049893101199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119112159501399857468265 3089334119626049893101199)
              ·
                refine ⟨4634001179439074839651799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089334119626049893101199 4634001179439074839651799)
                ·
                  refine ⟨6951001769158612259477699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634001179439074839651799 6951001769158612259477699)
                  ·
                    refine ⟨10426502653737918389216549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6951001769158612259477699 10426502653737918389216549)
                    ·
                      refine ⟨1954969247575859697978103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10426502653737918389216549 1954969247575859697978103)
                      ·
                        rfl

theorem cell23_3807289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3807289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807289 prefixEnd_3807289 := by exact prefixLift 3807289
  have htrace : WordTrace (prefixWord ++ tailWord_3807289) baseStart_3807289 baseEnd_3807289 := by
    simpa [prefixWord, tailWord_3807289, baseEnd_3807289] using wordTrace_append hprefix tailTrace_3807289
  have hstable : (prefixWord ++ tailWord_3807289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807289).length < 2 ^ (prefixWord ++ tailWord_3807289).sum := by decide
  have hdescent : baseEnd_3807289 < baseStart_3807289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807291 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 4, 7]
def baseStart_3807291 : Nat := 118140960795 + 3807291 * 2 ^ 59
def prefixEnd_3807291 : Nat := 4983230072969 + 3 ^ 40 * 3807291 * 2
def baseEnd_3807291 : Nat := 651656758179056230051031

theorem tailTrace_3807291 : CollatzResearch.WordTrace tailWord_3807291 prefixEnd_3807291 651656758179056230051031 := by
  unfold tailWord_3807291
  simp only [CollatzResearch.WordTrace]
  refine ⟨138863310849842415380173727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92575540566561610253449151 138863310849842415380173727)
  ·
    refine ⟨208294966274763623070260591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138863310849842415380173727 208294966274763623070260591)
    ·
      refine ⟨312442449412145434605390887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208294966274763623070260591 312442449412145434605390887)
      ·
        refine ⟨468663674118218151908086331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312442449412145434605390887 468663674118218151908086331)
        ·
          refine ⟨702995511177327227862129497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468663674118218151908086331 702995511177327227862129497)
          ·
            refine ⟨527246633382995420896597123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702995511177327227862129497 527246633382995420896597123)
            ·
              refine ⟨790869950074493131344895685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527246633382995420896597123 790869950074493131344895685)
              ·
                refine ⟨148288115638967462127167941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790869950074493131344895685 148288115638967462127167941)
                ·
                  refine ⟨27804021682306399148843989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148288115638967462127167941 27804021682306399148843989)
                  ·
                    refine ⟨651656758179056230051031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27804021682306399148843989 651656758179056230051031)
                    ·
                      rfl

theorem cell23_3807291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_3807291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807291 prefixEnd_3807291 := by exact prefixLift 3807291
  have htrace : WordTrace (prefixWord ++ tailWord_3807291) baseStart_3807291 baseEnd_3807291 := by
    simpa [prefixWord, tailWord_3807291, baseEnd_3807291] using wordTrace_append hprefix tailTrace_3807291
  have hstable : (prefixWord ++ tailWord_3807291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807291).length < 2 ^ (prefixWord ++ tailWord_3807291).sum := by decide
  have hdescent : baseEnd_3807291 < baseStart_3807291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807305 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 3]
def baseStart_3807305 : Nat := 118140960795 + 3807305 * 2 ^ 59
def prefixEnd_3807305 : Nat := 4983230072969 + 3 ^ 40 * 3807305 * 2
def baseEnd_3807305 : Nat := 1954977463266331635378029

theorem tailTrace_3807305 : CollatzResearch.WordTrace tailWord_3807305 prefixEnd_3807305 1954977463266331635378029 := by
  unfold tailWord_3807305
  simp only [CollatzResearch.WordTrace]
  refine ⟨138863821471791695771183369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92575880981194463847455579 138863821471791695771183369)
  ·
    refine ⟨104147866103843771828387527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138863821471791695771183369 104147866103843771828387527)
    ·
      refine ⟨156221799155765657742581291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104147866103843771828387527 156221799155765657742581291)
      ·
        refine ⟨234332698733648486613871937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156221799155765657742581291 234332698733648486613871937)
        ·
          refine ⟨175749524050236364960403953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234332698733648486613871937 175749524050236364960403953)
          ·
            refine ⟨131812143037677273720302965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175749524050236364960403953 131812143037677273720302965)
            ·
              refine ⟨12357388409782244411278403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131812143037677273720302965 12357388409782244411278403)
              ·
                refine ⟨18536082614673366616917605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12357388409782244411278403 18536082614673366616917605)
                ·
                  refine ⟨3475515490251256240672051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18536082614673366616917605 3475515490251256240672051)
                  ·
                    refine ⟨5213273235376884361008077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3475515490251256240672051 5213273235376884361008077)
                    ·
                      refine ⟨1954977463266331635378029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5213273235376884361008077 1954977463266331635378029)
                      ·
                        rfl

theorem cell23_3807305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_3807305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807305 prefixEnd_3807305 := by exact prefixLift 3807305
  have htrace : WordTrace (prefixWord ++ tailWord_3807305) baseStart_3807305 baseEnd_3807305 := by
    simpa [prefixWord, tailWord_3807305, baseEnd_3807305] using wordTrace_append hprefix tailTrace_3807305
  have hstable : (prefixWord ++ tailWord_3807305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807305).length < 2 ^ (prefixWord ++ tailWord_3807305).sum := by decide
  have hdescent : baseEnd_3807305 < baseStart_3807305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807332 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_3807332 : Nat := 118140960795 + 3807332 * 2 ^ 59
def prefixEnd_3807332 : Nat := 4983230072969 + 3 ^ 40 * 3807332 * 2
def baseEnd_3807332 : Nat := 1954991327244003029740405

theorem tailTrace_3807332 : CollatzResearch.WordTrace tailWord_3807332 prefixEnd_3807332 1954991327244003029740405 := by
  unfold tailWord_3807332
  simp only [CollatzResearch.WordTrace]
  refine ⟨69432403121346939691208125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92576537495129252921610833 69432403121346939691208125)
  ·
    refine ⟨26037151170505102384203047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69432403121346939691208125 26037151170505102384203047)
    ·
      refine ⟨39055726755757653576304571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26037151170505102384203047 39055726755757653576304571)
      ·
        refine ⟨58583590133636480364456857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39055726755757653576304571 58583590133636480364456857)
        ·
          refine ⟨43937692600227360273342643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58583590133636480364456857 43937692600227360273342643)
          ·
            refine ⟨65906538900341040410013965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43937692600227360273342643 65906538900341040410013965)
            ·
              refine ⟨24714952087627890153755237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65906538900341040410013965 24714952087627890153755237)
              ·
                refine ⟨4634053516430229403829107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24714952087627890153755237 4634053516430229403829107)
                ·
                  refine ⟨6951080274645344105743661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634053516430229403829107 6951080274645344105743661)
                  ·
                    refine ⟨2606655102992004039653873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6951080274645344105743661 2606655102992004039653873)
                    ·
                      refine ⟨1954991327244003029740405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606655102992004039653873 1954991327244003029740405)
                      ·
                        rfl

theorem cell23_3807332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_3807332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807332 prefixEnd_3807332 := by exact prefixLift 3807332
  have htrace : WordTrace (prefixWord ++ tailWord_3807332) baseStart_3807332 baseEnd_3807332 := by
    simpa [prefixWord, tailWord_3807332, baseEnd_3807332] using wordTrace_append hprefix tailTrace_3807332
  have hstable : (prefixWord ++ tailWord_3807332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807332).length < 2 ^ (prefixWord ++ tailWord_3807332).sum := by decide
  have hdescent : baseEnd_3807332 < baseStart_3807332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807345 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 3, 4, 2]
def baseStart_3807345 : Nat := 118140960795 + 3807345 * 2 ^ 59
def prefixEnd_3807345 : Nat := 4983230072969 + 3 ^ 40 * 3807345 * 2
def baseEnd_3807345 : Nat := 1954998002492511478877845

theorem tailTrace_3807345 : CollatzResearch.WordTrace tailWord_3807345 prefixEnd_3807345 1954998002492511478877845 := by
  unfold tailWord_3807345
  simp only [CollatzResearch.WordTrace]
  refine ⟨138865280391646782602639489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92576853594431188401759659 138865280391646782602639489)
  ·
    refine ⟨104148960293735086951979617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138865280391646782602639489 104148960293735086951979617)
    ·
      refine ⟨78111720220301315213984713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104148960293735086951979617 78111720220301315213984713)
      ·
        refine ⟨58583790165225986410488535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78111720220301315213984713 58583790165225986410488535)
        ·
          refine ⟨87875685247838979615732803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58583790165225986410488535 87875685247838979615732803)
          ·
            refine ⟨131813527871758469423599205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87875685247838979615732803 131813527871758469423599205)
            ·
              refine ⟨24715036475954713016924851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131813527871758469423599205 24715036475954713016924851)
              ·
                refine ⟨37072554713932069525387277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24715036475954713016924851 37072554713932069525387277)
                ·
                  refine ⟨13902208017724526072020229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37072554713932069525387277 13902208017724526072020229)
                  ·
                    refine ⟨2606664003323348638503793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13902208017724526072020229 2606664003323348638503793)
                    ·
                      refine ⟨1954998002492511478877845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606664003323348638503793 1954998002492511478877845)
                      ·
                        rfl

theorem cell23_3807345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_3807345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807345 prefixEnd_3807345 := by exact prefixLift 3807345
  have htrace : WordTrace (prefixWord ++ tailWord_3807345) baseStart_3807345 baseEnd_3807345 := by
    simpa [prefixWord, tailWord_3807345, baseEnd_3807345] using wordTrace_append hprefix tailTrace_3807345
  have hstable : (prefixWord ++ tailWord_3807345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807345).length < 2 ^ (prefixWord ++ tailWord_3807345).sum := by decide
  have hdescent : baseEnd_3807345 < baseStart_3807345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807413 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3807413 : Nat := 118140960795 + 3807413 * 2 ^ 59
def prefixEnd_3807413 : Nat := 4983230072969 + 3 ^ 40 * 3807413 * 2
def baseEnd_3807413 : Nat := 1955032919177017212827533

theorem tailTrace_3807413 : CollatzResearch.WordTrace tailWord_3807413 prefixEnd_3807413 1955032919177017212827533 := by
  unfold tailWord_3807413
  simp only [CollatzResearch.WordTrace]
  refine ⟨138867760555400430216114893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92578507036933620144076595 138867760555400430216114893)
  ·
    refine ⟨52075410208275161331043085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138867760555400430216114893 52075410208275161331043085)
    ·
      refine ⟨19528278828103185499141157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52075410208275161331043085 19528278828103185499141157)
      ·
        refine ⟨3661552280269347281088967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19528278828103185499141157 3661552280269347281088967)
        ·
          refine ⟨5492328420404020921633451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661552280269347281088967 5492328420404020921633451)
          ·
            refine ⟨8238492630606031382450177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492328420404020921633451 8238492630606031382450177)
            ·
              refine ⟨6178869472954523536837633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8238492630606031382450177 6178869472954523536837633)
              ·
                refine ⟨4634152104715892652628225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6178869472954523536837633 4634152104715892652628225)
                ·
                  refine ⟨3475614078536919489471169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4634152104715892652628225 3475614078536919489471169)
                  ·
                    refine ⟨2606710558902689617103377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3475614078536919489471169 2606710558902689617103377)
                    ·
                      refine ⟨1955032919177017212827533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606710558902689617103377 1955032919177017212827533)
                      ·
                        rfl

theorem cell23_3807413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3807413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807413 prefixEnd_3807413 := by exact prefixLift 3807413
  have htrace : WordTrace (prefixWord ++ tailWord_3807413) baseStart_3807413 baseEnd_3807413 := by
    simpa [prefixWord, tailWord_3807413, baseEnd_3807413] using wordTrace_append hprefix tailTrace_3807413
  have hstable : (prefixWord ++ tailWord_3807413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807413).length < 2 ^ (prefixWord ++ tailWord_3807413).sum := by decide
  have hdescent : baseEnd_3807413 < baseStart_3807413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807415 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 2, 5]
def baseStart_3807415 : Nat := 118140960795 + 3807415 * 2 ^ 59
def prefixEnd_3807415 : Nat := 4983230072969 + 3 ^ 40 * 3807415 * 2
def baseEnd_3807415 : Nat := 651677982046108735000841

theorem tailTrace_3807415 : CollatzResearch.WordTrace tailWord_3807415 prefixEnd_3807415 651677982046108735000841 := by
  unfold tailWord_3807415
  simp only [CollatzResearch.WordTrace]
  refine ⟨138867833501393184557687699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92578555667595456371791799 138867833501393184557687699)
  ·
    refine ⟨208301750252089776836531549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138867833501393184557687699 208301750252089776836531549)
    ·
      refine ⟨78113156344533666313699331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208301750252089776836531549 78113156344533666313699331)
      ·
        refine ⟨117169734516800499470548997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78113156344533666313699331 117169734516800499470548997)
        ·
          refine ⟨21969325221900093650727937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117169734516800499470548997 21969325221900093650727937)
          ·
            refine ⟨16476993916425070238045953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21969325221900093650727937 16476993916425070238045953)
            ·
              refine ⟨12357745437318802678534465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16476993916425070238045953 12357745437318802678534465)
              ·
                refine ⟨9268309077989102008900849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12357745437318802678534465 9268309077989102008900849)
                ·
                  refine ⟨6951231808491826506675637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9268309077989102008900849 6951231808491826506675637)
                  ·
                    refine ⟨651677982046108735000841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6951231808491826506675637 651677982046108735000841)
                    ·
                      rfl

theorem cell23_3807415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_3807415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807415 prefixEnd_3807415 := by exact prefixLift 3807415
  have htrace : WordTrace (prefixWord ++ tailWord_3807415) baseStart_3807415 baseEnd_3807415 := by
    simpa [prefixWord, tailWord_3807415, baseEnd_3807415] using wordTrace_append hprefix tailTrace_3807415
  have hstable : (prefixWord ++ tailWord_3807415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807415).length < 2 ^ (prefixWord ++ tailWord_3807415).sum := by decide
  have hdescent : baseEnd_3807415 < baseStart_3807415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807512 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 1, 5, 2]
def baseStart_3807512 : Nat := 118140960795 + 3807512 * 2 ^ 59
def prefixEnd_3807512 : Nat := 4983230072969 + 3 ^ 40 * 3807512 * 2
def baseEnd_3807512 : Nat := 1955083753761812325489577

theorem tailTrace_3807512 : CollatzResearch.WordTrace tailWord_3807512 prefixEnd_3807512 1955083753761812325489577 := by
  unfold tailWord_3807512
  simp only [CollatzResearch.WordTrace]
  refine ⟨69435685691020885061984395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92580914254694513415979193 69435685691020885061984395)
  ·
    refine ⟨104153528536531327592976593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69435685691020885061984395 104153528536531327592976593)
    ·
      refine ⟨78115146402398495694732445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104153528536531327592976593 78115146402398495694732445)
      ·
        refine ⟨29293179900899435885524667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78115146402398495694732445 29293179900899435885524667)
        ·
          refine ⟨43939769851349153828287001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29293179900899435885524667 43939769851349153828287001)
          ·
            refine ⟨32954827388511865371215251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43939769851349153828287001 32954827388511865371215251)
            ·
              refine ⟨49432241082767798056822877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32954827388511865371215251 49432241082767798056822877)
              ·
                refine ⟨18537090406037924271308579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49432241082767798056822877 18537090406037924271308579)
                ·
                  refine ⟨27805635609056886406962869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18537090406037924271308579 27805635609056886406962869)
                  ·
                    refine ⟨2606778338349083100652769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27805635609056886406962869 2606778338349083100652769)
                    ·
                      refine ⟨1955083753761812325489577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606778338349083100652769 1955083753761812325489577)
                      ·
                        rfl

theorem cell23_3807512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_3807512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807512 prefixEnd_3807512 := by exact prefixLift 3807512
  have htrace : WordTrace (prefixWord ++ tailWord_3807512) baseStart_3807512 baseEnd_3807512 := by
    simpa [prefixWord, tailWord_3807512, baseEnd_3807512] using wordTrace_append hprefix tailTrace_3807512
  have hstable : (prefixWord ++ tailWord_3807512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807512).length < 2 ^ (prefixWord ++ tailWord_3807512).sum := by decide
  have hdescent : baseEnd_3807512 < baseStart_3807512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807555 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6]
def baseStart_3807555 : Nat := 118140960795 + 3807555 * 2 ^ 59
def prefixEnd_3807555 : Nat := 4983230072969 + 3 ^ 40 * 3807555 * 2
def baseEnd_3807555 : Nat := 1955105833429955657251879

theorem tailTrace_3807555 : CollatzResearch.WordTrace tailWord_3807555 prefixEnd_3807555 1955105833429955657251879 := by
  unfold tailWord_3807555
  simp only [CollatzResearch.WordTrace]
  refine ⟨138872939720885988467784119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92581959813923992311856079 138872939720885988467784119)
  ·
    refine ⟨208309409581328982701676179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138872939720885988467784119 208309409581328982701676179)
    ·
      refine ⟨312464114371993474052514269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208309409581328982701676179 312464114371993474052514269)
      ·
        refine ⟨117174042889497552769692851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312464114371993474052514269 117174042889497552769692851)
        ·
          refine ⟨175761064334246329154539277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117174042889497552769692851 175761064334246329154539277)
          ·
            refine ⟨65910399125342373432952229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175761064334246329154539277 65910399125342373432952229)
            ·
              refine ⟨12358199836001695018678543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65910399125342373432952229 12358199836001695018678543)
              ·
                refine ⟨18537299754002542528017815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12358199836001695018678543 18537299754002542528017815)
                ·
                  refine ⟨27805949631003813792026723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18537299754002542528017815 27805949631003813792026723)
                  ·
                    refine ⟨41708924446505720688040085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27805949631003813792026723 41708924446505720688040085)
                    ·
                      refine ⟨1955105833429955657251879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41708924446505720688040085 1955105833429955657251879)
                      ·
                        rfl

theorem cell23_3807555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_3807555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807555 prefixEnd_3807555 := by exact prefixLift 3807555
  have htrace : WordTrace (prefixWord ++ tailWord_3807555) baseStart_3807555 baseEnd_3807555 := by
    simpa [prefixWord, tailWord_3807555, baseEnd_3807555] using wordTrace_append hprefix tailTrace_3807555
  have hstable : (prefixWord ++ tailWord_3807555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807555).length < 2 ^ (prefixWord ++ tailWord_3807555).sum := by decide
  have hdescent : baseEnd_3807555 < baseStart_3807555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807559 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_3807559 : Nat := 118140960795 + 3807559 * 2 ^ 59
def prefixEnd_3807559 : Nat := 4983230072969 + 3 ^ 40 * 3807559 * 2
def baseEnd_3807559 : Nat := 1955107887352573641601861

theorem tailTrace_3807559 : CollatzResearch.WordTrace tailWord_3807559 prefixEnd_3807559 1955107887352573641601861 := by
  unfold tailWord_3807559
  simp only [CollatzResearch.WordTrace]
  refine ⟨138873085612871497150929731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92582057075247664767286487 138873085612871497150929731)
  ·
    refine ⟨208309628419307245726394597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138873085612871497150929731 208309628419307245726394597)
    ·
      refine ⟨39058055328620108573698987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208309628419307245726394597 39058055328620108573698987)
      ·
        refine ⟨58587082992930162860548481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39058055328620108573698987 58587082992930162860548481)
        ·
          refine ⟨43940312244697622145411361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58587082992930162860548481 43940312244697622145411361)
          ·
            refine ⟨32955234183523216609058521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43940312244697622145411361 32955234183523216609058521)
            ·
              refine ⟨24716425637642412456793891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32955234183523216609058521 24716425637642412456793891)
              ·
                refine ⟨37074638456463618685190837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24716425637642412456793891 37074638456463618685190837)
                ·
                  refine ⟨3475747355293464251736641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37074638456463618685190837 3475747355293464251736641)
                  ·
                    refine ⟨2606810516470098188802481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3475747355293464251736641 2606810516470098188802481)
                    ·
                      refine ⟨1955107887352573641601861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606810516470098188802481 1955107887352573641601861)
                      ·
                        rfl

theorem cell23_3807559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_3807559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807559 prefixEnd_3807559 := by exact prefixLift 3807559
  have htrace : WordTrace (prefixWord ++ tailWord_3807559) baseStart_3807559 baseEnd_3807559 := by
    simpa [prefixWord, tailWord_3807559, baseEnd_3807559] using wordTrace_append hprefix tailTrace_3807559
  have hstable : (prefixWord ++ tailWord_3807559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807559).length < 2 ^ (prefixWord ++ tailWord_3807559).sum := by decide
  have hdescent : baseEnd_3807559 < baseStart_3807559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807572 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3807572 : Nat := 118140960795 + 3807572 * 2 ^ 59
def prefixEnd_3807572 : Nat := 4983230072969 + 3 ^ 40 * 3807572 * 2
def baseEnd_3807572 : Nat := 1955114562601082090739301

theorem tailTrace_3807572 : CollatzResearch.WordTrace tailWord_3807572 prefixEnd_3807572 1955114562601082090739301 := by
  unfold tailWord_3807572
  simp only [CollatzResearch.WordTrace]
  refine ⟨69436779880912200185576485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92582373174549600247435313 69436779880912200185576485)
  ·
    refine ⟨13019396227671037534795591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69436779880912200185576485 13019396227671037534795591)
    ·
      refine ⟨19529094341506556302193387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13019396227671037534795591 19529094341506556302193387)
      ·
        refine ⟨29293641512259834453290081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19529094341506556302193387 29293641512259834453290081)
        ·
          refine ⟨21970231134194875839967561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29293641512259834453290081 21970231134194875839967561)
          ·
            refine ⟨16477673350646156879975671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21970231134194875839967561 16477673350646156879975671)
            ·
              refine ⟨24716510025969235319963507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477673350646156879975671 24716510025969235319963507)
              ·
                refine ⟨37074765038953852979945261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24716510025969235319963507 37074765038953852979945261)
                ·
                  refine ⟨13903036889607694867479473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37074765038953852979945261 13903036889607694867479473)
                  ·
                    refine ⟨10427277667205771150609605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13903036889607694867479473 10427277667205771150609605)
                    ·
                      refine ⟨1955114562601082090739301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10427277667205771150609605 1955114562601082090739301)
                      ·
                        rfl

theorem cell23_3807572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3807572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807572 prefixEnd_3807572 := by exact prefixLift 3807572
  have htrace : WordTrace (prefixWord ++ tailWord_3807572) baseStart_3807572 baseEnd_3807572 := by
    simpa [prefixWord, tailWord_3807572, baseEnd_3807572] using wordTrace_append hprefix tailTrace_3807572
  have hstable : (prefixWord ++ tailWord_3807572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807572).length < 2 ^ (prefixWord ++ tailWord_3807572).sum := by decide
  have hdescent : baseEnd_3807572 < baseStart_3807572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807586 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3807586 : Nat := 118140960795 + 3807586 * 2 ^ 59
def prefixEnd_3807586 : Nat := 4983230072969 + 3 ^ 40 * 3807586 * 2
def baseEnd_3807586 : Nat := 651707250443415011988079

theorem tailTrace_3807586 : CollatzResearch.WordTrace tailWord_3807586 prefixEnd_3807586 651707250443415011988079 := by
  unfold tailWord_3807586
  simp only [CollatzResearch.WordTrace]
  refine ⟨34718517595943420190540653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92582713589182453841441741 34718517595943420190540653)
  ·
    refine ⟨13019444098478782571452745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34718517595943420190540653 13019444098478782571452745)
    ·
      refine ⟨9764583073859086928589559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13019444098478782571452745 9764583073859086928589559)
      ·
        refine ⟨14646874610788630392884339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9764583073859086928589559 14646874610788630392884339)
        ·
          refine ⟨21970311916182945589326509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14646874610788630392884339 21970311916182945589326509)
          ·
            refine ⟨8238866968568604595997441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21970311916182945589326509 8238866968568604595997441)
            ·
              refine ⟨6179150226426453446998081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8238866968568604595997441 6179150226426453446998081)
              ·
                refine ⟨4634362669819840085248561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6179150226426453446998081 4634362669819840085248561)
                ·
                  refine ⟨3475772002364880063936421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4634362669819840085248561 3475772002364880063936421)
                  ·
                    refine ⟨651707250443415011988079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3475772002364880063936421 651707250443415011988079)
                    ·
                      rfl

theorem cell23_3807586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3807586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807586 prefixEnd_3807586 := by exact prefixLift 3807586
  have htrace : WordTrace (prefixWord ++ tailWord_3807586) baseStart_3807586 baseEnd_3807586 := by
    simpa [prefixWord, tailWord_3807586, baseEnd_3807586] using wordTrace_append hprefix tailTrace_3807586
  have hstable : (prefixWord ++ tailWord_3807586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807586).length < 2 ^ (prefixWord ++ tailWord_3807586).sum := by decide
  have hdescent : baseEnd_3807586 < baseStart_3807586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807642 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_3807642 : Nat := 118140960795 + 3807642 * 2 ^ 59
def prefixEnd_3807642 : Nat := 4983230072969 + 3 ^ 40 * 3807642 * 2
def baseEnd_3807642 : Nat := 651716835415632272287993

theorem tailTrace_3807642 : CollatzResearch.WordTrace tailWord_3807642 prefixEnd_3807642 651716835415632272287993 := by
  unfold tailWord_3807642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34719028217892700581550295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92584075247713868217467453 34719028217892700581550295)
  ·
    refine ⟨52078542326839050872325443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34719028217892700581550295 52078542326839050872325443)
    ·
      refine ⟨78117813490258576308488165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52078542326839050872325443 78117813490258576308488165)
      ·
        refine ⟨14647090029423483057841531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78117813490258576308488165 14647090029423483057841531)
        ·
          refine ⟨21970635044135224586762297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14647090029423483057841531 21970635044135224586762297)
          ·
            refine ⟨16477976283101418440071723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21970635044135224586762297 16477976283101418440071723)
            ·
              refine ⟨24716964424652127660107585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477976283101418440071723 24716964424652127660107585)
              ·
                refine ⟨18537723318489095745080689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24716964424652127660107585 18537723318489095745080689)
                ·
                  refine ⟨13903292488866821808810517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18537723318489095745080689 13903292488866821808810517)
                  ·
                    refine ⟨651716835415632272287993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13903292488866821808810517 651716835415632272287993)
                    ·
                      rfl

theorem cell23_3807642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_3807642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807642 prefixEnd_3807642 := by exact prefixLift 3807642
  have htrace : WordTrace (prefixWord ++ tailWord_3807642) baseStart_3807642 baseEnd_3807642 := by
    simpa [prefixWord, tailWord_3807642, baseEnd_3807642] using wordTrace_append hprefix tailTrace_3807642
  have hstable : (prefixWord ++ tailWord_3807642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807642).length < 2 ^ (prefixWord ++ tailWord_3807642).sum := by decide
  have hdescent : baseEnd_3807642 < baseStart_3807642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807652 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3807652 : Nat := 118140960795 + 3807652 * 2 ^ 59
def prefixEnd_3807652 : Nat := 4983230072969 + 3 ^ 40 * 3807652 * 2
def baseEnd_3807652 : Nat := 1955155641053441777738933

theorem tailTrace_3807652 : CollatzResearch.WordTrace tailWord_3807652 prefixEnd_3807652 1955155641053441777738933 := by
  unfold tailWord_3807652
  simp only [CollatzResearch.WordTrace]
  refine ⟨69438238800767287017032605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92584318401023049356043473 69438238800767287017032605)
  ·
    refine ⟨26039339550287732631387227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69438238800767287017032605 26039339550287732631387227)
    ·
      refine ⟨39059009325431598947080841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26039339550287732631387227 39059009325431598947080841)
      ·
        refine ⟨29294256994073699210310631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39059009325431598947080841 29294256994073699210310631)
        ·
          refine ⟨43941385491110548815465947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29294256994073699210310631 43941385491110548815465947)
          ·
            refine ⟨65912078236665823223198921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43941385491110548815465947 65912078236665823223198921)
            ·
              refine ⟨49434058677499367417399191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65912078236665823223198921 49434058677499367417399191)
              ·
                refine ⟨74151088016249051126098787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49434058677499367417399191 74151088016249051126098787)
                ·
                  refine ⟨111226632024373576689148181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74151088016249051126098787 111226632024373576689148181)
                  ·
                    refine ⟨5213748376142511407303821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111226632024373576689148181 5213748376142511407303821)
                    ·
                      refine ⟨1955155641053441777738933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5213748376142511407303821 1955155641053441777738933)
                      ·
                        rfl

theorem cell23_3807652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3807652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807652 prefixEnd_3807652 := by exact prefixLift 3807652
  have htrace : WordTrace (prefixWord ++ tailWord_3807652) baseStart_3807652 baseEnd_3807652 := by
    simpa [prefixWord, tailWord_3807652, baseEnd_3807652] using wordTrace_append hprefix tailTrace_3807652
  have hstable : (prefixWord ++ tailWord_3807652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807652).length < 2 ^ (prefixWord ++ tailWord_3807652).sum := by decide
  have hdescent : baseEnd_3807652 < baseStart_3807652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807675 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_3807675 : Nat := 118140960795 + 3807675 * 2 ^ 59
def prefixEnd_3807675 : Nat := 4983230072969 + 3 ^ 40 * 3807675 * 2
def baseEnd_3807675 : Nat := 1955167451108495187751327

theorem tailTrace_3807675 : CollatzResearch.WordTrace tailWord_3807675 prefixEnd_3807675 1955167451108495187751327 := by
  unfold tailWord_3807675
  simp only [CollatzResearch.WordTrace]
  refine ⟨138877316480451248962152479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92584877653634165974768319 138877316480451248962152479)
  ·
    refine ⟨208315974720676873443228719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138877316480451248962152479 208315974720676873443228719)
    ·
      refine ⟨312473962081015310164843079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208315974720676873443228719 312473962081015310164843079)
      ·
        refine ⟨468710943121522965247264619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312473962081015310164843079 468710943121522965247264619)
        ·
          refine ⟨703066414682284447870896929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468710943121522965247264619 703066414682284447870896929)
          ·
            refine ⟨527299811011713335903172697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703066414682284447870896929 527299811011713335903172697)
            ·
              refine ⟨395474858258785001927379523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527299811011713335903172697 395474858258785001927379523)
              ·
                refine ⟨593212287388177502891069285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395474858258785001927379523 593212287388177502891069285)
                ·
                  refine ⟨111227303885283281792075491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593212287388177502891069285 111227303885283281792075491)
                  ·
                    refine ⟨166840955827924922688113237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111227303885283281792075491 166840955827924922688113237)
                    ·
                      refine ⟨1955167451108495187751327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 166840955827924922688113237 1955167451108495187751327)
                      ·
                        rfl

theorem cell23_3807675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_3807675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807675 prefixEnd_3807675 := by exact prefixLift 3807675
  have htrace : WordTrace (prefixWord ++ tailWord_3807675) baseStart_3807675 baseEnd_3807675 := by
    simpa [prefixWord, tailWord_3807675, baseEnd_3807675] using wordTrace_append hprefix tailTrace_3807675
  have hstable : (prefixWord ++ tailWord_3807675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807675).length < 2 ^ (prefixWord ++ tailWord_3807675).sum := by decide
  have hdescent : baseEnd_3807675 < baseStart_3807675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807689 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 5]
def baseStart_3807689 : Nat := 118140960795 + 3807689 * 2 ^ 59
def prefixEnd_3807689 : Nat := 4983230072969 + 3 ^ 40 * 3807689 * 2
def baseEnd_3807689 : Nat := 217241626648628681441807

theorem tailTrace_3807689 : CollatzResearch.WordTrace tailWord_3807689 prefixEnd_3807689 217241626648628681441807 := by
  unfold tailWord_3807689
  simp only [CollatzResearch.WordTrace]
  refine ⟨138877827102400529353162121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92585218068267019568774747 138877827102400529353162121)
  ·
    refine ⟨104158370326800397014871591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138877827102400529353162121 104158370326800397014871591)
    ·
      refine ⟨156237555490200595522307387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104158370326800397014871591 156237555490200595522307387)
      ·
        refine ⟨234356333235300893283461081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156237555490200595522307387 234356333235300893283461081)
        ·
          refine ⟨175767249926475669962595811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234356333235300893283461081 175767249926475669962595811)
          ·
            refine ⟨263650874889713504943893717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175767249926475669962595811 263650874889713504943893717)
            ·
              refine ⟨6179317380227660272122509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 263650874889713504943893717 6179317380227660272122509)
              ·
                refine ⟨2317244017585372602045941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6179317380227660272122509 2317244017585372602045941)
                ·
                  refine ⟨217241626648628681441807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2317244017585372602045941 217241626648628681441807)
                  ·
                    rfl

theorem cell23_3807689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 5].length) (baseStart_3807689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807689 prefixEnd_3807689 := by exact prefixLift 3807689
  have htrace : WordTrace (prefixWord ++ tailWord_3807689) baseStart_3807689 baseEnd_3807689 := by
    simpa [prefixWord, tailWord_3807689, baseEnd_3807689] using wordTrace_append hprefix tailTrace_3807689
  have hstable : (prefixWord ++ tailWord_3807689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807689).length < 2 ^ (prefixWord ++ tailWord_3807689).sum := by decide
  have hdescent : baseEnd_3807689 < baseStart_3807689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807706 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_3807706 : Nat := 118140960795 + 3807706 * 2 ^ 59
def prefixEnd_3807706 : Nat := 4983230072969 + 3 ^ 40 * 3807706 * 2
def baseEnd_3807706 : Nat := 217242596556531618495965

theorem tailTrace_3807706 : CollatzResearch.WordTrace tailWord_3807706 prefixEnd_3807706 217242596556531618495965 := by
  unfold tailWord_3807706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34719611785834735314132743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92585631428892627504353981 34719611785834735314132743)
  ·
    refine ⟨52079417678752102971199115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34719611785834735314132743 52079417678752102971199115)
    ·
      refine ⟨78119126518128154456798673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52079417678752102971199115 78119126518128154456798673)
      ·
        refine ⟨58589344888596115842599005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78119126518128154456798673 58589344888596115842599005)
        ·
          refine ⟨21971004333223543440974627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58589344888596115842599005 21971004333223543440974627)
          ·
            refine ⟨32956506499835315161461941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21971004333223543440974627 32956506499835315161461941)
            ·
              refine ⟨3089672484359560796387057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32956506499835315161461941 3089672484359560796387057)
              ·
                refine ⟨2317254363269670597290293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089672484359560796387057 2317254363269670597290293)
                ·
                  refine ⟨217242596556531618495965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2317254363269670597290293 217242596556531618495965)
                  ·
                    rfl

theorem cell23_3807706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_3807706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807706 prefixEnd_3807706 := by exact prefixLift 3807706
  have htrace : WordTrace (prefixWord ++ tailWord_3807706) baseStart_3807706 baseEnd_3807706 := by
    simpa [prefixWord, tailWord_3807706, baseEnd_3807706] using wordTrace_append hprefix tailTrace_3807706
  have hstable : (prefixWord ++ tailWord_3807706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807706).length < 2 ^ (prefixWord ++ tailWord_3807706).sum := by decide
  have hdescent : baseEnd_3807706 < baseStart_3807706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807712 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_3807712 : Nat := 118140960795 + 3807712 * 2 ^ 59
def prefixEnd_3807712 : Nat := 4983230072969 + 3 ^ 40 * 3807712 * 2
def baseEnd_3807712 : Nat := 1955186449892711542988657

theorem tailTrace_3807712 : CollatzResearch.WordTrace tailWord_3807712 prefixEnd_3807712 1955186449892711542988657 := by
  unfold tailWord_3807712
  simp only [CollatzResearch.WordTrace]
  refine ⟨69439332990658602140624695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92585777320878136187499593 69439332990658602140624695)
  ·
    refine ⟨104158999485987903210937043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69439332990658602140624695 104158999485987903210937043)
    ·
      refine ⟨156238499228981854816405565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104158999485987903210937043 156238499228981854816405565)
      ·
        refine ⟨58589437210868195556152087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156238499228981854816405565 58589437210868195556152087)
        ·
          refine ⟨87884155816302293334228131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58589437210868195556152087 87884155816302293334228131)
          ·
            refine ⟨131826233724453440001342197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87884155816302293334228131 131826233724453440001342197)
            ·
              refine ⟨12358709411667510000125831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131826233724453440001342197 12358709411667510000125831)
              ·
                refine ⟨18538064117501265000188747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12358709411667510000125831 18538064117501265000188747)
                ·
                  refine ⟨27807096176251897500283121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18538064117501265000188747 27807096176251897500283121)
                  ·
                    refine ⟨20855322132188923125212341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27807096176251897500283121 20855322132188923125212341)
                    ·
                      refine ⟨1955186449892711542988657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20855322132188923125212341 1955186449892711542988657)
                      ·
                        rfl

theorem cell23_3807712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_3807712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807712 prefixEnd_3807712 := by exact prefixLift 3807712
  have htrace : WordTrace (prefixWord ++ tailWord_3807712) baseStart_3807712 baseEnd_3807712 := by
    simpa [prefixWord, tailWord_3807712, baseEnd_3807712] using wordTrace_append hprefix tailTrace_3807712
  have hstable : (prefixWord ++ tailWord_3807712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807712).length < 2 ^ (prefixWord ++ tailWord_3807712).sum := by decide
  have hdescent : baseEnd_3807712 < baseStart_3807712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807717 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3807717 : Nat := 118140960795 + 3807717 * 2 ^ 59
def prefixEnd_3807717 : Nat := 4983230072969 + 3 ^ 40 * 3807717 * 2
def baseEnd_3807717 : Nat := 1955189017295984023426135

theorem tailTrace_3807717 : CollatzResearch.WordTrace tailWord_3807717 prefixEnd_3807717 1955189017295984023426135 := by
  unfold tailWord_3807717
  simp only [CollatzResearch.WordTrace]
  refine ⟨138878848346299090135181405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92585898897532726756787603 138878848346299090135181405)
  ·
    refine ⟨52079568129862158800693027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138878848346299090135181405 52079568129862158800693027)
    ·
      refine ⟨78119352194793238201039541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52079568129862158800693027 78119352194793238201039541)
      ·
        refine ⟨7323689268261866081347457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78119352194793238201039541 7323689268261866081347457)
        ·
          refine ⟨5492766951196399561010593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7323689268261866081347457 5492766951196399561010593)
          ·
            refine ⟨4119575213397299670757945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492766951196399561010593 4119575213397299670757945)
            ·
              refine ⟨3089681410047974753068459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119575213397299670757945 3089681410047974753068459)
              ·
                refine ⟨4634522115071962129602689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089681410047974753068459 4634522115071962129602689)
                ·
                  refine ⟨3475891586303971597202017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4634522115071962129602689 3475891586303971597202017)
                  ·
                    refine ⟨2606918689727978697901513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3475891586303971597202017 2606918689727978697901513)
                    ·
                      refine ⟨1955189017295984023426135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606918689727978697901513 1955189017295984023426135)
                      ·
                        rfl

theorem cell23_3807717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3807717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807717 prefixEnd_3807717 := by exact prefixLift 3807717
  have htrace : WordTrace (prefixWord ++ tailWord_3807717) baseStart_3807717 baseEnd_3807717 := by
    simpa [prefixWord, tailWord_3807717, baseEnd_3807717] using wordTrace_append hprefix tailTrace_3807717
  have hstable : (prefixWord ++ tailWord_3807717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807717).length < 2 ^ (prefixWord ++ tailWord_3807717).sum := by decide
  have hdescent : baseEnd_3807717 < baseStart_3807717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807752 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3807752 : Nat := 118140960795 + 3807752 * 2 ^ 59
def prefixEnd_3807752 : Nat := 4983230072969 + 3 ^ 40 * 3807752 * 2
def baseEnd_3807752 : Nat := 1955206989118891386488473

theorem tailTrace_3807752 : CollatzResearch.WordTrace tailWord_3807752 prefixEnd_3807752 1955206989118891386488473 := by
  unfold tailWord_3807752
  simp only [CollatzResearch.WordTrace]
  refine ⟨69440062450586145556352755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92586749934114860741803673 69440062450586145556352755)
  ·
    refine ⟨104160093675879218334529133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69440062450586145556352755 104160093675879218334529133)
    ·
      refine ⟨39060035128454706875448425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104160093675879218334529133 39060035128454706875448425)
      ·
        refine ⟨29295026346341030156586319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39060035128454706875448425 29295026346341030156586319)
        ·
          refine ⟨43942539519511545234879479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29295026346341030156586319 43942539519511545234879479)
          ·
            refine ⟨65913809279267317852319219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43942539519511545234879479 65913809279267317852319219)
            ·
              refine ⟨98870713918900976778478829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65913809279267317852319219 98870713918900976778478829)
              ·
                refine ⟨37076517719587866291929561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98870713918900976778478829 37076517719587866291929561)
                ·
                  refine ⟨27807388289690899718947171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37076517719587866291929561 27807388289690899718947171)
                  ·
                    refine ⟨41711082434536349578420757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27807388289690899718947171 41711082434536349578420757)
                    ·
                      refine ⟨1955206989118891386488473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41711082434536349578420757 1955206989118891386488473)
                      ·
                        rfl

theorem cell23_3807752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3807752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807752 prefixEnd_3807752 := by exact prefixLift 3807752
  have htrace : WordTrace (prefixWord ++ tailWord_3807752) baseStart_3807752 baseEnd_3807752 := by
    simpa [prefixWord, tailWord_3807752, baseEnd_3807752] using wordTrace_append hprefix tailTrace_3807752
  have hstable : (prefixWord ++ tailWord_3807752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807752).length < 2 ^ (prefixWord ++ tailWord_3807752).sum := by decide
  have hdescent : baseEnd_3807752 < baseStart_3807752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807757 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3807757 : Nat := 118140960795 + 3807757 * 2 ^ 59
def prefixEnd_3807757 : Nat := 4983230072969 + 3 ^ 40 * 3807757 * 2
def baseEnd_3807757 : Nat := 217245506280240429658439

theorem tailTrace_3807757 : CollatzResearch.WordTrace tailWord_3807757 prefixEnd_3807757 217245506280240429658439 := by
  unfold tailWord_3807757
  simp only [CollatzResearch.WordTrace]
  refine ⟨138880307266154176966637525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92586871510769451311091683 138880307266154176966637525)
  ·
    refine ⟨3255007201550488522655567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 138880307266154176966637525 3255007201550488522655567)
    ·
      refine ⟨4882510802325732783983351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3255007201550488522655567 4882510802325732783983351)
      ·
        refine ⟨7323766203488599175975027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882510802325732783983351 7323766203488599175975027)
        ·
          refine ⟨10985649305232898763962541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323766203488599175975027 10985649305232898763962541)
          ·
            refine ⟨4119618489462337036485953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10985649305232898763962541 4119618489462337036485953)
            ·
              refine ⟨3089713867096752777364465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119618489462337036485953 3089713867096752777364465)
              ·
                refine ⟨2317285400322564583023349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089713867096752777364465 2317285400322564583023349)
                ·
                  refine ⟨217245506280240429658439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2317285400322564583023349 217245506280240429658439)
                  ·
                    rfl

theorem cell23_3807757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3807757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807757 prefixEnd_3807757 := by exact prefixLift 3807757
  have htrace : WordTrace (prefixWord ++ tailWord_3807757) baseStart_3807757 baseEnd_3807757 := by
    simpa [prefixWord, tailWord_3807757, baseEnd_3807757] using wordTrace_append hprefix tailTrace_3807757
  have hstable : (prefixWord ++ tailWord_3807757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807757).length < 2 ^ (prefixWord ++ tailWord_3807757).sum := by decide
  have hdescent : baseEnd_3807757 < baseStart_3807757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807779 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 6]
def baseStart_3807779 : Nat := 118140960795 + 3807779 * 2 ^ 59
def prefixEnd_3807779 : Nat := 4983230072969 + 3 ^ 40 * 3807779 * 2
def baseEnd_3807779 : Nat := 217246761455173642316761

theorem tailTrace_3807779 : CollatzResearch.WordTrace tailWord_3807779 prefixEnd_3807779 217246761455173642316761 := by
  unfold tailWord_3807779
  simp only [CollatzResearch.WordTrace]
  refine ⟨138881109672074474723938391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92587406448049649815958927 138881109672074474723938391)
  ·
    refine ⟨208321664508111712085907587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138881109672074474723938391 208321664508111712085907587)
    ·
      refine ⟨312482496762167568128861381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208321664508111712085907587 312482496762167568128861381)
      ·
        refine ⟨58590468142906419024161509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312482496762167568128861381 58590468142906419024161509)
        ·
          refine ⟨10985712776794953567030283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58590468142906419024161509 10985712776794953567030283)
          ·
            refine ⟨16478569165192430350545425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985712776794953567030283 16478569165192430350545425)
            ·
              refine ⟨12358926873894322762909069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16478569165192430350545425 12358926873894322762909069)
              ·
                refine ⟨4634597577710371036090901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12358926873894322762909069 4634597577710371036090901)
                ·
                  refine ⟨217246761455173642316761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4634597577710371036090901 217246761455173642316761)
                  ·
                    rfl

theorem cell23_3807779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 6].length) (baseStart_3807779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807779 prefixEnd_3807779 := by exact prefixLift 3807779
  have htrace : WordTrace (prefixWord ++ tailWord_3807779) baseStart_3807779 baseEnd_3807779 := by
    simpa [prefixWord, tailWord_3807779, baseEnd_3807779] using wordTrace_append hprefix tailTrace_3807779
  have hstable : (prefixWord ++ tailWord_3807779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807779).length < 2 ^ (prefixWord ++ tailWord_3807779).sum := by decide
  have hdescent : baseEnd_3807779 < baseStart_3807779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807790 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_3807790 : Nat := 118140960795 + 3807790 * 2 ^ 59
def prefixEnd_3807790 : Nat := 4983230072969 + 3 ^ 40 * 3807790 * 2
def baseEnd_3807790 : Nat := 1955226501383762237813299

theorem tailTrace_3807790 : CollatzResearch.WordTrace tailWord_3807790 prefixEnd_3807790 1955226501383762237813299 := by
  unfold tailWord_3807790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17360188859379327950323603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92587673916689749068392549 17360188859379327950323603)
  ·
    refine ⟨26040283289068991925485405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17360188859379327950323603 26040283289068991925485405)
    ·
      refine ⟨9765106233400871972057027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26040283289068991925485405 9765106233400871972057027)
      ·
        refine ⟨14647659350101307958085541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9765106233400871972057027 14647659350101307958085541)
        ·
          refine ⟨2746436128143995242141039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14647659350101307958085541 2746436128143995242141039)
          ·
            refine ⟨4119654192215992863211559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746436128143995242141039 4119654192215992863211559)
            ·
              refine ⟨6179481288323989294817339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119654192215992863211559 6179481288323989294817339)
              ·
                refine ⟨9269221932485983942226009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179481288323989294817339 9269221932485983942226009)
                ·
                  refine ⟨6951916449364487956669507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269221932485983942226009 6951916449364487956669507)
                  ·
                    refine ⟨10427874674046731935004261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6951916449364487956669507 10427874674046731935004261)
                    ·
                      refine ⟨1955226501383762237813299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10427874674046731935004261 1955226501383762237813299)
                      ·
                        rfl

theorem cell23_3807790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_3807790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807790 prefixEnd_3807790 := by exact prefixLift 3807790
  have htrace : WordTrace (prefixWord ++ tailWord_3807790) baseStart_3807790 baseEnd_3807790 := by
    simpa [prefixWord, tailWord_3807790, baseEnd_3807790] using wordTrace_append hprefix tailTrace_3807790
  have hstable : (prefixWord ++ tailWord_3807790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807790).length < 2 ^ (prefixWord ++ tailWord_3807790).sum := by decide
  have hdescent : baseEnd_3807790 < baseStart_3807790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807816 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_3807816 : Nat := 118140960795 + 3807816 * 2 ^ 59
def prefixEnd_3807816 : Nat := 4983230072969 + 3 ^ 40 * 3807816 * 2
def baseEnd_3807816 : Nat := 1955239851880779136088179

theorem tailTrace_3807816 : CollatzResearch.WordTrace tailWord_3807816 prefixEnd_3807816 1955239851880779136088179 := by
  unfold tailWord_3807816
  simp only [CollatzResearch.WordTrace]
  refine ⟨69441229586470215021517651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92588306115293620028690201 69441229586470215021517651)
  ·
    refine ⟨104161844379705322532276477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69441229586470215021517651 104161844379705322532276477)
    ·
      refine ⟨39060691642389495949603679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104161844379705322532276477 39060691642389495949603679)
      ·
        refine ⟨58591037463584243924405519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39060691642389495949603679 58591037463584243924405519)
        ·
          refine ⟨87886556195376365886608279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58591037463584243924405519 87886556195376365886608279)
          ·
            refine ⟨131829834293064548829912419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87886556195376365886608279 131829834293064548829912419)
            ·
              refine ⟨197744751439596823244868629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131829834293064548829912419 197744751439596823244868629)
              ·
                refine ⟨9269285223731101089603217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197744751439596823244868629 9269285223731101089603217)
                ·
                  refine ⟨6951963917798325817202413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269285223731101089603217 6951963917798325817202413)
                  ·
                    refine ⟨2606986469174372181450905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6951963917798325817202413 2606986469174372181450905)
                    ·
                      refine ⟨1955239851880779136088179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2606986469174372181450905 1955239851880779136088179)
                      ·
                        rfl

theorem cell23_3807816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_3807816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807816 prefixEnd_3807816 := by exact prefixLift 3807816
  have htrace : WordTrace (prefixWord ++ tailWord_3807816) baseStart_3807816 baseEnd_3807816 := by
    simpa [prefixWord, tailWord_3807816, baseEnd_3807816] using wordTrace_append hprefix tailTrace_3807816
  have hstable : (prefixWord ++ tailWord_3807816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807816).length < 2 ^ (prefixWord ++ tailWord_3807816).sum := by decide
  have hdescent : baseEnd_3807816 < baseStart_3807816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807823 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 1, 1, 3]
def baseStart_3807823 : Nat := 118140960795 + 3807823 * 2 ^ 59
def prefixEnd_3807823 : Nat := 4983230072969 + 3 ^ 40 * 3807823 * 2
def baseEnd_3807823 : Nat := 1955243446245360608700647

theorem tailTrace_3807823 : CollatzResearch.WordTrace tailWord_3807823 prefixEnd_3807823 1955243446245360608700647 := by
  unfold tailWord_3807823
  simp only [CollatzResearch.WordTrace]
  refine ⟨138882714483915070238540123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92588476322610046825693415 138882714483915070238540123)
  ·
    refine ⟨208324071725872605357810185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138882714483915070238540123 208324071725872605357810185)
    ·
      refine ⟨156243053794404454018357639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208324071725872605357810185 156243053794404454018357639)
      ·
        refine ⟨234364580691606681027536459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156243053794404454018357639 234364580691606681027536459)
        ·
          refine ⟨351546871037410021541304689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234364580691606681027536459 351546871037410021541304689)
          ·
            refine ⟨263660153278057516155978517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351546871037410021541304689 263660153278057516155978517)
            ·
              refine ⟨12359069684908946069811493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263660153278057516155978517 12359069684908946069811493)
              ·
                refine ⟨2317325565920427388089655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12359069684908946069811493 2317325565920427388089655)
                ·
                  refine ⟨3475988348880641082134483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317325565920427388089655 3475988348880641082134483)
                  ·
                    refine ⟨5213982523320961623201725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3475988348880641082134483 5213982523320961623201725)
                    ·
                      refine ⟨1955243446245360608700647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5213982523320961623201725 1955243446245360608700647)
                      ·
                        rfl

theorem cell23_3807823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 1, 3].length) (baseStart_3807823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807823 prefixEnd_3807823 := by exact prefixLift 3807823
  have htrace : WordTrace (prefixWord ++ tailWord_3807823) baseStart_3807823 baseEnd_3807823 := by
    simpa [prefixWord, tailWord_3807823, baseEnd_3807823] using wordTrace_append hprefix tailTrace_3807823
  have hstable : (prefixWord ++ tailWord_3807823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807823).length < 2 ^ (prefixWord ++ tailWord_3807823).sum := by decide
  have hdescent : baseEnd_3807823 < baseStart_3807823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807829 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3807829 : Nat := 118140960795 + 3807829 * 2 ^ 59
def prefixEnd_3807829 : Nat := 4983230072969 + 3 ^ 40 * 3807829 * 2
def baseEnd_3807829 : Nat := 1955246527129287585225619

theorem tailTrace_3807829 : CollatzResearch.WordTrace tailWord_3807829 prefixEnd_3807829 1955246527129287585225619 := by
  unfold tailWord_3807829
  simp only [CollatzResearch.WordTrace]
  refine ⟨138882933321893333263258541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92588622214595555508839027 138882933321893333263258541)
  ·
    refine ⟨52081099995709999973721953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138882933321893333263258541 52081099995709999973721953)
    ·
      refine ⟨39060824996782499980291465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52081099995709999973721953 39060824996782499980291465)
      ·
        refine ⟨29295618747586874985218599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39060824996782499980291465 29295618747586874985218599)
        ·
          refine ⟨43943428121380312477827899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29295618747586874985218599 43943428121380312477827899)
          ·
            refine ⟨65915142182070468716741849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43943428121380312477827899 65915142182070468716741849)
            ·
              refine ⟨49436356636552851537556387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65915142182070468716741849 49436356636552851537556387)
              ·
                refine ⟨74154534954829277306334581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49436356636552851537556387 74154534954829277306334581)
                ·
                  refine ⟨6951987652015244747468867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74154534954829277306334581 6951987652015244747468867)
                  ·
                    refine ⟨10427981478022867121203301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6951987652015244747468867 10427981478022867121203301)
                    ·
                      refine ⟨1955246527129287585225619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10427981478022867121203301 1955246527129287585225619)
                      ·
                        rfl

theorem cell23_3807829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3807829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807829 prefixEnd_3807829 := by exact prefixLift 3807829
  have htrace : WordTrace (prefixWord ++ tailWord_3807829) baseStart_3807829 baseEnd_3807829 := by
    simpa [prefixWord, tailWord_3807829, baseEnd_3807829] using wordTrace_append hprefix tailTrace_3807829
  have hstable : (prefixWord ++ tailWord_3807829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807829).length < 2 ^ (prefixWord ++ tailWord_3807829).sum := by decide
  have hdescent : baseEnd_3807829 < baseStart_3807829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807890 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3807890 : Nat := 118140960795 + 3807890 * 2 ^ 59
def prefixEnd_3807890 : Nat := 4983230072969 + 3 ^ 40 * 3807890 * 2
def baseEnd_3807890 : Nat := 651759283149737282187613

theorem tailTrace_3807890 : CollatzResearch.WordTrace tailWord_3807890 prefixEnd_3807890 651759283149737282187613 := by
  unfold tailWord_3807890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34721289543668085170307281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92590105449781560454152749 34721289543668085170307281)
  ·
    refine ⟨26040967157751063877730461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34721289543668085170307281 26040967157751063877730461)
    ·
      refine ⟨9765362684156648954148923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26040967157751063877730461 9765362684156648954148923)
      ·
        refine ⟨14648044026234973431223385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9765362684156648954148923 14648044026234973431223385)
        ·
          refine ⟨10986033019676230073417539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14648044026234973431223385 10986033019676230073417539)
          ·
            refine ⟨16479049529514345110126309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10986033019676230073417539 16479049529514345110126309)
            ·
              refine ⟨3089821786783939708148683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16479049529514345110126309 3089821786783939708148683)
              ·
                refine ⟨4634732680175909562223025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089821786783939708148683 4634732680175909562223025)
                ·
                  refine ⟨3476049510131932171667269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4634732680175909562223025 3476049510131932171667269)
                  ·
                    refine ⟨651759283149737282187613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476049510131932171667269 651759283149737282187613)
                    ·
                      rfl

theorem cell23_3807890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3807890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807890 prefixEnd_3807890 := by exact prefixLift 3807890
  have htrace : WordTrace (prefixWord ++ tailWord_3807890) baseStart_3807890 baseEnd_3807890 := by
    simpa [prefixWord, tailWord_3807890, baseEnd_3807890] using wordTrace_append hprefix tailTrace_3807890
  have hstable : (prefixWord ++ tailWord_3807890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807890).length < 2 ^ (prefixWord ++ tailWord_3807890).sum := by decide
  have hdescent : baseEnd_3807890 < baseStart_3807890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807896 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3807896 : Nat := 118140960795 + 3807896 * 2 ^ 59
def prefixEnd_3807896 : Nat := 4983230072969 + 3 ^ 40 * 3807896 * 2
def baseEnd_3807896 : Nat := 1955280930333138823087811

theorem tailTrace_3807896 : CollatzResearch.WordTrace tailWord_3807896 prefixEnd_3807896 1955280930333138823087811 := by
  unfold tailWord_3807896
  simp only [CollatzResearch.WordTrace]
  refine ⟨69442688506325301852973771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92590251341767069137298361 69442688506325301852973771)
  ·
    refine ⟨104164032759487952779460657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69442688506325301852973771 104164032759487952779460657)
    ·
      refine ⟨78123024569615964584595493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104164032759487952779460657 78123024569615964584595493)
      ·
        refine ⟨14648067106802993359611655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78123024569615964584595493 14648067106802993359611655)
        ·
          refine ⟨21972100660204490039417483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14648067106802993359611655 21972100660204490039417483)
          ·
            refine ⟨32958150990306735059126225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21972100660204490039417483 32958150990306735059126225)
            ·
              refine ⟨24718613242730051294344669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32958150990306735059126225 24718613242730051294344669)
              ·
                refine ⟨9269479966023769235379251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24718613242730051294344669 9269479966023769235379251)
                ·
                  refine ⟨13904219949035653853068877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9269479966023769235379251 13904219949035653853068877)
                  ·
                    refine ⟨5214082480888370194900829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13904219949035653853068877 5214082480888370194900829)
                    ·
                      refine ⟨1955280930333138823087811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214082480888370194900829 1955280930333138823087811)
                      ·
                        rfl

theorem cell23_3807896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3807896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807896 prefixEnd_3807896 := by exact prefixLift 3807896
  have htrace : WordTrace (prefixWord ++ tailWord_3807896) baseStart_3807896 baseEnd_3807896 := by
    simpa [prefixWord, tailWord_3807896, baseEnd_3807896] using wordTrace_append hprefix tailTrace_3807896
  have hstable : (prefixWord ++ tailWord_3807896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807896).length < 2 ^ (prefixWord ++ tailWord_3807896).sum := by decide
  have hdescent : baseEnd_3807896 < baseStart_3807896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807900 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3807900 : Nat := 118140960795 + 3807900 * 2 ^ 59
def prefixEnd_3807900 : Nat := 4983230072969 + 3 ^ 40 * 3807900 * 2
def baseEnd_3807900 : Nat := 1955282984255756807437793

theorem tailTrace_3807900 : CollatzResearch.WordTrace tailWord_3807900 prefixEnd_3807900 1955282984255756807437793 := by
  unfold tailWord_3807900
  simp only [CollatzResearch.WordTrace]
  refine ⟨69442761452318056194546577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92590348603090741592728769 69442761452318056194546577)
  ·
    refine ⟨52082071089238542145909933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69442761452318056194546577 52082071089238542145909933)
    ·
      refine ⟨19530776658464453304716225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52082071089238542145909933 19530776658464453304716225)
      ·
        refine ⟨14648082493848339978537169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19530776658464453304716225 14648082493848339978537169)
        ·
          refine ⟨10986061870386254983902877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14648082493848339978537169 10986061870386254983902877)
          ·
            refine ⟨4119773201394845618963579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10986061870386254983902877 4119773201394845618963579)
            ·
              refine ⟨6179659802092268428445369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119773201394845618963579 6179659802092268428445369)
              ·
                refine ⟨4634744851569201321334027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6179659802092268428445369 4634744851569201321334027)
                ·
                  refine ⟨6952117277353801982001041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634744851569201321334027 6952117277353801982001041)
                  ·
                    refine ⟨5214087958015351486500781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6952117277353801982001041 5214087958015351486500781)
                    ·
                      refine ⟨1955282984255756807437793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214087958015351486500781 1955282984255756807437793)
                      ·
                        rfl

theorem cell23_3807900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3807900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807900 prefixEnd_3807900 := by exact prefixLift 3807900
  have htrace : WordTrace (prefixWord ++ tailWord_3807900) baseStart_3807900 baseEnd_3807900 := by
    simpa [prefixWord, tailWord_3807900, baseEnd_3807900] using wordTrace_append hprefix tailTrace_3807900
  have hstable : (prefixWord ++ tailWord_3807900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807900).length < 2 ^ (prefixWord ++ tailWord_3807900).sum := by decide
  have hdescent : baseEnd_3807900 < baseStart_3807900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807929 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_3807929 : Nat := 118140960795 + 3807929 * 2 ^ 59
def prefixEnd_3807929 : Nat := 4983230072969 + 3 ^ 40 * 3807929 * 2
def baseEnd_3807929 : Nat := 651765958398245731325053

theorem tailTrace_3807929 : CollatzResearch.WordTrace tailWord_3807929 prefixEnd_3807929 651765958398245731325053 := by
  unfold tailWord_3807929
  simp only [CollatzResearch.WordTrace]
  refine ⟨138886580621531050341898841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92591053747687366894599227 138886580621531050341898841)
  ·
    refine ⟨104164935466148287756424131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138886580621531050341898841 104164935466148287756424131)
    ·
      refine ⟨156247403199222431634636197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104164935466148287756424131 156247403199222431634636197)
      ·
        refine ⟨29296388099854205931494287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156247403199222431634636197 29296388099854205931494287)
        ·
          refine ⟨43944582149781308897241431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29296388099854205931494287 43944582149781308897241431)
          ·
            refine ⟨65916873224671963345862147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43944582149781308897241431 65916873224671963345862147)
            ·
              refine ⟨98875309837007945018793221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65916873224671963345862147 98875309837007945018793221)
              ·
                refine ⟨18539120594438989691023729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98875309837007945018793221 18539120594438989691023729)
                ·
                  refine ⟨13904340445829242268267797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18539120594438989691023729 13904340445829242268267797)
                  ·
                    refine ⟨651765958398245731325053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13904340445829242268267797 651765958398245731325053)
                    ·
                      rfl

theorem cell23_3807929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_3807929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807929 prefixEnd_3807929 := by exact prefixLift 3807929
  have htrace : WordTrace (prefixWord ++ tailWord_3807929) baseStart_3807929 baseEnd_3807929 := by
    simpa [prefixWord, tailWord_3807929, baseEnd_3807929] using wordTrace_append hprefix tailTrace_3807929
  have hstable : (prefixWord ++ tailWord_3807929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807929).length < 2 ^ (prefixWord ++ tailWord_3807929).sum := by decide
  have hdescent : baseEnd_3807929 < baseStart_3807929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807946 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_3807946 : Nat := 118140960795 + 3807946 * 2 ^ 59
def prefixEnd_3807946 : Nat := 4983230072969 + 3 ^ 40 * 3807946 * 2
def baseEnd_3807946 : Nat := 651768868121954542487527

theorem tailTrace_3807946 : CollatzResearch.WordTrace tailWord_3807946 prefixEnd_3807946 651768868121954542487527 := by
  unfold tailWord_3807946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34721800165617365561316923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92591467108312974830178461 34721800165617365561316923)
  ·
    refine ⟨52082700248426048341975385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34721800165617365561316923 52082700248426048341975385)
    ·
      refine ⟨39062025186319536256481539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52082700248426048341975385 39062025186319536256481539)
      ·
        refine ⟨58593037779479304384722309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39062025186319536256481539 58593037779479304384722309)
        ·
          refine ⟨10986194583652369572135433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58593037779479304384722309 10986194583652369572135433)
          ·
            refine ⟨8239645937739277179101575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10986194583652369572135433 8239645937739277179101575)
            ·
              refine ⟨12359468906608915768652363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239645937739277179101575 12359468906608915768652363)
              ·
                refine ⟨18539203359913373652978545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359468906608915768652363 18539203359913373652978545)
                ·
                  refine ⟨13904402519935030239733909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18539203359913373652978545 13904402519935030239733909)
                  ·
                    refine ⟨651768868121954542487527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13904402519935030239733909 651768868121954542487527)
                    ·
                      rfl

theorem cell23_3807946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_3807946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807946 prefixEnd_3807946 := by exact prefixLift 3807946
  have htrace : WordTrace (prefixWord ++ tailWord_3807946) baseStart_3807946 baseEnd_3807946 := by
    simpa [prefixWord, tailWord_3807946, baseEnd_3807946] using wordTrace_append hprefix tailTrace_3807946
  have hstable : (prefixWord ++ tailWord_3807946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807946).length < 2 ^ (prefixWord ++ tailWord_3807946).sum := by decide
  have hdescent : baseEnd_3807946 < baseStart_3807946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807953 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 1, 4, 2]
def baseStart_3807953 : Nat := 118140960795 + 3807953 * 2 ^ 59
def prefixEnd_3807953 : Nat := 4983230072969 + 3 ^ 40 * 3807953 * 2
def baseEnd_3807953 : Nat := 1955310198730445100075049

theorem tailTrace_3807953 : CollatzResearch.WordTrace tailWord_3807953 prefixEnd_3807953 1955310198730445100075049 := by
  unfold tailWord_3807953
  simp only [CollatzResearch.WordTrace]
  refine ⟨138887455973444102440772513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92591637315629401627181675 138887455973444102440772513)
  ·
    refine ⟨104165591980083076830579385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138887455973444102440772513 104165591980083076830579385)
    ·
      refine ⟨78124193985062307622934539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104165591980083076830579385 78124193985062307622934539)
      ·
        refine ⟨117186290977593461434401809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78124193985062307622934539 117186290977593461434401809)
        ·
          refine ⟨87889718233195096075801357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117186290977593461434401809 87889718233195096075801357)
          ·
            refine ⟨32958644337448161028425509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87889718233195096075801357 32958644337448161028425509)
            ·
              refine ⟨6179745813271530192829783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32958644337448161028425509 6179745813271530192829783)
              ·
                refine ⟨9269618719907295289244675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179745813271530192829783 9269618719907295289244675)
                ·
                  refine ⟨13904428079860942933867013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9269618719907295289244675 13904428079860942933867013)
                  ·
                    refine ⟨2607080264973926800100065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13904428079860942933867013 2607080264973926800100065)
                    ·
                      refine ⟨1955310198730445100075049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607080264973926800100065 1955310198730445100075049)
                      ·
                        rfl

theorem cell23_3807953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_3807953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807953 prefixEnd_3807953 := by exact prefixLift 3807953
  have htrace : WordTrace (prefixWord ++ tailWord_3807953) baseStart_3807953 baseEnd_3807953 := by
    simpa [prefixWord, tailWord_3807953, baseEnd_3807953] using wordTrace_append hprefix tailTrace_3807953
  have hstable : (prefixWord ++ tailWord_3807953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807953).length < 2 ^ (prefixWord ++ tailWord_3807953).sum := by decide
  have hdescent : baseEnd_3807953 < baseStart_3807953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807959 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 9]
def baseStart_3807959 : Nat := 118140960795 + 3807959 * 2 ^ 59
def prefixEnd_3807959 : Nat := 4983230072969 + 3 ^ 40 * 3807959 * 2
def baseEnd_3807959 : Nat := 217257031068263564066669

theorem tailTrace_3807959 : CollatzResearch.WordTrace tailWord_3807959 prefixEnd_3807959 217257031068263564066669 := by
  unfold tailWord_3807959
  simp only [CollatzResearch.WordTrace]
  refine ⟨138887674811422365465490931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92591783207614910310327287 138887674811422365465490931)
  ·
    refine ⟨208331512217133548198236397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138887674811422365465490931 208331512217133548198236397)
    ·
      refine ⟨78124317081425080574338649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208331512217133548198236397 78124317081425080574338649)
      ·
        refine ⟨58593237811068810430753987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78124317081425080574338649 58593237811068810430753987)
        ·
          refine ⟨87889856716603215646130981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58593237811068810430753987 87889856716603215646130981)
          ·
            refine ⟨16479348134363102933649559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87889856716603215646130981 16479348134363102933649559)
            ·
              refine ⟨24719022201544654400474339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16479348134363102933649559 24719022201544654400474339)
              ·
                refine ⟨37078533302316981600711509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24719022201544654400474339 37078533302316981600711509)
                ·
                  refine ⟨217257031068263564066669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37078533302316981600711509 217257031068263564066669)
                  ·
                    rfl

theorem cell23_3807959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 9].length) (baseStart_3807959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807959 prefixEnd_3807959 := by exact prefixLift 3807959
  have htrace : WordTrace (prefixWord ++ tailWord_3807959) baseStart_3807959 baseEnd_3807959 := by
    simpa [prefixWord, tailWord_3807959, baseEnd_3807959] using wordTrace_append hprefix tailTrace_3807959
  have hstable : (prefixWord ++ tailWord_3807959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807959).length < 2 ^ (prefixWord ++ tailWord_3807959).sum := by decide
  have hdescent : baseEnd_3807959 < baseStart_3807959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807999 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_3807999 : Nat := 118140960795 + 3807999 * 2 ^ 59
def prefixEnd_3807999 : Nat := 4983230072969 + 3 ^ 40 * 3807999 * 2
def baseEnd_3807999 : Nat := 1955333818840551920099837

theorem tailTrace_3807999 : CollatzResearch.WordTrace tailWord_3807999 prefixEnd_3807999 1955333818840551920099837 := by
  unfold tailWord_3807999
  simp only [CollatzResearch.WordTrace]
  refine ⟨138889133731277452296947051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92592755820851634864631367 138889133731277452296947051)
  ·
    refine ⟨208333700596916178445420577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138889133731277452296947051 208333700596916178445420577)
    ·
      refine ⟨156250275447687133834065433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208333700596916178445420577 156250275447687133834065433)
      ·
        refine ⟨117187706585765350375549075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156250275447687133834065433 117187706585765350375549075)
        ·
          refine ⟨175781559878648025563323613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117187706585765350375549075 175781559878648025563323613)
          ·
            refine ⟨65918084954493009586246355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175781559878648025563323613 65918084954493009586246355)
            ·
              refine ⟨98877127431739514379369533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65918084954493009586246355 98877127431739514379369533)
              ·
                refine ⟨37078922786902317892263575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98877127431739514379369533 37078922786902317892263575)
                ·
                  refine ⟨55618384180353476838395363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37078922786902317892263575 55618384180353476838395363)
                  ·
                    refine ⟨83427576270530215257593045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55618384180353476838395363 83427576270530215257593045)
                    ·
                      refine ⟨1955333818840551920099837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83427576270530215257593045 1955333818840551920099837)
                      ·
                        rfl

theorem cell23_3807999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_3807999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3807999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3807999 prefixEnd_3807999 := by exact prefixLift 3807999
  have htrace : WordTrace (prefixWord ++ tailWord_3807999) baseStart_3807999 baseEnd_3807999 := by
    simpa [prefixWord, tailWord_3807999, baseEnd_3807999] using wordTrace_append hprefix tailTrace_3807999
  have hstable : (prefixWord ++ tailWord_3807999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807999).length < 2 ^ (prefixWord ++ tailWord_3807999).sum := by decide
  have hdescent : baseEnd_3807999 < baseStart_3807999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808019 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 8]
def baseStart_3808019 : Nat := 118140960795 + 3808019 * 2 ^ 59
def prefixEnd_3808019 : Nat := 4983230072969 + 3 ^ 40 * 3808019 * 2
def baseEnd_3808019 : Nat := 651781362817880613949915

theorem tailTrace_3808019 : CollatzResearch.WordTrace tailWord_3808019 prefixEnd_3808019 651781362817880613949915 := by
  unfold tailWord_3808019
  simp only [CollatzResearch.WordTrace]
  refine ⟨138889863191204995712675111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92593242127469997141783407 138889863191204995712675111)
  ·
    refine ⟨208334794786807493569012667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138889863191204995712675111 208334794786807493569012667)
    ·
      refine ⟨312502192180211240353519001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208334794786807493569012667 312502192180211240353519001)
      ·
        refine ⟨234376644135158430265139251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312502192180211240353519001 234376644135158430265139251)
        ·
          refine ⟨351564966202737645397708877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234376644135158430265139251 351564966202737645397708877)
          ·
            refine ⟨131836862326026617024140829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351564966202737645397708877 131836862326026617024140829)
            ·
              refine ⟨49438823372259981384052811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131836862326026617024140829 49438823372259981384052811)
              ·
                refine ⟨74158235058389972076079217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49438823372259981384052811 74158235058389972076079217)
                ·
                  refine ⟨55618676293792479057059413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74158235058389972076079217 55618676293792479057059413)
                  ·
                    refine ⟨651781362817880613949915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55618676293792479057059413 651781362817880613949915)
                    ·
                      rfl

theorem cell23_3808019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_3808019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808019 prefixEnd_3808019 := by exact prefixLift 3808019
  have htrace : WordTrace (prefixWord ++ tailWord_3808019) baseStart_3808019 baseEnd_3808019 := by
    simpa [prefixWord, tailWord_3808019, baseEnd_3808019] using wordTrace_append hprefix tailTrace_3808019
  have hstable : (prefixWord ++ tailWord_3808019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808019).length < 2 ^ (prefixWord ++ tailWord_3808019).sum := by decide
  have hdescent : baseEnd_3808019 < baseStart_3808019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
