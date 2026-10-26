import V185TrunkScan22Chunk333

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2980103 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 1, 3]
def baseStart_2980103 : Nat := 118140960795 + 2980103 * 2 ^ 59
def prefixEnd_2980103 : Nat := 4983230072969 + 3 ^ 40 * 2980103 * 2
def baseEnd_2980103 : Nat := 1020150159270572711338175

theorem tailTrace_2980103 : CollatzResearch.WordTrace tailWord_2980103 prefixEnd_2980103 1020150159270572711338175 := by
  unfold tailWord_2980103
  simp only [CollatzResearch.WordTrace]
  refine ⟨108693285922603266917048963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72462190615068844611365975 108693285922603266917048963)
  ·
    refine ⟨163039928883904900375573445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108693285922603266917048963 163039928883904900375573445)
    ·
      refine ⟨30569986665732168820420021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163039928883904900375573445 30569986665732168820420021)
      ·
        refine ⟨2865936249912390826914377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30569986665732168820420021 2865936249912390826914377)
        ·
          refine ⟨2149452187434293120185783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2865936249912390826914377 2149452187434293120185783)
          ·
            refine ⟨3224178281151439680278675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149452187434293120185783 3224178281151439680278675)
            ·
              refine ⟨4836267421727159520418013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224178281151439680278675 4836267421727159520418013)
              ·
                refine ⟨1813600283147684820156755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4836267421727159520418013 1813600283147684820156755)
                ·
                  refine ⟨2720400424721527230235133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813600283147684820156755 2720400424721527230235133)
                  ·
                    refine ⟨1020150159270572711338175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720400424721527230235133 1020150159270572711338175)
                    ·
                      rfl

theorem cell22_2980103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_2980103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980103 prefixEnd_2980103 := by exact prefixLift 2980103
  have htrace : WordTrace (prefixWord ++ tailWord_2980103) baseStart_2980103 baseEnd_2980103 := by
    simpa [prefixWord, tailWord_2980103, baseEnd_2980103] using wordTrace_append hprefix tailTrace_2980103
  have hstable : (prefixWord ++ tailWord_2980103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980103).length < 2 ^ (prefixWord ++ tailWord_2980103).sum := by decide
  have hdescent : baseEnd_2980103 < baseStart_2980103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980108 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_2980108 : Nat := 118140960795 + 2980108 * 2 ^ 59
def prefixEnd_2980108 : Nat := 4983230072969 + 3 ^ 40 * 2980108 * 2
def baseEnd_2980108 : Nat := 1020151870872754364963159

theorem tailTrace_2980108 : CollatzResearch.WordTrace tailWord_2980108 prefixEnd_2980108 1020151870872754364963159 := by
  unfold tailWord_2980108
  simp only [CollatzResearch.WordTrace]
  refine ⟨54346734143792576385490489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72462312191723435180653985 54346734143792576385490489)
  ·
    refine ⟨40760050607844432289117867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54346734143792576385490489 40760050607844432289117867)
    ·
      refine ⟨61140075911766648433676801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40760050607844432289117867 61140075911766648433676801)
      ·
        refine ⟨45855056933824986325257601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61140075911766648433676801 45855056933824986325257601)
        ·
          refine ⟨34391292700368739743943201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45855056933824986325257601 34391292700368739743943201)
          ·
            refine ⟨25793469525276554807957401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34391292700368739743943201 25793469525276554807957401)
            ·
              refine ⟨19345102143957416105968051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25793469525276554807957401 19345102143957416105968051)
              ·
                refine ⟨29017653215936124158952077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19345102143957416105968051 29017653215936124158952077)
                ·
                  refine ⟨10881619955976046559607029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29017653215936124158952077 10881619955976046559607029)
                  ·
                    refine ⟨1020151870872754364963159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10881619955976046559607029 1020151870872754364963159)
                    ·
                      rfl

theorem cell22_2980108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_2980108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980108 prefixEnd_2980108 := by exact prefixLift 2980108
  have htrace : WordTrace (prefixWord ++ tailWord_2980108) baseStart_2980108 baseEnd_2980108 := by
    simpa [prefixWord, tailWord_2980108, baseEnd_2980108] using wordTrace_append hprefix tailTrace_2980108
  have hstable : (prefixWord ++ tailWord_2980108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980108).length < 2 ^ (prefixWord ++ tailWord_2980108).sum := by decide
  have hdescent : baseEnd_2980108 < baseStart_2980108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980123 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 4, 4]
def baseStart_2980123 : Nat := 118140960795 + 2980123 * 2 ^ 59
def prefixEnd_2980123 : Nat := 4983230072969 + 3 ^ 40 * 2980123 * 2
def baseEnd_2980123 : Nat := 1020157005679299325838113

theorem tailTrace_2980123 : CollatzResearch.WordTrace tailWord_2980123 prefixEnd_2980123 1020157005679299325838113 := by
  unfold tailWord_2980123
  simp only [CollatzResearch.WordTrace]
  refine ⟨108694015382530810332777023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72462676921687206888518015 108694015382530810332777023)
  ·
    refine ⟨163041023073796215499165535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108694015382530810332777023 163041023073796215499165535)
    ·
      refine ⟨244561534610694323248748303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163041023073796215499165535 244561534610694323248748303)
      ·
        refine ⟨366842301916041484873122455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244561534610694323248748303 366842301916041484873122455)
        ·
          refine ⟨550263452874062227309683683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366842301916041484873122455 550263452874062227309683683)
          ·
            refine ⟨825395179311093340964525525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550263452874062227309683683 825395179311093340964525525)
            ·
              refine ⟨19345199515103750178856067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 825395179311093340964525525 19345199515103750178856067)
              ·
                refine ⟨29017799272655625268284101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19345199515103750178856067 29017799272655625268284101)
                ·
                  refine ⟨5440837363622929737803269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29017799272655625268284101 5440837363622929737803269)
                  ·
                    refine ⟨1020157005679299325838113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440837363622929737803269 1020157005679299325838113)
                    ·
                      rfl

theorem cell22_2980123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_2980123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980123 prefixEnd_2980123 := by exact prefixLift 2980123
  have htrace : WordTrace (prefixWord ++ tailWord_2980123) baseStart_2980123 baseEnd_2980123 := by
    simpa [prefixWord, tailWord_2980123, baseEnd_2980123] using wordTrace_append hprefix tailTrace_2980123
  have hstable : (prefixWord ++ tailWord_2980123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980123).length < 2 ^ (prefixWord ++ tailWord_2980123).sum := by decide
  have hdescent : baseEnd_2980123 < baseStart_2980123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980243 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_2980243 : Nat := 118140960795 + 2980243 * 2 ^ 59
def prefixEnd_2980243 : Nat := 4983230072969 + 3 ^ 40 * 2980243 * 2
def baseEnd_2980243 : Nat := 1020198084131659012837745

theorem tailTrace_2980243 : CollatzResearch.WordTrace tailWord_2980243 prefixEnd_2980243 1020198084131659012837745 := by
  unfold tailWord_2980243
  simp only [CollatzResearch.WordTrace]
  refine ⟨108698392142096070827145383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72465594761397380551430255 108698392142096070827145383)
  ·
    refine ⟨163047588213144106240718075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108698392142096070827145383 163047588213144106240718075)
    ·
      refine ⟨244571382319716159361077113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163047588213144106240718075 244571382319716159361077113)
      ·
        refine ⟨183428536739787119520807835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244571382319716159361077113 183428536739787119520807835)
        ·
          refine ⟨275142805109680679281211753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183428536739787119520807835 275142805109680679281211753)
          ·
            refine ⟨206357103832260509460908815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275142805109680679281211753 206357103832260509460908815)
            ·
              refine ⟨309535655748390764191363223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206357103832260509460908815 309535655748390764191363223)
              ·
                refine ⟨464303483622586146287044835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309535655748390764191363223 464303483622586146287044835)
                ·
                  refine ⟨696455225433879219430567253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464303483622586146287044835 696455225433879219430567253)
                  ·
                    refine ⟨1020198084131659012837745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 696455225433879219430567253 1020198084131659012837745)
                    ·
                      rfl

theorem cell22_2980243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_2980243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980243 prefixEnd_2980243 := by exact prefixLift 2980243
  have htrace : WordTrace (prefixWord ++ tailWord_2980243) baseStart_2980243 baseEnd_2980243 := by
    simpa [prefixWord, tailWord_2980243, baseEnd_2980243] using wordTrace_append hprefix tailTrace_2980243
  have hstable : (prefixWord ++ tailWord_2980243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980243).length < 2 ^ (prefixWord ++ tailWord_2980243).sum := by decide
  have hdescent : baseEnd_2980243 < baseStart_2980243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980264 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2980264 : Nat := 118140960795 + 2980264 * 2 ^ 59
def prefixEnd_2980264 : Nat := 4983230072969 + 3 ^ 40 * 2980264 * 2
def baseEnd_2980264 : Nat := 1020205272860821958062681

theorem tailTrace_2980264 : CollatzResearch.WordTrace tailWord_2980264 prefixEnd_2980264 1020205272860821958062681 := by
  unfold tailWord_2980264
  simp only [CollatzResearch.WordTrace]
  refine ⟨54349579037509995706829923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72466105383346660942439897 54349579037509995706829923)
  ·
    refine ⟨81524368556264993560244885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54349579037509995706829923 81524368556264993560244885)
    ·
      refine ⟨3821454776074921573136479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81524368556264993560244885 3821454776074921573136479)
      ·
        refine ⟨5732182164112382359704719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3821454776074921573136479 5732182164112382359704719)
        ·
          refine ⟨8598273246168573539557079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732182164112382359704719 8598273246168573539557079)
          ·
            refine ⟨12897409869252860309335619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598273246168573539557079 12897409869252860309335619)
            ·
              refine ⟨19346114803879290464003429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12897409869252860309335619 19346114803879290464003429)
              ·
                refine ⟨3627396525727366962000643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19346114803879290464003429 3627396525727366962000643)
                ·
                  refine ⟨5441094788591050443000965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627396525727366962000643 5441094788591050443000965)
                  ·
                    refine ⟨1020205272860821958062681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5441094788591050443000965 1020205272860821958062681)
                    ·
                      rfl

theorem cell22_2980264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2980264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980264 prefixEnd_2980264 := by exact prefixLift 2980264
  have htrace : WordTrace (prefixWord ++ tailWord_2980264) baseStart_2980264 baseEnd_2980264 := by
    simpa [prefixWord, tailWord_2980264, baseEnd_2980264] using wordTrace_append hprefix tailTrace_2980264
  have hstable : (prefixWord ++ tailWord_2980264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980264).length < 2 ^ (prefixWord ++ tailWord_2980264).sum := by decide
  have hdescent : baseEnd_2980264 < baseStart_2980264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980279 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 4]
def baseStart_2980279 : Nat := 118140960795 + 2980279 * 2 ^ 59
def prefixEnd_2980279 : Nat := 4983230072969 + 3 ^ 40 * 2980279 * 2
def baseEnd_2980279 : Nat := 340070135889122306312545

theorem tailTrace_2980279 : CollatzResearch.WordTrace tailWord_2980279 prefixEnd_2980279 340070135889122306312545 := by
  unfold tailWord_2980279
  simp only [CollatzResearch.WordTrace]
  refine ⟨108699705169965648975455891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72466470113310432650303927 108699705169965648975455891)
  ·
    refine ⟨163049557754948473463183837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108699705169965648975455891 163049557754948473463183837)
    ·
      refine ⟨61143584158105677548693939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163049557754948473463183837 61143584158105677548693939)
      ·
        refine ⟨91715376237158516323040909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61143584158105677548693939 91715376237158516323040909)
        ·
          refine ⟨34393266088934443621140341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91715376237158516323040909 34393266088934443621140341)
          ·
            refine ⟨3224368695837604089481907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34393266088934443621140341 3224368695837604089481907)
            ·
              refine ⟨4836553043756406134222861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224368695837604089481907 4836553043756406134222861)
              ·
                refine ⟨1813707391408652300333573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4836553043756406134222861 1813707391408652300333573)
                ·
                  refine ⟨340070135889122306312545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1813707391408652300333573 340070135889122306312545)
                  ·
                    rfl

theorem cell22_2980279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 4].length) (baseStart_2980279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980279 prefixEnd_2980279 := by exact prefixLift 2980279
  have htrace : WordTrace (prefixWord ++ tailWord_2980279) baseStart_2980279 baseEnd_2980279 := by
    simpa [prefixWord, tailWord_2980279, baseEnd_2980279] using wordTrace_append hprefix tailTrace_2980279
  have hstable : (prefixWord ++ tailWord_2980279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980279).length < 2 ^ (prefixWord ++ tailWord_2980279).sum := by decide
  have hdescent : baseEnd_2980279 < baseStart_2980279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980339 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 1, 3]
def baseStart_2980339 : Nat := 118140960795 + 2980339 * 2 ^ 59
def prefixEnd_2980339 : Nat := 4983230072969 + 3 ^ 40 * 2980339 * 2
def baseEnd_2980339 : Nat := 1020230946893546762437451

theorem tailTrace_2980339 : CollatzResearch.WordTrace tailWord_2980339 prefixEnd_2980339 1020230946893546762437451 := by
  unfold tailWord_2980339
  simp only [CollatzResearch.WordTrace]
  refine ⟨108701893549748279222640071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72467929033165519481760047 108701893549748279222640071)
  ·
    refine ⟨163052840324622418833960107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108701893549748279222640071 163052840324622418833960107)
    ·
      refine ⟨244579260486933628250940161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163052840324622418833960107 244579260486933628250940161)
      ·
        refine ⟨183434445365200221188205121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244579260486933628250940161 183434445365200221188205121)
        ·
          refine ⟨137575834023900165891153841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183434445365200221188205121 137575834023900165891153841)
          ·
            refine ⟨103181875517925124418365381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137575834023900165891153841 103181875517925124418365381)
            ·
              refine ⟨19346601659610960828443509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103181875517925124418365381 19346601659610960828443509)
              ·
                refine ⟨1813743905588527577666579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19346601659610960828443509 1813743905588527577666579)
                ·
                  refine ⟨2720615858382791366499869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813743905588527577666579 2720615858382791366499869)
                  ·
                    refine ⟨1020230946893546762437451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720615858382791366499869 1020230946893546762437451)
                    ·
                      rfl

theorem cell22_2980339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 3].length) (baseStart_2980339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980339 prefixEnd_2980339 := by exact prefixLift 2980339
  have htrace : WordTrace (prefixWord ++ tailWord_2980339) baseStart_2980339 baseEnd_2980339 := by
    simpa [prefixWord, tailWord_2980339, baseEnd_2980339] using wordTrace_append hprefix tailTrace_2980339
  have hstable : (prefixWord ++ tailWord_2980339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980339).length < 2 ^ (prefixWord ++ tailWord_2980339).sum := by decide
  have hdescent : baseEnd_2980339 < baseStart_2980339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980358 : List Nat := [6, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2980358 : Nat := 118140960795 + 2980358 * 2 ^ 59
def prefixEnd_2980358 : Nat := 4983230072969 + 3 ^ 40 * 2980358 * 2
def baseEnd_2980358 : Nat := 113359716775759671801377

theorem tailTrace_2980358 : CollatzResearch.WordTrace tailWord_2980358 prefixEnd_2980358 113359716775759671801377 := by
  unfold tailWord_2980358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396955829271232670861929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72468391024452963645054485 3396955829271232670861929)
  ·
    refine ⟨2547716871953424503146447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3396955829271232670861929 2547716871953424503146447)
    ·
      refine ⟨3821575307930136754719671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547716871953424503146447 3821575307930136754719671)
      ·
        refine ⟨5732362961895205132079507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3821575307930136754719671 5732362961895205132079507)
        ·
          refine ⟨8598544442842807698119261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732362961895205132079507 8598544442842807698119261)
          ·
            refine ⟨3224454166066052886794723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8598544442842807698119261 3224454166066052886794723)
            ·
              refine ⟨4836681249099079330192085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224454166066052886794723 4836681249099079330192085)
              ·
                refine ⟨113359716775759671801377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4836681249099079330192085 113359716775759671801377)
                ·
                  rfl

theorem cell22_2980358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2980358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980358 prefixEnd_2980358 := by exact prefixLift 2980358
  have htrace : WordTrace (prefixWord ++ tailWord_2980358) baseStart_2980358 baseEnd_2980358 := by
    simpa [prefixWord, tailWord_2980358, baseEnd_2980358] using wordTrace_append hprefix tailTrace_2980358
  have hstable : (prefixWord ++ tailWord_2980358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980358).length < 2 ^ (prefixWord ++ tailWord_2980358).sum := by decide
  have hdescent : baseEnd_2980358 < baseStart_2980358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980420 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 5]
def baseStart_2980420 : Nat := 118140960795 + 2980420 * 2 ^ 59
def prefixEnd_2980420 : Nat := 4983230072969 + 3 ^ 40 * 2980420 * 2
def baseEnd_2980420 : Nat := 340086224949629850387401

theorem tailTrace_2980420 : CollatzResearch.WordTrace tailWord_2980420 prefixEnd_2980420 340086224949629850387401 := by
  unfold tailWord_2980420
  simp only [CollatzResearch.WordTrace]
  refine ⟨54352423931227415028169357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72469898574969886704225809 54352423931227415028169357)
  ·
    refine ⟨20382158974210280635563509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54352423931227415028169357 20382158974210280635563509)
    ·
      refine ⟨1910827403832213809584079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20382158974210280635563509 1910827403832213809584079)
      ·
        refine ⟨2866241105748320714376119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910827403832213809584079 2866241105748320714376119)
        ·
          refine ⟨4299361658622481071564179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866241105748320714376119 4299361658622481071564179)
          ·
            refine ⟨6449042487933721607346269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299361658622481071564179 6449042487933721607346269)
            ·
              refine ⟨2418390932975145602754851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6449042487933721607346269 2418390932975145602754851)
              ·
                refine ⟨3627586399462718404132277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418390932975145602754851 3627586399462718404132277)
                ·
                  refine ⟨340086224949629850387401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3627586399462718404132277 340086224949629850387401)
                  ·
                    rfl

theorem cell22_2980420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_2980420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980420 prefixEnd_2980420 := by exact prefixLift 2980420
  have htrace : WordTrace (prefixWord ++ tailWord_2980420) baseStart_2980420 baseEnd_2980420 := by
    simpa [prefixWord, tailWord_2980420, baseEnd_2980420] using wordTrace_append hprefix tailTrace_2980420
  have hstable : (prefixWord ++ tailWord_2980420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980420).length < 2 ^ (prefixWord ++ tailWord_2980420).sum := by decide
  have hdescent : baseEnd_2980420 < baseStart_2980420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980525 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2980525 : Nat := 118140960795 + 2980525 * 2 ^ 59
def prefixEnd_2980525 : Nat := 4983230072969 + 3 ^ 40 * 2980525 * 2
def baseEnd_2980525 : Nat := 1020294618494704277286881

theorem tailTrace_2980525 : CollatzResearch.WordTrace tailWord_2980525 prefixEnd_2980525 1020294618494704277286881 := by
  unfold tailWord_2980525
  simp only [CollatzResearch.WordTrace]
  refine ⟨108708677527074432988911029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72472451684716288659274019 108708677527074432988911029)
  ·
    refine ⟨10191438518163228092710409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108708677527074432988911029 10191438518163228092710409)
    ·
      refine ⟨7643578888622421069532807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10191438518163228092710409 7643578888622421069532807)
      ·
        refine ⟨11465368332933631604299211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7643578888622421069532807 11465368332933631604299211)
        ·
          refine ⟨17198052499400447406448817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11465368332933631604299211 17198052499400447406448817)
          ·
            refine ⟨12898539374550335554836613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17198052499400447406448817 12898539374550335554836613)
            ·
              refine ⟨2418476132728187916531865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12898539374550335554836613 2418476132728187916531865)
              ·
                refine ⟨1813857099546140937398899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2418476132728187916531865 1813857099546140937398899)
                ·
                  refine ⟨2720785649319211406098349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813857099546140937398899 2720785649319211406098349)
                  ·
                    refine ⟨1020294618494704277286881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720785649319211406098349 1020294618494704277286881)
                    ·
                      rfl

theorem cell22_2980525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2980525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980525 prefixEnd_2980525 := by exact prefixLift 2980525
  have htrace : WordTrace (prefixWord ++ tailWord_2980525) baseStart_2980525 baseEnd_2980525 := by
    simpa [prefixWord, tailWord_2980525, baseEnd_2980525] using wordTrace_append hprefix tailTrace_2980525
  have hstable : (prefixWord ++ tailWord_2980525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980525).length < 2 ^ (prefixWord ++ tailWord_2980525).sum := by decide
  have hdescent : baseEnd_2980525 < baseStart_2980525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980568 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 1, 4]
def baseStart_2980568 : Nat := 118140960795 + 2980568 * 2 ^ 59
def prefixEnd_2980568 : Nat := 4983230072969 + 3 ^ 40 * 2980568 * 2
def baseEnd_2980568 : Nat := 1020309338273466498461749

theorem tailTrace_2980568 : CollatzResearch.WordTrace tailWord_2980568 prefixEnd_2980568 1020309338273466498461749 := by
  unfold tailWord_2980568
  simp only [CollatzResearch.WordTrace]
  refine ⟨54355122932959325666363179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72473497243945767555150905 54355122932959325666363179)
  ·
    refine ⟨81532684399438988499544769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54355122932959325666363179 81532684399438988499544769)
    ·
      refine ⟨61149513299579241374658577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81532684399438988499544769 61149513299579241374658577)
      ·
        refine ⟨45862134974684431030993933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61149513299579241374658577 45862134974684431030993933)
        ·
          refine ⟨17198300615506661636622725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45862134974684431030993933 17198300615506661636622725)
          ·
            refine ⟨3224681365407499056866761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17198300615506661636622725 3224681365407499056866761)
            ·
              refine ⟨2418511024055624292650071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3224681365407499056866761 2418511024055624292650071)
              ·
                refine ⟨3627766536083436438975107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418511024055624292650071 3627766536083436438975107)
                ·
                  refine ⟨5441649804125154658462661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627766536083436438975107 5441649804125154658462661)
                  ·
                    refine ⟨1020309338273466498461749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5441649804125154658462661 1020309338273466498461749)
                    ·
                      rfl

theorem cell22_2980568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_2980568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980568 prefixEnd_2980568 := by exact prefixLift 2980568
  have htrace : WordTrace (prefixWord ++ tailWord_2980568) baseStart_2980568 baseEnd_2980568 := by
    simpa [prefixWord, tailWord_2980568, baseEnd_2980568] using wordTrace_append hprefix tailTrace_2980568
  have hstable : (prefixWord ++ tailWord_2980568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980568).length < 2 ^ (prefixWord ++ tailWord_2980568).sum := by decide
  have hdescent : baseEnd_2980568 < baseStart_2980568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980581 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_2980581 : Nat := 118140960795 + 2980581 * 2 ^ 59
def prefixEnd_2980581 : Nat := 4983230072969 + 3 ^ 40 * 2980581 * 2
def baseEnd_2980581 : Nat := 1020313788439138797886709

theorem tailTrace_2980581 : CollatzResearch.WordTrace tailWord_2980581 prefixEnd_2980581 1020313788439138797886709 := by
  unfold tailWord_2980581
  simp only [CollatzResearch.WordTrace]
  refine ⟨108710720014871554552949597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72473813343247703035299731 108710720014871554552949597)
  ·
    refine ⟨40766520005576832957356099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108710720014871554552949597 40766520005576832957356099)
    ·
      refine ⟨61149780008365249436034149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40766520005576832957356099 61149780008365249436034149)
      ·
        refine ⟨11465583751568484269256403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61149780008365249436034149 11465583751568484269256403)
        ·
          refine ⟨17198375627352726403884605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11465583751568484269256403 17198375627352726403884605)
          ·
            refine ⟨6449390860257272401456727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17198375627352726403884605 6449390860257272401456727)
            ·
              refine ⟨9674086290385908602185091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449390860257272401456727 9674086290385908602185091)
              ·
                refine ⟨14511129435578862903277637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9674086290385908602185091 14511129435578862903277637)
                ·
                  refine ⟨2720836769171036794364557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14511129435578862903277637 2720836769171036794364557)
                  ·
                    refine ⟨1020313788439138797886709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720836769171036794364557 1020313788439138797886709)
                    ·
                      rfl

theorem cell22_2980581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_2980581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980581 prefixEnd_2980581 := by exact prefixLift 2980581
  have htrace : WordTrace (prefixWord ++ tailWord_2980581) baseStart_2980581 baseEnd_2980581 := by
    simpa [prefixWord, tailWord_2980581, baseEnd_2980581] using wordTrace_append hprefix tailTrace_2980581
  have hstable : (prefixWord ++ tailWord_2980581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980581).length < 2 ^ (prefixWord ++ tailWord_2980581).sum := by decide
  have hdescent : baseEnd_2980581 < baseStart_2980581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980639 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 7]
def baseStart_2980639 : Nat := 118140960795 + 2980639 * 2 ^ 59
def prefixEnd_2980639 : Nat := 4983230072969 + 3 ^ 40 * 2980639 * 2
def baseEnd_2980639 : Nat := 340111214341481993312177

theorem tailTrace_2980639 : CollatzResearch.WordTrace tailWord_2980639 prefixEnd_2980639 340111214341481993312177 := by
  unfold tailWord_2980639
  simp only [CollatzResearch.WordTrace]
  refine ⟨108712835448661430458560971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72475223632440953639040647 108712835448661430458560971)
  ·
    refine ⟨163069253172992145687841457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108712835448661430458560971 163069253172992145687841457)
    ·
      refine ⟨122301939879744109265881093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163069253172992145687841457 122301939879744109265881093)
      ·
        refine ⟨22931613727452020487352705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122301939879744109265881093 22931613727452020487352705)
        ·
          refine ⟨17198710295589015365514529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22931613727452020487352705 17198710295589015365514529)
          ·
            refine ⟨12899032721691761524135897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17198710295589015365514529 12899032721691761524135897)
            ·
              refine ⟨9674274541268821143101923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12899032721691761524135897 9674274541268821143101923)
              ·
                refine ⟨14511411811903231714652885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9674274541268821143101923 14511411811903231714652885)
                ·
                  refine ⟨340111214341481993312177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14511411811903231714652885 340111214341481993312177)
                  ·
                    rfl

theorem cell22_2980639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 7].length) (baseStart_2980639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980639 prefixEnd_2980639 := by exact prefixLift 2980639
  have htrace : WordTrace (prefixWord ++ tailWord_2980639) baseStart_2980639 baseEnd_2980639 := by
    simpa [prefixWord, tailWord_2980639, baseEnd_2980639] using wordTrace_append hprefix tailTrace_2980639
  have hstable : (prefixWord ++ tailWord_2980639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980639).length < 2 ^ (prefixWord ++ tailWord_2980639).sum := by decide
  have hdescent : baseEnd_2980639 < baseStart_2980639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980686 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_2980686 : Nat := 118140960795 + 2980686 * 2 ^ 59
def prefixEnd_2980686 : Nat := 4983230072969 + 3 ^ 40 * 2980686 * 2
def baseEnd_2980686 : Nat := 1020349732084953524011387

theorem tailTrace_2980686 : CollatzResearch.WordTrace tailWord_2980686 prefixEnd_2980686 1020349732084953524011387 := by
  unfold tailWord_2980686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589318709936394685690239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72476366452994104990347941 13589318709936394685690239)
  ·
    refine ⟨20383978064904592028535359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13589318709936394685690239 20383978064904592028535359)
    ·
      refine ⟨30575967097356888042803039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20383978064904592028535359 30575967097356888042803039)
      ·
        refine ⟨45863950646035332064204559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30575967097356888042803039 45863950646035332064204559)
        ·
          refine ⟨68795925969052998096306839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45863950646035332064204559 68795925969052998096306839)
          ·
            refine ⟨103193888953579497144460259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68795925969052998096306839 103193888953579497144460259)
            ·
              refine ⟨154790833430369245716690389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103193888953579497144460259 154790833430369245716690389)
              ·
                refine ⟨3627910158524279196484931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154790833430369245716690389 3627910158524279196484931)
                ·
                  refine ⟨5441865237786418794727397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627910158524279196484931 5441865237786418794727397)
                  ·
                    refine ⟨1020349732084953524011387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5441865237786418794727397 1020349732084953524011387)
                    ·
                      rfl

theorem cell22_2980686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_2980686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980686 prefixEnd_2980686 := by exact prefixLift 2980686
  have htrace : WordTrace (prefixWord ++ tailWord_2980686) baseStart_2980686 baseEnd_2980686 := by
    simpa [prefixWord, tailWord_2980686, baseEnd_2980686] using wordTrace_append hprefix tailTrace_2980686
  have hstable : (prefixWord ++ tailWord_2980686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980686).length < 2 ^ (prefixWord ++ tailWord_2980686).sum := by decide
  have hdescent : baseEnd_2980686 < baseStart_2980686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980716 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_2980716 : Nat := 118140960795 + 2980716 * 2 ^ 59
def prefixEnd_2980716 : Nat := 4983230072969 + 3 ^ 40 * 2980716 * 2
def baseEnd_2980716 : Nat := 1020360001698043445761295

theorem tailTrace_2980716 : CollatzResearch.WordTrace tailWord_2980716 prefixEnd_2980716 1020360001698043445761295 := by
  unfold tailWord_2980716
  simp only [CollatzResearch.WordTrace]
  refine ⟨54357821934691236304557001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72477095912921648406076001 54357821934691236304557001)
  ·
    refine ⟨40768366451018427228417751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54357821934691236304557001 40768366451018427228417751)
    ·
      refine ⟨61152549676527640842626627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40768366451018427228417751 61152549676527640842626627)
      ·
        refine ⟨91728824514791461263939941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61152549676527640842626627 91728824514791461263939941)
        ·
          refine ⟨17199154596523398986988739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91728824514791461263939941 17199154596523398986988739)
          ·
            refine ⟨25798731894785098480483109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17199154596523398986988739 25798731894785098480483109)
            ·
              refine ⟨4837262230272205965090583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25798731894785098480483109 4837262230272205965090583)
              ·
                refine ⟨7255893345408308947635875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837262230272205965090583 7255893345408308947635875)
                ·
                  refine ⟨10883840018112463421453813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7255893345408308947635875 10883840018112463421453813)
                  ·
                    refine ⟨1020360001698043445761295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10883840018112463421453813 1020360001698043445761295)
                    ·
                      rfl

theorem cell22_2980716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_2980716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980716 prefixEnd_2980716 := by exact prefixLift 2980716
  have htrace : WordTrace (prefixWord ++ tailWord_2980716) baseStart_2980716 baseEnd_2980716 := by
    simpa [prefixWord, tailWord_2980716, baseEnd_2980716] using wordTrace_append hprefix tailTrace_2980716
  have hstable : (prefixWord ++ tailWord_2980716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980716).length < 2 ^ (prefixWord ++ tailWord_2980716).sum := by decide
  have hdescent : baseEnd_2980716 < baseStart_2980716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980718 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_2980718 : Nat := 118140960795 + 2980718 * 2 ^ 59
def prefixEnd_2980718 : Nat := 4983230072969 + 3 ^ 40 * 2980718 * 2
def baseEnd_2980718 : Nat := 340120228779638702403763

theorem tailTrace_2980718 : CollatzResearch.WordTrace tailWord_2980718 prefixEnd_2980718 340120228779638702403763 := by
  unfold tailWord_2980718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589464601921903368835851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72477144543583484633791205 13589464601921903368835851)
  ·
    refine ⟨20384196902882855053253777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13589464601921903368835851 20384196902882855053253777)
    ·
      refine ⟨15288147677162141289940333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20384196902882855053253777 15288147677162141289940333)
      ·
        refine ⟨5733055378935802983727625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15288147677162141289940333 5733055378935802983727625)
        ·
          refine ⟨4299791534201852237795719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733055378935802983727625 4299791534201852237795719)
          ·
            refine ⟨6449687301302778356693579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299791534201852237795719 6449687301302778356693579)
            ·
              refine ⟨9674530951954167535040369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449687301302778356693579 9674530951954167535040369)
              ·
                refine ⟨7255898213965625651280277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9674530951954167535040369 7255898213965625651280277)
                ·
                  refine ⟨340120228779638702403763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7255898213965625651280277 340120228779638702403763)
                  ·
                    rfl

theorem cell22_2980718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_2980718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980718 prefixEnd_2980718 := by exact prefixLift 2980718
  have htrace : WordTrace (prefixWord ++ tailWord_2980718) baseStart_2980718 baseEnd_2980718 := by
    simpa [prefixWord, tailWord_2980718, baseEnd_2980718] using wordTrace_append hprefix tailTrace_2980718
  have hstable : (prefixWord ++ tailWord_2980718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980718).length < 2 ^ (prefixWord ++ tailWord_2980718).sum := by decide
  have hdescent : baseEnd_2980718 < baseStart_2980718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980731 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 2, 4]
def baseStart_2980731 : Nat := 118140960795 + 2980731 * 2 ^ 59
def prefixEnd_2980731 : Nat := 4983230072969 + 3 ^ 40 * 2980731 * 2
def baseEnd_2980731 : Nat := 1020365136504588406636249

theorem tailTrace_2980731 : CollatzResearch.WordTrace tailWord_2980731 prefixEnd_2980731 1020365136504588406636249 := by
  unfold tailWord_2980731
  simp only [CollatzResearch.WordTrace]
  refine ⟨108716190964328130170910047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72477460642885420113940031 108716190964328130170910047)
  ·
    refine ⟨163074286446492195256365071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108716190964328130170910047 163074286446492195256365071)
    ·
      refine ⟨244611429669738292884547607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163074286446492195256365071 244611429669738292884547607)
      ·
        refine ⟨366917144504607439326821411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244611429669738292884547607 366917144504607439326821411)
        ·
          refine ⟨550375716756911158990232117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366917144504607439326821411 550375716756911158990232117)
          ·
            refine ⟨51597723445960421155334261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 550375716756911158990232117 51597723445960421155334261)
            ·
              refine ⟨4837286573058789483312587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51597723445960421155334261 4837286573058789483312587)
              ·
                refine ⟨7255929859588184224968881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837286573058789483312587 7255929859588184224968881)
                ·
                  refine ⟨5441947394691138168726661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255929859588184224968881 5441947394691138168726661)
                  ·
                    refine ⟨1020365136504588406636249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5441947394691138168726661 1020365136504588406636249)
                    ·
                      rfl

theorem cell22_2980731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].length) (baseStart_2980731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980731 prefixEnd_2980731 := by exact prefixLift 2980731
  have htrace : WordTrace (prefixWord ++ tailWord_2980731) baseStart_2980731 baseEnd_2980731 := by
    simpa [prefixWord, tailWord_2980731, baseEnd_2980731] using wordTrace_append hprefix tailTrace_2980731
  have hstable : (prefixWord ++ tailWord_2980731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980731).length < 2 ^ (prefixWord ++ tailWord_2980731).sum := by decide
  have hdescent : baseEnd_2980731 < baseStart_2980731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980746 : List Nat := [3, 1, 2, 4, 1, 2, 9]
def baseStart_2980746 : Nat := 118140960795 + 2980746 * 2 ^ 59
def prefixEnd_2980746 : Nat := 4983230072969 + 3 ^ 40 * 2980746 * 2
def baseEnd_2980746 : Nat := 37791491530041976574489

theorem tailTrace_2980746 : CollatzResearch.WordTrace tailWord_2980746 prefixEnd_2980746 37791491530041976574489 := by
  unfold tailWord_2980746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27179184514818446933176523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72477825372849191821804061 27179184514818446933176523)
  ·
    refine ⟨40768776772227670399764785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27179184514818446933176523 40768776772227670399764785)
    ·
      refine ⟨30576582579170752799823589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40768776772227670399764785 30576582579170752799823589)
      ·
        refine ⟨5733109233594516149966923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30576582579170752799823589 5733109233594516149966923)
        ·
          refine ⟨8599663850391774224950385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733109233594516149966923 8599663850391774224950385)
          ·
            refine ⟨6449747887793830668712789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599663850391774224950385 6449747887793830668712789)
            ·
              refine ⟨37791491530041976574489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6449747887793830668712789 37791491530041976574489)
              ·
                rfl

theorem cell22_2980746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 9].length) (baseStart_2980746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980746 prefixEnd_2980746 := by exact prefixLift 2980746
  have htrace : WordTrace (prefixWord ++ tailWord_2980746) baseStart_2980746 baseEnd_2980746 := by
    simpa [prefixWord, tailWord_2980746, baseEnd_2980746] using wordTrace_append hprefix tailTrace_2980746
  have hstable : (prefixWord ++ tailWord_2980746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980746).length < 2 ^ (prefixWord ++ tailWord_2980746).sum := by decide
  have hdescent : baseEnd_2980746 < baseStart_2980746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980812 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_2980812 : Nat := 118140960795 + 2980812 * 2 ^ 59
def prefixEnd_2980812 : Nat := 4983230072969 + 3 ^ 40 * 2980812 * 2
def baseEnd_2980812 : Nat := 1020392864459931195361001

theorem tailTrace_2980812 : CollatzResearch.WordTrace tailWord_2980812 prefixEnd_2980812 1020392864459931195361001 := by
  unfold tailWord_2980812
  simp only [CollatzResearch.WordTrace]
  refine ⟨54359572638517340502304345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72479430184689787336405793 54359572638517340502304345)
  ·
    refine ⟨40769679478888005376728259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54359572638517340502304345 40769679478888005376728259)
    ·
      refine ⟨61154519218332008065092389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40769679478888005376728259 61154519218332008065092389)
      ·
        refine ⟨11466472353437251512204823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61154519218332008065092389 11466472353437251512204823)
        ·
          refine ⟨17199708530155877268307235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11466472353437251512204823 17199708530155877268307235)
          ·
            refine ⟨25799562795233815902460853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17199708530155877268307235 25799562795233815902460853)
            ·
              refine ⟨2418709012053170240855705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25799562795233815902460853 2418709012053170240855705)
              ·
                refine ⟨1814031759039877680641779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2418709012053170240855705 1814031759039877680641779)
                ·
                  refine ⟨2721047638559816520962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814031759039877680641779 2721047638559816520962669)
                  ·
                    refine ⟨1020392864459931195361001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721047638559816520962669 1020392864459931195361001)
                    ·
                      rfl

theorem cell22_2980812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_2980812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980812 prefixEnd_2980812 := by exact prefixLift 2980812
  have htrace : WordTrace (prefixWord ++ tailWord_2980812) baseStart_2980812 baseEnd_2980812 := by
    simpa [prefixWord, tailWord_2980812, baseEnd_2980812] using wordTrace_append hprefix tailTrace_2980812
  have hstable : (prefixWord ++ tailWord_2980812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980812).length < 2 ^ (prefixWord ++ tailWord_2980812).sum := by decide
  have hdescent : baseEnd_2980812 < baseStart_2980812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980825 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 5]
def baseStart_2980825 : Nat := 118140960795 + 2980825 * 2 ^ 59
def prefixEnd_2980825 : Nat := 4983230072969 + 3 ^ 40 * 2980825 * 2
def baseEnd_2980825 : Nat := 340132438208534498261987

theorem tailTrace_2980825 : CollatzResearch.WordTrace tailWord_2980825 prefixEnd_2980825 340132438208534498261987 := by
  unfold tailWord_2980825
  simp only [CollatzResearch.WordTrace]
  refine ⟨108719619425987584224831929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72479746283991722816554619 108719619425987584224831929)
  ·
    refine ⟨81539714569490688168623947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108719619425987584224831929 81539714569490688168623947)
    ·
      refine ⟨122309571854236032252935921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81539714569490688168623947 122309571854236032252935921)
      ·
        refine ⟨91732178890677024189701941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122309571854236032252935921 91732178890677024189701941)
        ·
          refine ⟨8599891771000971017784557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91732178890677024189701941 8599891771000971017784557)
          ·
            refine ⟨3224959414125364131669209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8599891771000971017784557 3224959414125364131669209)
            ·
              refine ⟨2418719560594023098751907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3224959414125364131669209 2418719560594023098751907)
              ·
                refine ⟨3628079340891034648127861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418719560594023098751907 3628079340891034648127861)
                ·
                  refine ⟨340132438208534498261987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3628079340891034648127861 340132438208534498261987)
                  ·
                    rfl

theorem cell22_2980825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_2980825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980825 prefixEnd_2980825 := by exact prefixLift 2980825
  have htrace : WordTrace (prefixWord ++ tailWord_2980825) baseStart_2980825 baseEnd_2980825 := by
    simpa [prefixWord, tailWord_2980825, baseEnd_2980825] using wordTrace_append hprefix tailTrace_2980825
  have hstable : (prefixWord ++ tailWord_2980825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980825).length < 2 ^ (prefixWord ++ tailWord_2980825).sum := by decide
  have hdescent : baseEnd_2980825 < baseStart_2980825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980885 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2980885 : Nat := 118140960795 + 2980885 * 2 ^ 59
def prefixEnd_2980885 : Nat := 4983230072969 + 3 ^ 40 * 2980885 * 2
def baseEnd_2980885 : Nat := 1020417853851783338285777

theorem tailTrace_2980885 : CollatzResearch.WordTrace tailWord_2980885 prefixEnd_2980885 1020417853851783338285777 := by
  unfold tailWord_2980885
  simp only [CollatzResearch.WordTrace]
  refine ⟨108721807805770214472016109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72481205203846809648010739 108721807805770214472016109)
  ·
    refine ⟨40770677927163830427006041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108721807805770214472016109 40770677927163830427006041)
    ·
      refine ⟨30578008445372872820254531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40770677927163830427006041 30578008445372872820254531)
      ·
        refine ⟨45867012668059309230381797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30578008445372872820254531 45867012668059309230381797)
        ·
          refine ⟨8600064875261120480696587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45867012668059309230381797 8600064875261120480696587)
          ·
            refine ⟨12900097312891680721044881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600064875261120480696587 12900097312891680721044881)
            ·
              refine ⟨9675072984668760540783661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12900097312891680721044881 9675072984668760540783661)
              ·
                refine ⟨3628152369250785202793873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9675072984668760540783661 3628152369250785202793873)
                ·
                  refine ⟨2721114276938088902095405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628152369250785202793873 2721114276938088902095405)
                  ·
                    refine ⟨1020417853851783338285777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721114276938088902095405 1020417853851783338285777)
                    ·
                      rfl

theorem cell22_2980885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2980885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980885 prefixEnd_2980885 := by exact prefixLift 2980885
  have htrace : WordTrace (prefixWord ++ tailWord_2980885) baseStart_2980885 baseEnd_2980885 := by
    simpa [prefixWord, tailWord_2980885, baseEnd_2980885] using wordTrace_append hprefix tailTrace_2980885
  have hstable : (prefixWord ++ tailWord_2980885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980885).length < 2 ^ (prefixWord ++ tailWord_2980885).sum := by decide
  have hdescent : baseEnd_2980885 < baseStart_2980885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980900 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_2980900 : Nat := 118140960795 + 2980900 * 2 ^ 59
def prefixEnd_2980900 : Nat := 4983230072969 + 3 ^ 40 * 2980900 * 2
def baseEnd_2980900 : Nat := 1020422988658328299160731

theorem tailTrace_2980900 : CollatzResearch.WordTrace tailWord_2980900 prefixEnd_2980900 1020422988658328299160731 := by
  unfold tailWord_2980900
  simp only [CollatzResearch.WordTrace]
  refine ⟨54361177450357936016906077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72481569933810581355874769 54361177450357936016906077)
  ·
    refine ⟨20385441543884226006339779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54361177450357936016906077 20385441543884226006339779)
    ·
      refine ⟨30578162315826339009509669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20385441543884226006339779 30578162315826339009509669)
      ·
        refine ⟨5733405434217438564283063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30578162315826339009509669 5733405434217438564283063)
        ·
          refine ⟨8600108151326157846424595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733405434217438564283063 8600108151326157846424595)
          ·
            refine ⟨12900162226989236769636893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600108151326157846424595 12900162226989236769636893)
            ·
              refine ⟨4837560835120963788613835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12900162226989236769636893 4837560835120963788613835)
              ·
                refine ⟨7256341252681445682920753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837560835120963788613835 7256341252681445682920753)
                ·
                  refine ⟨5442255939511084262190565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7256341252681445682920753 5442255939511084262190565)
                  ·
                    refine ⟨1020422988658328299160731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5442255939511084262190565 1020422988658328299160731)
                    ·
                      rfl

theorem cell22_2980900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_2980900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980900 prefixEnd_2980900 := by exact prefixLift 2980900
  have htrace : WordTrace (prefixWord ++ tailWord_2980900) baseStart_2980900 baseEnd_2980900 := by
    simpa [prefixWord, tailWord_2980900, baseEnd_2980900] using wordTrace_append hprefix tailTrace_2980900
  have hstable : (prefixWord ++ tailWord_2980900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980900).length < 2 ^ (prefixWord ++ tailWord_2980900).sum := by decide
  have hdescent : baseEnd_2980900 < baseStart_2980900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980913 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_2980913 : Nat := 118140960795 + 2980913 * 2 ^ 59
def prefixEnd_2980913 : Nat := 4983230072969 + 3 ^ 40 * 2980913 * 2
def baseEnd_2980913 : Nat := 1020427438824000598585691

theorem tailTrace_2980913 : CollatzResearch.WordTrace tailWord_2980913 prefixEnd_2980913 1020427438824000598585691 := by
  unfold tailWord_2980913
  simp only [CollatzResearch.WordTrace]
  refine ⟨108722829049668775254035393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72481886033112516836023595 108722829049668775254035393)
  ·
    refine ⟨81542121787251581440526545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108722829049668775254035393 81542121787251581440526545)
    ·
      refine ⟨61156591340438686080394909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81542121787251581440526545 61156591340438686080394909)
      ·
        refine ⟨22933721752664507280148091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61156591340438686080394909 22933721752664507280148091)
        ·
          refine ⟨34400582628996760920222137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22933721752664507280148091 34400582628996760920222137)
          ·
            refine ⟨25800436971747570690166603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34400582628996760920222137 25800436971747570690166603)
            ·
              refine ⟨38700655457621356035249905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25800436971747570690166603 38700655457621356035249905)
              ·
                refine ⟨29025491593216017026437429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38700655457621356035249905 29025491593216017026437429)
                ·
                  refine ⟨2721139836864001596228509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29025491593216017026437429 2721139836864001596228509)
                  ·
                    refine ⟨1020427438824000598585691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721139836864001596228509 1020427438824000598585691)
                    ·
                      rfl

theorem cell22_2980913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_2980913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980913 prefixEnd_2980913 := by exact prefixLift 2980913
  have htrace : WordTrace (prefixWord ++ tailWord_2980913) baseStart_2980913 baseEnd_2980913 := by
    simpa [prefixWord, tailWord_2980913, baseEnd_2980913] using wordTrace_append hprefix tailTrace_2980913
  have hstable : (prefixWord ++ tailWord_2980913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980913).length < 2 ^ (prefixWord ++ tailWord_2980913).sum := by decide
  have hdescent : baseEnd_2980913 < baseStart_2980913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2980981 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2980981 : Nat := 118140960795 + 2980981 * 2 ^ 59
def prefixEnd_2980981 : Nat := 4983230072969 + 3 ^ 40 * 2980981 * 2
def baseEnd_2980981 : Nat := 1020450716613671087885483

theorem tailTrace_2980981 : CollatzResearch.WordTrace tailWord_2980981 prefixEnd_2980981 1020450716613671087885483 := by
  unfold tailWord_2980981
  simp only [CollatzResearch.WordTrace]
  refine ⟨108725309213422422867510797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72483539475614948578340531 108725309213422422867510797)
  ·
    refine ⟨40771990955033408575316549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108725309213422422867510797 40771990955033408575316549)
    ·
      refine ⟨7644748304068764107871853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40771990955033408575316549 7644748304068764107871853)
      ·
        refine ⟨2866780614025786540451945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7644748304068764107871853 2866780614025786540451945)
        ·
          refine ⟨2150085460519339905338959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2866780614025786540451945 2150085460519339905338959)
          ·
            refine ⟨3225128190779009858008439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150085460519339905338959 3225128190779009858008439)
            ·
              refine ⟨4837692286168514787012659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225128190779009858008439 4837692286168514787012659)
              ·
                refine ⟨7256538429252772180518989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837692286168514787012659 7256538429252772180518989)
                ·
                  refine ⟨2721201910969789567694621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7256538429252772180518989 2721201910969789567694621)
                  ·
                    refine ⟨1020450716613671087885483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721201910969789567694621 1020450716613671087885483)
                    ·
                      rfl

theorem cell22_2980981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2980981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2980981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2980981 prefixEnd_2980981 := by exact prefixLift 2980981
  have htrace : WordTrace (prefixWord ++ tailWord_2980981) baseStart_2980981 baseEnd_2980981 := by
    simpa [prefixWord, tailWord_2980981, baseEnd_2980981] using wordTrace_append hprefix tailTrace_2980981
  have hstable : (prefixWord ++ tailWord_2980981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2980981).length < 2 ^ (prefixWord ++ tailWord_2980981).sum := by decide
  have hdescent : baseEnd_2980981 < baseStart_2980981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2980981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981020 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2981020 : Nat := 118140960795 + 2981020 * 2 ^ 59
def prefixEnd_2981020 : Nat := 4983230072969 + 3 ^ 40 * 2981020 * 2
def baseEnd_2981020 : Nat := 1020464067110687986160363

theorem tailTrace_2981020 : CollatzResearch.WordTrace tailWord_2981020 prefixEnd_2981020 1020464067110687986160363 := by
  unfold tailWord_2981020
  simp only [CollatzResearch.WordTrace]
  refine ⟨54363365830140566264090257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72484487773520755018787009 54363365830140566264090257)
  ·
    refine ⟨40772524372605424698067693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54363365830140566264090257 40772524372605424698067693)
    ·
      refine ⟨15289696639727034261775385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40772524372605424698067693 15289696639727034261775385)
      ·
        refine ⟨11467272479795275696331539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15289696639727034261775385 11467272479795275696331539)
        ·
          refine ⟨17200908719692913544497309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11467272479795275696331539 17200908719692913544497309)
          ·
            refine ⟨6450340769884842579186491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17200908719692913544497309 6450340769884842579186491)
            ·
              refine ⟨9675511154827263868779737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450340769884842579186491 9675511154827263868779737)
              ·
                refine ⟨7256633366120447901584803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9675511154827263868779737 7256633366120447901584803)
                ·
                  refine ⟨10884950049180671852377205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256633366120447901584803 10884950049180671852377205)
                  ·
                    refine ⟨1020464067110687986160363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10884950049180671852377205 1020464067110687986160363)
                    ·
                      rfl

theorem cell22_2981020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2981020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981020 prefixEnd_2981020 := by exact prefixLift 2981020
  have htrace : WordTrace (prefixWord ++ tailWord_2981020) baseStart_2981020 baseEnd_2981020 := by
    simpa [prefixWord, tailWord_2981020, baseEnd_2981020] using wordTrace_append hprefix tailTrace_2981020
  have hstable : (prefixWord ++ tailWord_2981020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981020).length < 2 ^ (prefixWord ++ tailWord_2981020).sum := by decide
  have hdescent : baseEnd_2981020 < baseStart_2981020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981069 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2981069 : Nat := 118140960795 + 2981069 * 2 ^ 59
def prefixEnd_2981069 : Nat := 4983230072969 + 3 ^ 40 * 2981069 * 2
def baseEnd_2981069 : Nat := 1020480840812068191685213

theorem tailTrace_2981069 : CollatzResearch.WordTrace tailWord_2981069 prefixEnd_2981069 1020480840812068191685213 := by
  unfold tailWord_2981069
  simp only [CollatzResearch.WordTrace]
  refine ⟨108728518837103613896714261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72485679224735742597809507 108728518837103613896714261)
  ·
    refine ⟨5096649320489231901408481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108728518837103613896714261 5096649320489231901408481)
    ·
      refine ⟨3822486990366923926056361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5096649320489231901408481 3822486990366923926056361)
      ·
        refine ⟨2866865242775192944542271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3822486990366923926056361 2866865242775192944542271)
        ·
          refine ⟨4300297864162789416813407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866865242775192944542271 4300297864162789416813407)
          ·
            refine ⟨6450446796244184125220111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300297864162789416813407 6450446796244184125220111)
            ·
              refine ⟨9675670194366276187830167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450446796244184125220111 9675670194366276187830167)
              ·
                refine ⟨14513505291549414281745251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9675670194366276187830167 14513505291549414281745251)
                ·
                  refine ⟨21770257937324121422617877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14513505291549414281745251 21770257937324121422617877)
                  ·
                    refine ⟨1020480840812068191685213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21770257937324121422617877 1020480840812068191685213)
                    ·
                      rfl

theorem cell22_2981069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2981069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981069 prefixEnd_2981069 := by exact prefixLift 2981069
  have htrace : WordTrace (prefixWord ++ tailWord_2981069) baseStart_2981069 baseEnd_2981069 := by
    simpa [prefixWord, tailWord_2981069, baseEnd_2981069] using wordTrace_append hprefix tailTrace_2981069
  have hstable : (prefixWord ++ tailWord_2981069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981069).length < 2 ^ (prefixWord ++ tailWord_2981069).sum := by decide
  have hdescent : baseEnd_2981069 < baseStart_2981069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981150 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2981150 : Nat := 118140960795 + 2981150 * 2 ^ 59
def prefixEnd_2981150 : Nat := 4983230072969 + 3 ^ 40 * 2981150 * 2
def baseEnd_2981150 : Nat := 1020508568767410980409965

theorem tailTrace_2981150 : CollatzResearch.WordTrace tailWord_2981150 prefixEnd_2981150 1020508568767410980409965 := by
  unfold tailWord_2981150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13591434143726270591301613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72487648766540109820275269 13591434143726270591301613)
  ·
    refine ⟨5096787803897351471738105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13591434143726270591301613 5096787803897351471738105)
    ·
      refine ⟨3822590852923013603803579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5096787803897351471738105 3822590852923013603803579)
      ·
        refine ⟨5733886279384520405705369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822590852923013603803579 5733886279384520405705369)
        ·
          refine ⟨4300414709538390304279027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733886279384520405705369 4300414709538390304279027)
          ·
            refine ⟨6450622064307585456418541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300414709538390304279027 6450622064307585456418541)
            ·
              refine ⟨2418983274115344546156953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6450622064307585456418541 2418983274115344546156953)
              ·
                refine ⟨1814237455586508409617715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2418983274115344546156953 1814237455586508409617715)
                ·
                  refine ⟨2721356183379762614426573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814237455586508409617715 2721356183379762614426573)
                  ·
                    refine ⟨1020508568767410980409965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721356183379762614426573 1020508568767410980409965)
                    ·
                      rfl

theorem cell22_2981150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2981150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981150 prefixEnd_2981150 := by exact prefixLift 2981150
  have htrace : WordTrace (prefixWord ++ tailWord_2981150) baseStart_2981150 baseEnd_2981150 := by
    simpa [prefixWord, tailWord_2981150, baseEnd_2981150] using wordTrace_append hprefix tailTrace_2981150
  have hstable : (prefixWord ++ tailWord_2981150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981150).length < 2 ^ (prefixWord ++ tailWord_2981150).sum := by decide
  have hdescent : baseEnd_2981150 < baseStart_2981150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981157 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 6]
def baseStart_2981157 : Nat := 118140960795 + 2981157 * 2 ^ 59
def prefixEnd_2981157 : Nat := 4983230072969 + 3 ^ 40 * 2981157 * 2
def baseEnd_2981157 : Nat := 340170321670155098494981

theorem tailTrace_2981157 : CollatzResearch.WordTrace tailWord_2981157 prefixEnd_2981157 340170321670155098494981 := by
  unfold tailWord_2981157
  simp only [CollatzResearch.WordTrace]
  refine ⟨108731728460784804925917725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72487818973856536617278483 108731728460784804925917725)
  ·
    refine ⟨40774398172794301847219147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108731728460784804925917725 40774398172794301847219147)
    ·
      refine ⟨61161597259191452770828721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40774398172794301847219147 61161597259191452770828721)
      ·
        refine ⟨45871197944393589578121541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61161597259191452770828721 45871197944393589578121541)
        ·
          refine ⟨8600849614573798045897789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45871197944393589578121541 8600849614573798045897789)
          ·
            refine ⟨3225318605465174267211671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8600849614573798045897789 3225318605465174267211671)
            ·
              refine ⟨4837977908197761400817507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225318605465174267211671 4837977908197761400817507)
              ·
                refine ⟨7256966862296642101226261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837977908197761400817507 7256966862296642101226261)
                ·
                  refine ⟨340170321670155098494981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7256966862296642101226261 340170321670155098494981)
                  ·
                    rfl

theorem cell22_2981157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_2981157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981157 prefixEnd_2981157 := by exact prefixLift 2981157
  have htrace : WordTrace (prefixWord ++ tailWord_2981157) baseStart_2981157 baseEnd_2981157 := by
    simpa [prefixWord, tailWord_2981157, baseEnd_2981157] using wordTrace_append hprefix tailTrace_2981157
  have hstable : (prefixWord ++ tailWord_2981157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981157).length < 2 ^ (prefixWord ++ tailWord_2981157).sum := by decide
  have hdescent : baseEnd_2981157 < baseStart_2981157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981172 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2981172 : Nat := 118140960795 + 2981172 * 2 ^ 59
def prefixEnd_2981172 : Nat := 4983230072969 + 3 ^ 40 * 2981172 * 2
def baseEnd_2981172 : Nat := 1020516099817010256359897

theorem tailTrace_2981172 : CollatzResearch.WordTrace tailWord_2981172 prefixEnd_2981172 1020516099817010256359897 := by
  unfold tailWord_2981172
  simp only [CollatzResearch.WordTrace]
  refine ⟨54366137777865231243856885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72488183703820308325142513 54366137777865231243856885)
  ·
    refine ⟨5096825416674865429111583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54366137777865231243856885 5096825416674865429111583)
    ·
      refine ⟨7645238125012298143667375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5096825416674865429111583 7645238125012298143667375)
      ·
        refine ⟨11467857187518447215501063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645238125012298143667375 11467857187518447215501063)
        ·
          refine ⟨17201785781277670823251595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11467857187518447215501063 17201785781277670823251595)
          ·
            refine ⟨25802678671916506234877393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17201785781277670823251595 25802678671916506234877393)
            ·
              refine ⟨19352009003937379676158045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25802678671916506234877393 19352009003937379676158045)
              ·
                refine ⟨7257003376476517378559267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19352009003937379676158045 7257003376476517378559267)
                ·
                  refine ⟨10885505064714776067838901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7257003376476517378559267 10885505064714776067838901)
                  ·
                    refine ⟨1020516099817010256359897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10885505064714776067838901 1020516099817010256359897)
                    ·
                      rfl

theorem cell22_2981172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2981172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981172 prefixEnd_2981172 := by exact prefixLift 2981172
  have htrace : WordTrace (prefixWord ++ tailWord_2981172) baseStart_2981172 baseEnd_2981172 := by
    simpa [prefixWord, tailWord_2981172, baseEnd_2981172] using wordTrace_append hprefix tailTrace_2981172
  have hstable : (prefixWord ++ tailWord_2981172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981172).length < 2 ^ (prefixWord ++ tailWord_2981172).sum := by decide
  have hdescent : baseEnd_2981172 < baseStart_2981172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981245 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2981245 : Nat := 118140960795 + 2981245 * 2 ^ 59
def prefixEnd_2981245 : Nat := 4983230072969 + 3 ^ 40 * 2981245 * 2
def baseEnd_2981245 : Nat := 1020541089208862399284673

theorem tailTrace_2981245 : CollatzResearch.WordTrace tailWord_2981245 prefixEnd_2981245 1020541089208862399284673 := by
  unfold tailWord_2981245
  simp only [CollatzResearch.WordTrace]
  refine ⟨108734938084465995955121189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72489958722977330636747459 108734938084465995955121189)
  ·
    refine ⟨20387800890837374241585223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108734938084465995955121189 20387800890837374241585223)
    ·
      refine ⟨30581701336256061362377835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20387800890837374241585223 30581701336256061362377835)
      ·
        refine ⟨45872552004384092043566753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30581701336256061362377835 45872552004384092043566753)
        ·
          refine ⟨34404414003288069032675065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45872552004384092043566753 34404414003288069032675065)
          ·
            refine ⟨25803310502466051774506299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34404414003288069032675065 25803310502466051774506299)
            ·
              refine ⟨38704965753699077661759449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25803310502466051774506299 38704965753699077661759449)
              ·
                refine ⟨29028724315274308246319587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38704965753699077661759449 29028724315274308246319587)
                ·
                  refine ⟨43543086472911462369479381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29028724315274308246319587 43543086472911462369479381)
                  ·
                    refine ⟨1020541089208862399284673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43543086472911462369479381 1020541089208862399284673)
                    ·
                      rfl

theorem cell22_2981245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2981245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981245 prefixEnd_2981245 := by exact prefixLift 2981245
  have htrace : WordTrace (prefixWord ++ tailWord_2981245) baseStart_2981245 baseEnd_2981245 := by
    simpa [prefixWord, tailWord_2981245, baseEnd_2981245] using wordTrace_append hprefix tailTrace_2981245
  have hstable : (prefixWord ++ tailWord_2981245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981245).length < 2 ^ (prefixWord ++ tailWord_2981245).sum := by decide
  have hdescent : baseEnd_2981245 < baseStart_2981245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981251 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 1, 3]
def baseStart_2981251 : Nat := 118140960795 + 2981251 * 2 ^ 59
def prefixEnd_2981251 : Nat := 4983230072969 + 3 ^ 40 * 2981251 * 2
def baseEnd_2981251 : Nat := 1020543143131480383634655

theorem tailTrace_2981251 : CollatzResearch.WordTrace tailWord_2981251 prefixEnd_2981251 1020543143131480383634655 := by
  unfold tailWord_2981251
  simp only [CollatzResearch.WordTrace]
  refine ⟨108735156922444258979839607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72490104614962839319893071 108735156922444258979839607)
  ·
    refine ⟨163102735383666388469759411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108735156922444258979839607 163102735383666388469759411)
    ·
      refine ⟨244654103075499582704639117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163102735383666388469759411 244654103075499582704639117)
      ·
        refine ⟨91745288653312343514239669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244654103075499582704639117 91745288653312343514239669)
        ·
          refine ⟨8601120811248032204459969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91745288653312343514239669 8601120811248032204459969)
          ·
            refine ⟨6450840608436024153344977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8601120811248032204459969 6450840608436024153344977)
            ·
              refine ⟨4838130456327018115008733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450840608436024153344977 4838130456327018115008733)
              ·
                refine ⟨1814298921122631793128275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4838130456327018115008733 1814298921122631793128275)
                ·
                  refine ⟨2721448381683947689692413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814298921122631793128275 2721448381683947689692413)
                  ·
                    refine ⟨1020543143131480383634655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721448381683947689692413 1020543143131480383634655)
                    ·
                      rfl

theorem cell22_2981251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 3].length) (baseStart_2981251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981251 prefixEnd_2981251 := by exact prefixLift 2981251
  have htrace : WordTrace (prefixWord ++ tailWord_2981251) baseStart_2981251 baseEnd_2981251 := by
    simpa [prefixWord, tailWord_2981251, baseEnd_2981251] using wordTrace_append hprefix tailTrace_2981251
  have hstable : (prefixWord ++ tailWord_2981251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981251).length < 2 ^ (prefixWord ++ tailWord_2981251).sum := by decide
  have hdescent : baseEnd_2981251 < baseStart_2981251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981322 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2981322 : Nat := 118140960795 + 2981322 * 2 ^ 59
def prefixEnd_2981322 : Nat := 4983230072969 + 3 ^ 40 * 2981322 * 2
def baseEnd_2981322 : Nat := 1020567447882459865109437

theorem tailTrace_2981322 : CollatzResearch.WordTrace tailWord_2981322 prefixEnd_2981322 1020567447882459865109437 := by
  unfold tailWord_2981322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27184436626296759526418555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72491831003458025403782813 27184436626296759526418555)
  ·
    refine ⟨40776654939445139289627833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27184436626296759526418555 40776654939445139289627833)
    ·
      refine ⟨30582491204583854467220875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40776654939445139289627833 30582491204583854467220875)
      ·
        refine ⟨45873736806875781700831313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30582491204583854467220875 45873736806875781700831313)
        ·
          refine ⟨34405302605156836275623485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45873736806875781700831313 34405302605156836275623485)
          ·
            refine ⟨12901988476933813603358807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34405302605156836275623485 12901988476933813603358807)
            ·
              refine ⟨19352982715400720405038211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901988476933813603358807 19352982715400720405038211)
              ·
                refine ⟨29029474073101080607557317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19352982715400720405038211 29029474073101080607557317)
                ·
                  refine ⟨5443026388706452613916997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29029474073101080607557317 5443026388706452613916997)
                  ·
                    refine ⟨1020567447882459865109437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5443026388706452613916997 1020567447882459865109437)
                    ·
                      rfl

theorem cell22_2981322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2981322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981322 prefixEnd_2981322 := by exact prefixLift 2981322
  have htrace : WordTrace (prefixWord ++ tailWord_2981322) baseStart_2981322 baseEnd_2981322 := by
    simpa [prefixWord, tailWord_2981322, baseEnd_2981322] using wordTrace_append hprefix tailTrace_2981322
  have hstable : (prefixWord ++ tailWord_2981322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981322).length < 2 ^ (prefixWord ++ tailWord_2981322).sum := by decide
  have hdescent : baseEnd_2981322 < baseStart_2981322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981324 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_2981324 : Nat := 118140960795 + 2981324 * 2 ^ 59
def prefixEnd_2981324 : Nat := 4983230072969 + 3 ^ 40 * 2981324 * 2
def baseEnd_2981324 : Nat := 1020568132523332526559431

theorem tailTrace_2981324 : CollatzResearch.WordTrace tailWord_2981324 prefixEnd_2981324 1020568132523332526559431 := by
  unfold tailWord_2981324
  simp only [CollatzResearch.WordTrace]
  refine ⟨54368909725589896223623513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72491879634119861631498017 54368909725589896223623513)
  ·
    refine ⟨40776682294192422167717635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54368909725589896223623513 40776682294192422167717635)
    ·
      refine ⟨61165023441288633251576453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40776682294192422167717635 61165023441288633251576453)
      ·
        refine ⟨11468441895241618734670585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61165023441288633251576453 11468441895241618734670585)
        ·
          refine ⟨8601331421431214051002939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11468441895241618734670585 8601331421431214051002939)
          ·
            refine ⟨12901997132146821076504409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8601331421431214051002939 12901997132146821076504409)
            ·
              refine ⟨9676497849110115807378307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12901997132146821076504409 9676497849110115807378307)
              ·
                refine ⟨14514746773665173711067461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676497849110115807378307 14514746773665173711067461)
                ·
                  refine ⟨2721515020062220070825149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14514746773665173711067461 2721515020062220070825149)
                  ·
                    refine ⟨1020568132523332526559431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721515020062220070825149 1020568132523332526559431)
                    ·
                      rfl

theorem cell22_2981324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_2981324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981324 prefixEnd_2981324 := by exact prefixLift 2981324
  have htrace : WordTrace (prefixWord ++ tailWord_2981324) baseStart_2981324 baseEnd_2981324 := by
    simpa [prefixWord, tailWord_2981324, baseEnd_2981324] using wordTrace_append hprefix tailTrace_2981324
  have hstable : (prefixWord ++ tailWord_2981324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981324).length < 2 ^ (prefixWord ++ tailWord_2981324).sum := by decide
  have hdescent : baseEnd_2981324 < baseStart_2981324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981337 : List Nat := [1, 2, 1, 2, 4, 3, 2, 7]
def baseStart_2981337 : Nat := 118140960795 + 2981337 * 2 ^ 59
def prefixEnd_2981337 : Nat := 4983230072969 + 3 ^ 40 * 2981337 * 2
def baseEnd_2981337 : Nat := 113396953632111647331599

theorem tailTrace_2981337 : CollatzResearch.WordTrace tailWord_2981337 prefixEnd_2981337 113396953632111647331599 := by
  unfold tailWord_2981337
  simp only [CollatzResearch.WordTrace]
  refine ⟨108738293600132695667470265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72492195733421797111646843 108738293600132695667470265)
  ·
    refine ⟨81553720200099521750602699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108738293600132695667470265 81553720200099521750602699)
    ·
      refine ⟨122330580300149282625904049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81553720200099521750602699 122330580300149282625904049)
      ·
        refine ⟨91747935225111961969428037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122330580300149282625904049 91747935225111961969428037)
        ·
          refine ⟨17202737854708492869267757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91747935225111961969428037 17202737854708492869267757)
          ·
            refine ⟨6451026695515684825975409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17202737854708492869267757 6451026695515684825975409)
            ·
              refine ⟨4838270021636763619481557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6451026695515684825975409 4838270021636763619481557)
              ·
                refine ⟨113396953632111647331599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4838270021636763619481557 113396953632111647331599)
                ·
                  rfl

theorem cell22_2981337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 7].length) (baseStart_2981337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981337 prefixEnd_2981337 := by exact prefixLift 2981337
  have htrace : WordTrace (prefixWord ++ tailWord_2981337) baseStart_2981337 baseEnd_2981337 := by
    simpa [prefixWord, tailWord_2981337, baseEnd_2981337] using wordTrace_append hprefix tailTrace_2981337
  have hstable : (prefixWord ++ tailWord_2981337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981337).length < 2 ^ (prefixWord ++ tailWord_2981337).sum := by decide
  have hdescent : baseEnd_2981337 < baseStart_2981337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981341 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2981341 : Nat := 118140960795 + 2981341 * 2 ^ 59
def prefixEnd_2981341 : Nat := 4983230072969 + 3 ^ 40 * 2981341 * 2
def baseEnd_2981341 : Nat := 1020573951970750148884379

theorem tailTrace_2981341 : CollatzResearch.WordTrace tailWord_2981341 prefixEnd_2981341 1020573951970750148884379 := by
  unfold tailWord_2981341
  simp only [CollatzResearch.WordTrace]
  refine ⟨108738439492118204350615877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72492292994745469567077251 108738439492118204350615877)
  ·
    refine ⟨20388457404772163315740477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108738439492118204350615877 20388457404772163315740477)
    ·
      refine ⟨7645671526789561243402679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20388457404772163315740477 7645671526789561243402679)
      ·
        refine ⟨11468507290184341865104019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645671526789561243402679 11468507290184341865104019)
        ·
          refine ⟨17202760935276512797656029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468507290184341865104019 17202760935276512797656029)
          ·
            refine ⟨6451035350728692299121011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17202760935276512797656029 6451035350728692299121011)
            ·
              refine ⟨9676553026093038448681517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451035350728692299121011 9676553026093038448681517)
              ·
                refine ⟨3628707384784889418255569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9676553026093038448681517 3628707384784889418255569)
                ·
                  refine ⟨2721530538588667063691677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628707384784889418255569 2721530538588667063691677)
                  ·
                    refine ⟨1020573951970750148884379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721530538588667063691677 1020573951970750148884379)
                    ·
                      rfl

theorem cell22_2981341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2981341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981341 prefixEnd_2981341 := by exact prefixLift 2981341
  have htrace : WordTrace (prefixWord ++ tailWord_2981341) baseStart_2981341 baseEnd_2981341 := by
    simpa [prefixWord, tailWord_2981341, baseEnd_2981341] using wordTrace_append hprefix tailTrace_2981341
  have hstable : (prefixWord ++ tailWord_2981341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981341).length < 2 ^ (prefixWord ++ tailWord_2981341).sum := by decide
  have hdescent : baseEnd_2981341 < baseStart_2981341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981397 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2981397 : Nat := 118140960795 + 2981397 * 2 ^ 59
def prefixEnd_2981397 : Nat := 4983230072969 + 3 ^ 40 * 2981397 * 2
def baseEnd_2981397 : Nat := 1020593121915184669484207

theorem tailTrace_2981397 : CollatzResearch.WordTrace tailWord_2981397 prefixEnd_2981397 1020593121915184669484207 := by
  unfold tailWord_2981397
  simp only [CollatzResearch.WordTrace]
  refine ⟨108740481979915325914654445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72493654653276883943102963 108740481979915325914654445)
  ·
    refine ⟨40777680742468247217995417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108740481979915325914654445 40777680742468247217995417)
    ·
      refine ⟨30583260556851185413496563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40777680742468247217995417 30583260556851185413496563)
      ·
        refine ⟨45874890835276778120244845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30583260556851185413496563 45874890835276778120244845)
        ·
          refine ⟨17203084063228791795091817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45874890835276778120244845 17203084063228791795091817)
          ·
            refine ⟨12902313047421593846318863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17203084063228791795091817 12902313047421593846318863)
            ·
              refine ⟨19353469571132390769478295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12902313047421593846318863 19353469571132390769478295)
              ·
                refine ⟨29030204356698586154217443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19353469571132390769478295 29030204356698586154217443)
                ·
                  refine ⟨43545306535047879231326165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29030204356698586154217443 43545306535047879231326165)
                  ·
                    refine ⟨1020593121915184669484207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43545306535047879231326165 1020593121915184669484207)
                    ·
                      rfl

theorem cell22_2981397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2981397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981397 prefixEnd_2981397 := by exact prefixLift 2981397
  have htrace : WordTrace (prefixWord ++ tailWord_2981397) baseStart_2981397 baseEnd_2981397 := by
    simpa [prefixWord, tailWord_2981397, baseEnd_2981397] using wordTrace_append hprefix tailTrace_2981397
  have hstable : (prefixWord ++ tailWord_2981397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981397).length < 2 ^ (prefixWord ++ tailWord_2981397).sum := by decide
  have hdescent : baseEnd_2981397 < baseStart_2981397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981457 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2981457 : Nat := 118140960795 + 2981457 * 2 ^ 59
def prefixEnd_2981457 : Nat := 4983230072969 + 3 ^ 40 * 2981457 * 2
def baseEnd_2981457 : Nat := 1020613661141364512984023

theorem tailTrace_2981457 : CollatzResearch.WordTrace tailWord_2981457 prefixEnd_2981457 1020613661141364512984023 := by
  unfold tailWord_2981457
  simp only [CollatzResearch.WordTrace]
  refine ⟨108742670359697956161838625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72495113573131970774559083 108742670359697956161838625)
  ·
    refine ⟨81557002769773467121378969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108742670359697956161838625 81557002769773467121378969)
    ·
      refine ⟨61167752077330100341034227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81557002769773467121378969 61167752077330100341034227)
      ·
        refine ⟨91751628115995150511551341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61167752077330100341034227 91751628115995150511551341)
        ·
          refine ⟨34406860543498181441831753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91751628115995150511551341 34406860543498181441831753)
          ·
            refine ⟨25805145407623636081373815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34406860543498181441831753 25805145407623636081373815)
            ·
              refine ⟨38707718111435454122060723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25805145407623636081373815 38707718111435454122060723)
              ·
                refine ⟨58061577167153181183091085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38707718111435454122060723 58061577167153181183091085)
                ·
                  refine ⟨21773091437682442943659157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58061577167153181183091085 21773091437682442943659157)
                  ·
                    refine ⟨1020613661141364512984023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21773091437682442943659157 1020613661141364512984023)
                    ·
                      rfl

theorem cell22_2981457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2981457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981457 prefixEnd_2981457 := by exact prefixLift 2981457
  have htrace : WordTrace (prefixWord ++ tailWord_2981457) baseStart_2981457 baseEnd_2981457 := by
    simpa [prefixWord, tailWord_2981457, baseEnd_2981457] using wordTrace_append hprefix tailTrace_2981457
  have hstable : (prefixWord ++ tailWord_2981457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981457).length < 2 ^ (prefixWord ++ tailWord_2981457).sum := by decide
  have hdescent : baseEnd_2981457 < baseStart_2981457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981566 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2981566 : Nat := 118140960795 + 2981566 * 2 ^ 59
def prefixEnd_2981566 : Nat := 4983230072969 + 3 ^ 40 * 2981566 * 2
def baseEnd_2981566 : Nat := 1020650974068924562008689

theorem tailTrace_2981566 : CollatzResearch.WordTrace tailWord_2981566 prefixEnd_2981566 1020650974068924562008689 := by
  unfold tailWord_2981566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593330739537883472194569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72497763944202045185037701 13593330739537883472194569)
  ·
    refine ⟨10194998054653412604145927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13593330739537883472194569 10194998054653412604145927)
    ·
      refine ⟨15292497081980118906218891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10194998054653412604145927 15292497081980118906218891)
      ·
        refine ⟨22938745622970178359328337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15292497081980118906218891 22938745622970178359328337)
        ·
          refine ⟨17204059217227633769496253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22938745622970178359328337 17204059217227633769496253)
          ·
            refine ⟨6451522206460362663561095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17204059217227633769496253 6451522206460362663561095)
            ·
              refine ⟨9677283309690543995341643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451522206460362663561095 9677283309690543995341643)
              ·
                refine ⟨14515924964535815993012465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9677283309690543995341643 14515924964535815993012465)
                ·
                  refine ⟨10886943723401861994759349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14515924964535815993012465 10886943723401861994759349)
                  ·
                    refine ⟨1020650974068924562008689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10886943723401861994759349 1020650974068924562008689)
                    ·
                      rfl

theorem cell22_2981566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2981566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981566 prefixEnd_2981566 := by exact prefixLift 2981566
  have htrace : WordTrace (prefixWord ++ tailWord_2981566) baseStart_2981566 baseEnd_2981566 := by
    simpa [prefixWord, tailWord_2981566, baseEnd_2981566] using wordTrace_append hprefix tailTrace_2981566
  have hstable : (prefixWord ++ tailWord_2981566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981566).length < 2 ^ (prefixWord ++ tailWord_2981566).sum := by decide
  have hdescent : baseEnd_2981566 < baseStart_2981566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981609 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_2981609 : Nat := 118140960795 + 2981609 * 2 ^ 59
def prefixEnd_2981609 : Nat := 4983230072969 + 3 ^ 40 * 2981609 * 2
def baseEnd_2981609 : Nat := 1020665693847686783183557

theorem tailTrace_2981609 : CollatzResearch.WordTrace tailWord_2981609 prefixEnd_2981609 1020665693847686783183557 := by
  unfold tailWord_2981609
  simp only [CollatzResearch.WordTrace]
  refine ⟨108748214255147286121371881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72498809503431524080914587 108748214255147286121371881)
  ·
    refine ⟨81561160691360464591028911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108748214255147286121371881 81561160691360464591028911)
    ·
      refine ⟨122341741037040696886543367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81561160691360464591028911 122341741037040696886543367)
      ·
        refine ⟨183512611555561045329815051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122341741037040696886543367 183512611555561045329815051)
        ·
          refine ⟨275268917333341567994722577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183512611555561045329815051 275268917333341567994722577)
          ·
            refine ⟨206451688000006175996041933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275268917333341567994722577 206451688000006175996041933)
            ·
              refine ⟨77419383000002315998515725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206451688000006175996041933 77419383000002315998515725)
              ·
                refine ⟨29032268625000868499443397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77419383000002315998515725 29032268625000868499443397)
                ·
                  refine ⟨5443550367187662843645637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29032268625000868499443397 5443550367187662843645637)
                  ·
                    refine ⟨1020665693847686783183557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5443550367187662843645637 1020665693847686783183557)
                    ·
                      rfl

theorem cell22_2981609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_2981609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981609 prefixEnd_2981609 := by exact prefixLift 2981609
  have htrace : WordTrace (prefixWord ++ tailWord_2981609) baseStart_2981609 baseEnd_2981609 := by
    simpa [prefixWord, tailWord_2981609, baseEnd_2981609] using wordTrace_append hprefix tailTrace_2981609
  have hstable : (prefixWord ++ tailWord_2981609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981609).length < 2 ^ (prefixWord ++ tailWord_2981609).sum := by decide
  have hdescent : baseEnd_2981609 < baseStart_2981609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981613 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2981613 : Nat := 118140960795 + 2981613 * 2 ^ 59
def prefixEnd_2981613 : Nat := 4983230072969 + 3 ^ 40 * 2981613 * 2
def baseEnd_2981613 : Nat := 340222354376477368694515

theorem tailTrace_2981613 : CollatzResearch.WordTrace tailWord_2981613 prefixEnd_2981613 340222354376477368694515 := by
  unfold tailWord_2981613
  simp only [CollatzResearch.WordTrace]
  refine ⟨108748360147132794804517493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72498906764755196536344995 108748360147132794804517493)
  ·
    refine ⟨10195158763793699512923515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108748360147132794804517493 10195158763793699512923515)
    ·
      refine ⟨15292738145690549269385273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10195158763793699512923515 15292738145690549269385273)
      ·
        refine ⟨11469553609267911952038955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15292738145690549269385273 11469553609267911952038955)
        ·
          refine ⟨17204330413901867928058433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11469553609267911952038955 17204330413901867928058433)
          ·
            refine ⟨12903247810426400946043825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17204330413901867928058433 12903247810426400946043825)
            ·
              refine ⟨9677435857819800709532869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12903247810426400946043825 9677435857819800709532869)
              ·
                refine ⟨1814519223341212633037413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9677435857819800709532869 1814519223341212633037413)
                ·
                  refine ⟨340222354376477368694515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1814519223341212633037413 340222354376477368694515)
                  ·
                    rfl

theorem cell22_2981613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2981613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981613 prefixEnd_2981613 := by exact prefixLift 2981613
  have htrace : WordTrace (prefixWord ++ tailWord_2981613) baseStart_2981613 baseEnd_2981613 := by
    simpa [prefixWord, tailWord_2981613, baseEnd_2981613] using wordTrace_append hprefix tailTrace_2981613
  have hstable : (prefixWord ++ tailWord_2981613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981613).length < 2 ^ (prefixWord ++ tailWord_2981613).sum := by decide
  have hdescent : baseEnd_2981613 < baseStart_2981613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981656 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_2981656 : Nat := 118140960795 + 2981656 * 2 ^ 59
def prefixEnd_2981656 : Nat := 4983230072969 + 3 ^ 40 * 2981656 * 2
def baseEnd_2981656 : Nat := 1020681782908194327258413

theorem tailTrace_2981656 : CollatzResearch.WordTrace tailWord_2981656 prefixEnd_2981656 1020681782908194327258413 := by
  unfold tailWord_2981656
  simp only [CollatzResearch.WordTrace]
  refine ⟨54374964242988506574166411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72499952323984675432221881 54374964242988506574166411)
  ·
    refine ⟨81562446364482759861249617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54374964242988506574166411 81562446364482759861249617)
    ·
      refine ⟨61171834773362069895937213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81562446364482759861249617 61171834773362069895937213)
      ·
        refine ⟨22939438040010776210976455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61171834773362069895937213 22939438040010776210976455)
        ·
          refine ⟨34409157060016164316464683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22939438040010776210976455 34409157060016164316464683)
          ·
            refine ⟨51613735590024246474697025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34409157060016164316464683 51613735590024246474697025)
            ·
              refine ⟨38710301692518184856022769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51613735590024246474697025 38710301692518184856022769)
              ·
                refine ⟨29032726269388638642017077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38710301692518184856022769 29032726269388638642017077)
                ·
                  refine ⟨2721818087755184872689101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29032726269388638642017077 2721818087755184872689101)
                  ·
                    refine ⟨1020681782908194327258413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721818087755184872689101 1020681782908194327258413)
                    ·
                      rfl

theorem cell22_2981656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_2981656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981656 prefixEnd_2981656 := by exact prefixLift 2981656
  have htrace : WordTrace (prefixWord ++ tailWord_2981656) baseStart_2981656 baseEnd_2981656 := by
    simpa [prefixWord, tailWord_2981656, baseEnd_2981656] using wordTrace_append hprefix tailTrace_2981656
  have hstable : (prefixWord ++ tailWord_2981656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981656).length < 2 ^ (prefixWord ++ tailWord_2981656).sum := by decide
  have hdescent : baseEnd_2981656 < baseStart_2981656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981767 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 1, 4]
def baseStart_2981767 : Nat := 118140960795 + 2981767 * 2 ^ 59
def prefixEnd_2981767 : Nat := 4983230072969 + 3 ^ 40 * 2981767 * 2
def baseEnd_2981767 : Nat := 1020719780476627037733073

theorem tailTrace_2981767 : CollatzResearch.WordTrace tailWord_2981767 prefixEnd_2981767 1020719780476627037733073 := by
  unfold tailWord_2981767
  simp only [CollatzResearch.WordTrace]
  refine ⟨108753976988574879105623555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72502651325716586070415703 108753976988574879105623555)
  ·
    refine ⟨163130965482862318658435333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108753976988574879105623555 163130965482862318658435333)
    ·
      refine ⟨30587056028036684748456625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163130965482862318658435333 30587056028036684748456625)
      ·
        refine ⟨22940292021027513561342469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30587056028036684748456625 22940292021027513561342469)
        ·
          refine ⟨4301304753942658792751713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22940292021027513561342469 4301304753942658792751713)
          ·
            refine ⟨3225978565456994094563785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4301304753942658792751713 3225978565456994094563785)
            ·
              refine ⟨2419483924092745570922839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3225978565456994094563785 2419483924092745570922839)
              ·
                refine ⟨3629225886139118356384259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419483924092745570922839 3629225886139118356384259)
                ·
                  refine ⟨5443838829208677534576389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629225886139118356384259 5443838829208677534576389)
                  ·
                    refine ⟨1020719780476627037733073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5443838829208677534576389 1020719780476627037733073)
                    ·
                      rfl

theorem cell22_2981767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_2981767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981767 prefixEnd_2981767 := by exact prefixLift 2981767
  have htrace : WordTrace (prefixWord ++ tailWord_2981767) baseStart_2981767 baseEnd_2981767 := by
    simpa [prefixWord, tailWord_2981767, baseEnd_2981767] using wordTrace_append hprefix tailTrace_2981767
  have hstable : (prefixWord ++ tailWord_2981767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981767).length < 2 ^ (prefixWord ++ tailWord_2981767).sum := by decide
  have hdescent : baseEnd_2981767 < baseStart_2981767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981780 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2981780 : Nat := 118140960795 + 2981780 * 2 ^ 59
def prefixEnd_2981780 : Nat := 4983230072969 + 3 ^ 40 * 2981780 * 2
def baseEnd_2981780 : Nat := 1020724230642299337158033

theorem tailTrace_2981780 : CollatzResearch.WordTrace tailWord_2981780 prefixEnd_2981780 1020724230642299337158033 := by
  unfold tailWord_2981780
  simp only [CollatzResearch.WordTrace]
  refine ⟨54377225568763891162923397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72502967425018521550564529 54377225568763891162923397)
  ·
    refine ⟨10195729794143229593048137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54377225568763891162923397 10195729794143229593048137)
    ·
      refine ⟨7646797345607422194786103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10195729794143229593048137 7646797345607422194786103)
      ·
        refine ⟨11470196018411133292179155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646797345607422194786103 11470196018411133292179155)
        ·
          refine ⟨17205294027616699938268733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11470196018411133292179155 17205294027616699938268733)
          ·
            refine ⟨6451985260356262476850775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17205294027616699938268733 6451985260356262476850775)
            ·
              refine ⟨9677977890534393715276163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451985260356262476850775 9677977890534393715276163)
              ·
                refine ⟨14516966835801590572914245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9677977890534393715276163 14516966835801590572914245)
                ·
                  refine ⟨2721931281712798232421421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14516966835801590572914245 2721931281712798232421421)
                  ·
                    refine ⟨1020724230642299337158033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721931281712798232421421 1020724230642299337158033)
                    ·
                      rfl

theorem cell22_2981780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2981780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981780 prefixEnd_2981780 := by exact prefixLift 2981780
  have htrace : WordTrace (prefixWord ++ tailWord_2981780) baseStart_2981780 baseEnd_2981780 := by
    simpa [prefixWord, tailWord_2981780, baseEnd_2981780] using wordTrace_append hprefix tailTrace_2981780
  have hstable : (prefixWord ++ tailWord_2981780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981780).length < 2 ^ (prefixWord ++ tailWord_2981780).sum := by decide
  have hdescent : baseEnd_2981780 < baseStart_2981780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981838 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2981838 : Nat := 118140960795 + 2981838 * 2 ^ 59
def prefixEnd_2981838 : Nat := 4983230072969 + 3 ^ 40 * 2981838 * 2
def baseEnd_2981838 : Nat := 340248028409202173069285

theorem tailTrace_2981838 : CollatzResearch.WordTrace tailWord_2981838 prefixEnd_2981838 340248028409202173069285 := by
  unfold tailWord_2981838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13594570821414707278932271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72504377714211772154305445 13594570821414707278932271)
  ·
    refine ⟨20391856232122060918398407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13594570821414707278932271 20391856232122060918398407)
    ·
      refine ⟨30587784348183091377597611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20391856232122060918398407 30587784348183091377597611)
      ·
        refine ⟨45881676522274637066396417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30587784348183091377597611 45881676522274637066396417)
        ·
          refine ⟨34411257391705977799797313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45881676522274637066396417 34411257391705977799797313)
          ·
            refine ⟨25808443043779483349847985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34411257391705977799797313 25808443043779483349847985)
            ·
              refine ⟨19356332282834612512385989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25808443043779483349847985 19356332282834612512385989)
              ·
                refine ⟨3629312303031489846072373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19356332282834612512385989 3629312303031489846072373)
                ·
                  refine ⟨340248028409202173069285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3629312303031489846072373 340248028409202173069285)
                  ·
                    rfl

theorem cell22_2981838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2981838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981838 prefixEnd_2981838 := by exact prefixLift 2981838
  have htrace : WordTrace (prefixWord ++ tailWord_2981838) baseStart_2981838 baseEnd_2981838 := by
    simpa [prefixWord, tailWord_2981838, baseEnd_2981838] using wordTrace_append hprefix tailTrace_2981838
  have hstable : (prefixWord ++ tailWord_2981838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981838).length < 2 ^ (prefixWord ++ tailWord_2981838).sum := by decide
  have hdescent : baseEnd_2981838 < baseStart_2981838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981855 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 5]
def baseStart_2981855 : Nat := 118140960795 + 2981855 * 2 ^ 59
def prefixEnd_2981855 : Nat := 4983230072969 + 3 ^ 40 * 2981855 * 2
def baseEnd_2981855 : Nat := 340249968225008047177601

theorem tailTrace_2981855 : CollatzResearch.WordTrace tailWord_2981855 prefixEnd_2981855 340249968225008047177601 := by
  unfold tailWord_2981855
  simp only [CollatzResearch.WordTrace]
  refine ⟨108757186612256070134827019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72504791074837380089884679 108757186612256070134827019)
  ·
    refine ⟨163135779918384105202240529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108757186612256070134827019 163135779918384105202240529)
    ·
      refine ⟨122351834938788078901680397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163135779918384105202240529 122351834938788078901680397)
      ·
        refine ⟨45881938102045529588130149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122351834938788078901680397 45881938102045529588130149)
        ·
          refine ⟨8602863394133536797774403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45881938102045529588130149 8602863394133536797774403)
          ·
            refine ⟨12904295091200305196661605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8602863394133536797774403 12904295091200305196661605)
            ·
              refine ⟨2419555329600057224374051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12904295091200305196661605 2419555329600057224374051)
              ·
                refine ⟨3629332994400085836561077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419555329600057224374051 3629332994400085836561077)
                ·
                  refine ⟨340249968225008047177601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3629332994400085836561077 340249968225008047177601)
                  ·
                    rfl

theorem cell22_2981855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 5].length) (baseStart_2981855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981855 prefixEnd_2981855 := by exact prefixLift 2981855
  have htrace : WordTrace (prefixWord ++ tailWord_2981855) baseStart_2981855 baseEnd_2981855 := by
    simpa [prefixWord, tailWord_2981855, baseEnd_2981855] using wordTrace_append hprefix tailTrace_2981855
  have hstable : (prefixWord ++ tailWord_2981855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981855).length < 2 ^ (prefixWord ++ tailWord_2981855).sum := by decide
  have hdescent : baseEnd_2981855 < baseStart_2981855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981900 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 4]
def baseStart_2981900 : Nat := 118140960795 + 2981900 * 2 ^ 59
def prefixEnd_2981900 : Nat := 4983230072969 + 3 ^ 40 * 2981900 * 2
def baseEnd_2981900 : Nat := 340255103031553008052555

theorem tailTrace_2981900 : CollatzResearch.WordTrace tailWord_2981900 prefixEnd_2981900 340255103031553008052555 := by
  unfold tailWord_2981900
  simp only [CollatzResearch.WordTrace]
  refine ⟨54379413948546521410107577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72505885264728695213476769 54379413948546521410107577)
  ·
    refine ⟨40784560461409891057580683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54379413948546521410107577 40784560461409891057580683)
    ·
      refine ⟨61176840692114836586371025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40784560461409891057580683 61176840692114836586371025)
      ·
        refine ⟨45882630519086127439778269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61176840692114836586371025 45882630519086127439778269)
        ·
          refine ⟨17205986444657297789916851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45882630519086127439778269 17205986444657297789916851)
          ·
            refine ⟨25808979666985946684875277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17205986444657297789916851 25808979666985946684875277)
            ·
              refine ⟨9678367375119730006828229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25808979666985946684875277 9678367375119730006828229)
              ·
                refine ⟨1814693882834949376280293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9678367375119730006828229 1814693882834949376280293)
                ·
                  refine ⟨340255103031553008052555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1814693882834949376280293 340255103031553008052555)
                  ·
                    rfl

theorem cell22_2981900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_2981900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981900 prefixEnd_2981900 := by exact prefixLift 2981900
  have htrace : WordTrace (prefixWord ++ tailWord_2981900) baseStart_2981900 baseEnd_2981900 := by
    simpa [prefixWord, tailWord_2981900, baseEnd_2981900] using wordTrace_append hprefix tailTrace_2981900
  have hstable : (prefixWord ++ tailWord_2981900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981900).length < 2 ^ (prefixWord ++ tailWord_2981900).sum := by decide
  have hdescent : baseEnd_2981900 < baseStart_2981900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981930 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2981930 : Nat := 118140960795 + 2981930 * 2 ^ 59
def prefixEnd_2981930 : Nat := 4983230072969 + 3 ^ 40 * 2981930 * 2
def baseEnd_2981930 : Nat := 1020775578707748945907573

theorem tailTrace_2981930 : CollatzResearch.WordTrace tailWord_2981930 prefixEnd_2981930 1020775578707748945907573 := by
  unfold tailWord_2981930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189980521746089485951811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72506614724656238629204829 27189980521746089485951811)
  ·
    refine ⟨40784970782619134228927717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27189980521746089485951811 40784970782619134228927717)
    ·
      refine ⟨7647182021741087667923947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40784970782619134228927717 7647182021741087667923947)
      ·
        refine ⟨11470773032611631501885921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7647182021741087667923947 11470773032611631501885921)
        ·
          refine ⟨8603079774458723626414441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11470773032611631501885921 8603079774458723626414441)
          ·
            refine ⟨6452309830844042719810831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8603079774458723626414441 6452309830844042719810831)
            ·
              refine ⟨9678464746266064079716247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452309830844042719810831 9678464746266064079716247)
              ·
                refine ⟨14517697119399096119574371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9678464746266064079716247 14517697119399096119574371)
                ·
                  refine ⟨21776545679098644179361557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14517697119399096119574371 21776545679098644179361557)
                  ·
                    refine ⟨1020775578707748945907573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21776545679098644179361557 1020775578707748945907573)
                    ·
                      rfl

theorem cell22_2981930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2981930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981930 prefixEnd_2981930 := by exact prefixLift 2981930
  have htrace : WordTrace (prefixWord ++ tailWord_2981930) baseStart_2981930 baseEnd_2981930 := by
    simpa [prefixWord, tailWord_2981930, baseEnd_2981930] using wordTrace_append hprefix tailTrace_2981930
  have hstable : (prefixWord ++ tailWord_2981930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981930).length < 2 ^ (prefixWord ++ tailWord_2981930).sum := by decide
  have hdescent : baseEnd_2981930 < baseStart_2981930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981988 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2981988 : Nat := 118140960795 + 2981988 * 2 ^ 59
def prefixEnd_2981988 : Nat := 4983230072969 + 3 ^ 40 * 2981988 * 2
def baseEnd_2981988 : Nat := 1020795433293056127957395

theorem tailTrace_2981988 : CollatzResearch.WordTrace tailWord_2981988 prefixEnd_2981988 1020795433293056127957395 := by
  unfold tailWord_2981988
  simp only [CollatzResearch.WordTrace]
  refine ⟨54381018760387116924709309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72508025013849489232945745 54381018760387116924709309)
  ·
    refine ⟨20392882035145168846765991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54381018760387116924709309 20392882035145168846765991)
    ·
      refine ⟨30589323052717753270148987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20392882035145168846765991 30589323052717753270148987)
      ·
        refine ⟨45883984579076629905223481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30589323052717753270148987 45883984579076629905223481)
        ·
          refine ⟨34412988434307472428917611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45883984579076629905223481 34412988434307472428917611)
          ·
            refine ⟨51619482651461208643376417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34412988434307472428917611 51619482651461208643376417)
            ·
              refine ⟨38714611988595906482532313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51619482651461208643376417 38714611988595906482532313)
              ·
                refine ⟨29035958991446929861899235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38714611988595906482532313 29035958991446929861899235)
                ·
                  refine ⟨43553938487170394792848853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29035958991446929861899235 43553938487170394792848853)
                  ·
                    refine ⟨1020795433293056127957395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43553938487170394792848853 1020795433293056127957395)
                    ·
                      rfl

theorem cell22_2981988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2981988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2981988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2981988 prefixEnd_2981988 := by exact prefixLift 2981988
  have htrace : WordTrace (prefixWord ++ tailWord_2981988) baseStart_2981988 baseEnd_2981988 := by
    simpa [prefixWord, tailWord_2981988, baseEnd_2981988] using wordTrace_append hprefix tailTrace_2981988
  have hstable : (prefixWord ++ tailWord_2981988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981988).length < 2 ^ (prefixWord ++ tailWord_2981988).sum := by decide
  have hdescent : baseEnd_2981988 < baseStart_2981988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982020 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2982020 : Nat := 118140960795 + 2982020 * 2 ^ 59
def prefixEnd_2982020 : Nat := 4983230072969 + 3 ^ 40 * 2982020 * 2
def baseEnd_2982020 : Nat := 1020806387547018711157297

theorem tailTrace_2982020 : CollatzResearch.WordTrace tailWord_2982020 prefixEnd_2982020 1020806387547018711157297 := by
  unfold tailWord_2982020
  simp only [CollatzResearch.WordTrace]
  refine ⟨54381602328329151657291757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72508803104438868876389009 54381602328329151657291757)
  ·
    refine ⟨20393100873123431871484409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54381602328329151657291757 20393100873123431871484409)
    ·
      refine ⟨15294825654842573903613307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20393100873123431871484409 15294825654842573903613307)
      ·
        refine ⟨22942238482263860855419961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15294825654842573903613307 22942238482263860855419961)
        ·
          refine ⟨17206678861697895641564971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22942238482263860855419961 17206678861697895641564971)
          ·
            refine ⟨25810018292546843462347457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17206678861697895641564971 25810018292546843462347457)
            ·
              refine ⟨19357513719410132596760593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25810018292546843462347457 19357513719410132596760593)
              ·
                refine ⟨14518135289557599447570445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19357513719410132596760593 14518135289557599447570445)
                ·
                  refine ⟨5444300733584099792838917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14518135289557599447570445 5444300733584099792838917)
                  ·
                    refine ⟨1020806387547018711157297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5444300733584099792838917 1020806387547018711157297)
                    ·
                      rfl

theorem cell22_2982020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2982020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982020 prefixEnd_2982020 := by exact prefixLift 2982020
  have htrace : WordTrace (prefixWord ++ tailWord_2982020) baseStart_2982020 baseEnd_2982020 := by
    simpa [prefixWord, tailWord_2982020, baseEnd_2982020] using wordTrace_append hprefix tailTrace_2982020
  have hstable : (prefixWord ++ tailWord_2982020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982020).length < 2 ^ (prefixWord ++ tailWord_2982020).sum := by decide
  have hdescent : baseEnd_2982020 < baseStart_2982020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982024 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 5]
def baseStart_2982024 : Nat := 118140960795 + 2982024 * 2 ^ 59
def prefixEnd_2982024 : Nat := 4983230072969 + 3 ^ 40 * 2982024 * 2
def baseEnd_2982024 : Nat := 340269252276254678019095

theorem tailTrace_2982024 : CollatzResearch.WordTrace tailWord_2982024 prefixEnd_2982024 340269252276254678019095 := by
  unfold tailWord_2982024
  simp only [CollatzResearch.WordTrace]
  refine ⟨54381675274321905998864563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72508900365762541331819417 54381675274321905998864563)
  ·
    refine ⟨81572512911482858998296845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54381675274321905998864563 81572512911482858998296845)
    ·
      refine ⟨30589692341806072124361317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81572512911482858998296845 30589692341806072124361317)
      ·
        refine ⟨5735567314088638523317747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30589692341806072124361317 5735567314088638523317747)
        ·
          refine ⟨8603350971132957784976621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5735567314088638523317747 8603350971132957784976621)
          ·
            refine ⟨3226256614174859169366233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8603350971132957784976621 3226256614174859169366233)
            ·
              refine ⟨2419692460631144377024675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226256614174859169366233 2419692460631144377024675)
              ·
                refine ⟨3629538690946716565537013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419692460631144377024675 3629538690946716565537013)
                ·
                  refine ⟨340269252276254678019095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3629538690946716565537013 340269252276254678019095)
                  ·
                    rfl

theorem cell22_2982024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_2982024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982024 prefixEnd_2982024 := by exact prefixLift 2982024
  have htrace : WordTrace (prefixWord ++ tailWord_2982024) baseStart_2982024 baseEnd_2982024 := by
    simpa [prefixWord, tailWord_2982024, baseEnd_2982024] using wordTrace_append hprefix tailTrace_2982024
  have hstable : (prefixWord ++ tailWord_2982024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982024).length < 2 ^ (prefixWord ++ tailWord_2982024).sum := by decide
  have hdescent : baseEnd_2982024 < baseStart_2982024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982033 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2982033 : Nat := 118140960795 + 2982033 * 2 ^ 59
def prefixEnd_2982033 : Nat := 4983230072969 + 3 ^ 40 * 2982033 * 2
def baseEnd_2982033 : Nat := 1020810837712691010582257

theorem tailTrace_2982033 : CollatzResearch.WordTrace tailWord_2982033 prefixEnd_2982033 1020810837712691010582257 := by
  unfold tailWord_2982033
  simp only [CollatzResearch.WordTrace]
  refine ⟨108763678805611206534806753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72509119203740804356537835 108763678805611206534806753)
  ·
    refine ⟨81572759104208404901105065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108763678805611206534806753 81572759104208404901105065)
    ·
      refine ⟨61179569328156303675828799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81572759104208404901105065 61179569328156303675828799)
      ·
        refine ⟨91769353992234455513743199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61179569328156303675828799 91769353992234455513743199)
        ·
          refine ⟨137654030988351683270614799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91769353992234455513743199 137654030988351683270614799)
          ·
            refine ⟨206481046482527524905922199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137654030988351683270614799 206481046482527524905922199)
            ·
              refine ⟨309721569723791287358883299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206481046482527524905922199 309721569723791287358883299)
              ·
                refine ⟨464582354585686931038324949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309721569723791287358883299 464582354585686931038324949)
                ·
                  refine ⟨10888648935602037446210741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 464582354585686931038324949 10888648935602037446210741)
                  ·
                    refine ⟨1020810837712691010582257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10888648935602037446210741 1020810837712691010582257)
                    ·
                      rfl

theorem cell22_2982033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2982033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982033 prefixEnd_2982033 := by exact prefixLift 2982033
  have htrace : WordTrace (prefixWord ++ tailWord_2982033) baseStart_2982033 baseEnd_2982033 := by
    simpa [prefixWord, tailWord_2982033, baseEnd_2982033] using wordTrace_append hprefix tailTrace_2982033
  have hstable : (prefixWord ++ tailWord_2982033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982033).length < 2 ^ (prefixWord ++ tailWord_2982033).sum := by decide
  have hdescent : baseEnd_2982033 < baseStart_2982033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982062 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2982062 : Nat := 118140960795 + 2982062 * 2 ^ 59
def prefixEnd_2982062 : Nat := 4983230072969 + 3 ^ 40 * 2982062 * 2
def baseEnd_2982062 : Nat := 1020820765005344601607169

theorem tailTrace_2982062 : CollatzResearch.WordTrace tailWord_2982062 prefixEnd_2982062 1020820765005344601607169 := by
  unfold tailWord_2982062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595592065313268060951555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72509824348337429658408293 13595592065313268060951555)
  ·
    refine ⟨20393388097969902091427333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13595592065313268060951555 20393388097969902091427333)
    ·
      refine ⟨3823760268369356642142625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20393388097969902091427333 3823760268369356642142625)
      ·
        refine ⟨2867820201277017481606969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3823760268369356642142625 2867820201277017481606969)
        ·
          refine ⟨2150865150957763111205227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2867820201277017481606969 2150865150957763111205227)
          ·
            refine ⟨3226297726436644666807841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150865150957763111205227 3226297726436644666807841)
            ·
              refine ⟨2419723294827483500105881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226297726436644666807841 2419723294827483500105881)
              ·
                refine ⟨1814792471120612625079411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419723294827483500105881 1814792471120612625079411)
                ·
                  refine ⟨2722188706680918937619117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814792471120612625079411 2722188706680918937619117)
                  ·
                    refine ⟨1020820765005344601607169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722188706680918937619117 1020820765005344601607169)
                    ·
                      rfl

theorem cell22_2982062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2982062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982062 prefixEnd_2982062 := by exact prefixLift 2982062
  have htrace : WordTrace (prefixWord ++ tailWord_2982062) baseStart_2982062 baseEnd_2982062 := by
    simpa [prefixWord, tailWord_2982062, baseEnd_2982062] using wordTrace_append hprefix tailTrace_2982062
  have hstable : (prefixWord ++ tailWord_2982062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982062).length < 2 ^ (prefixWord ++ tailWord_2982062).sum := by decide
  have hdescent : baseEnd_2982062 < baseStart_2982062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982080 : List Nat := [2, 1, 1, 2, 5, 1, 3, 7]
def baseStart_2982080 : Nat := 118140960795 + 2982080 * 2 ^ 59
def prefixEnd_2982080 : Nat := 4983230072969 + 3 ^ 40 * 2982080 * 2
def baseEnd_2982080 : Nat := 113425214085910950517457

theorem tailTrace_2982080 : CollatzResearch.WordTrace tailWord_2982080 prefixEnd_2982080 113425214085910950517457 := by
  unfold tailWord_2982080
  simp only [CollatzResearch.WordTrace]
  refine ⟨54382696518220466780883847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72510262024293955707845129 54382696518220466780883847)
  ·
    refine ⟨81574044777330700171325771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54382696518220466780883847 81574044777330700171325771)
    ·
      refine ⟨122361067165996050256988657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81574044777330700171325771 122361067165996050256988657)
      ·
        refine ⟨91770800374497037692741493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122361067165996050256988657 91770800374497037692741493)
        ·
          refine ⟨8603512535109097283694515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91770800374497037692741493 8603512535109097283694515)
          ·
            refine ⟨12905268802663645925541773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603512535109097283694515 12905268802663645925541773)
            ·
              refine ⟨4839475800998867222078165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12905268802663645925541773 4839475800998867222078165)
              ·
                refine ⟨113425214085910950517457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4839475800998867222078165 113425214085910950517457)
                ·
                  rfl

theorem cell22_2982080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_2982080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982080 prefixEnd_2982080 := by exact prefixLift 2982080
  have htrace : WordTrace (prefixWord ++ tailWord_2982080) baseStart_2982080 baseEnd_2982080 := by
    simpa [prefixWord, tailWord_2982080, baseEnd_2982080] using wordTrace_append hprefix tailTrace_2982080
  have hstable : (prefixWord ++ tailWord_2982080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982080).length < 2 ^ (prefixWord ++ tailWord_2982080).sum := by decide
  have hdescent : baseEnd_2982080 < baseStart_2982080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982084 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2982084 : Nat := 118140960795 + 2982084 * 2 ^ 59
def prefixEnd_2982084 : Nat := 4983230072969 + 3 ^ 40 * 2982084 * 2
def baseEnd_2982084 : Nat := 1020828296054943877557101

theorem tailTrace_2982084 : CollatzResearch.WordTrace tailWord_2982084 prefixEnd_2982084 1020828296054943877557101 := by
  unfold tailWord_2982084
  simp only [CollatzResearch.WordTrace]
  refine ⟨54382769464213221122456653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72510359285617628163275537 54382769464213221122456653)
  ·
    refine ⟨20393538549079957920921245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54382769464213221122456653 20393538549079957920921245)
    ·
      refine ⟨7647576955904984220345467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20393538549079957920921245 7647576955904984220345467)
      ·
        refine ⟨11471365433857476330518201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7647576955904984220345467 11471365433857476330518201)
        ·
          refine ⟨8603524075393107247888651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11471365433857476330518201 8603524075393107247888651)
          ·
            refine ⟨12905286113089660871832977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603524075393107247888651 12905286113089660871832977)
            ·
              refine ⟨9678964584817245653874733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12905286113089660871832977 9678964584817245653874733)
              ·
                refine ⟨3629611719306467120203025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9678964584817245653874733 3629611719306467120203025)
                ·
                  refine ⟨2722208789479850340152269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629611719306467120203025 2722208789479850340152269)
                  ·
                    refine ⟨1020828296054943877557101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722208789479850340152269 1020828296054943877557101)
                    ·
                      rfl

theorem cell22_2982084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2982084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982084 prefixEnd_2982084 := by exact prefixLift 2982084
  have htrace : WordTrace (prefixWord ++ tailWord_2982084) baseStart_2982084 baseEnd_2982084 := by
    simpa [prefixWord, tailWord_2982084, baseEnd_2982084] using wordTrace_append hprefix tailTrace_2982084
  have hstable : (prefixWord ++ tailWord_2982084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982084).length < 2 ^ (prefixWord ++ tailWord_2982084).sum := by decide
  have hdescent : baseEnd_2982084 < baseStart_2982084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982129 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 1, 3]
def baseStart_2982129 : Nat := 118140960795 + 2982129 * 2 ^ 59
def prefixEnd_2982129 : Nat := 4983230072969 + 3 ^ 40 * 2982129 * 2
def baseEnd_2982129 : Nat := 1020843700474578760181963

theorem tailTrace_2982129 : CollatzResearch.WordTrace tailWord_2982129 prefixEnd_2982129 1020843700474578760181963 := by
  unfold tailWord_2982129
  simp only [CollatzResearch.WordTrace]
  refine ⟨108767180213263414930301441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72511453475508943286867627 108767180213263414930301441)
  ·
    refine ⟨81575385159947561197726081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108767180213263414930301441 81575385159947561197726081)
    ·
      refine ⟨61181538869960670898294561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81575385159947561197726081 61181538869960670898294561)
      ·
        refine ⟨45886154152470503173720921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61181538869960670898294561 45886154152470503173720921)
        ·
          refine ⟨34414615614352877380290691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45886154152470503173720921 34414615614352877380290691)
          ·
            refine ⟨51621923421529316070436037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34414615614352877380290691 51621923421529316070436037)
            ·
              refine ⟨9679110641536746763206757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51621923421529316070436037 9679110641536746763206757)
              ·
                refine ⟨1814833245288140018101267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9679110641536746763206757 1814833245288140018101267)
                ·
                  refine ⟨2722249867932210027151901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814833245288140018101267 2722249867932210027151901)
                  ·
                    refine ⟨1020843700474578760181963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722249867932210027151901 1020843700474578760181963)
                    ·
                      rfl

theorem cell22_2982129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_2982129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982129 prefixEnd_2982129 := by exact prefixLift 2982129
  have htrace : WordTrace (prefixWord ++ tailWord_2982129) baseStart_2982129 baseEnd_2982129 := by
    simpa [prefixWord, tailWord_2982129, baseEnd_2982129] using wordTrace_append hprefix tailTrace_2982129
  have hstable : (prefixWord ++ tailWord_2982129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982129).length < 2 ^ (prefixWord ++ tailWord_2982129).sum := by decide
  have hdescent : baseEnd_2982129 < baseStart_2982129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982200 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_2982200 : Nat := 118140960795 + 2982200 * 2 ^ 59
def prefixEnd_2982200 : Nat := 4983230072969 + 3 ^ 40 * 2982200 * 2
def baseEnd_2982200 : Nat := 1020868005225558241656745

theorem tailTrace_2982200 : CollatzResearch.WordTrace tailWord_2982200 prefixEnd_2982200 1020868005225558241656745 := by
  unfold tailWord_2982200
  simp only [CollatzResearch.WordTrace]
  refine ⟨54384884898003097028068027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72513179864004129370757369 54384884898003097028068027)
  ·
    refine ⟨81577327347004645542102041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54384884898003097028068027 81577327347004645542102041)
    ·
      refine ⟨61182995510253484156576531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81577327347004645542102041 61182995510253484156576531)
      ·
        refine ⟨91774493265380226234864797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61182995510253484156576531 91774493265380226234864797)
        ·
          refine ⟨34415434974517584838074299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91774493265380226234864797 34415434974517584838074299)
          ·
            refine ⟨51623152461776377257111449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34415434974517584838074299 51623152461776377257111449)
            ·
              refine ⟨38717364346332282942833587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51623152461776377257111449 38717364346332282942833587)
              ·
                refine ⟨58076046519498424414250381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38717364346332282942833587 58076046519498424414250381)
                ·
                  refine ⟨21778517444811909155343893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58076046519498424414250381 21778517444811909155343893)
                  ·
                    refine ⟨1020868005225558241656745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21778517444811909155343893 1020868005225558241656745)
                    ·
                      rfl

theorem cell22_2982200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_2982200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982200 prefixEnd_2982200 := by exact prefixLift 2982200
  have htrace : WordTrace (prefixWord ++ tailWord_2982200) baseStart_2982200 baseEnd_2982200 := by
    simpa [prefixWord, tailWord_2982200, baseEnd_2982200] using wordTrace_append hprefix tailTrace_2982200
  have hstable : (prefixWord ++ tailWord_2982200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982200).length < 2 ^ (prefixWord ++ tailWord_2982200).sum := by decide
  have hdescent : baseEnd_2982200 < baseStart_2982200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982206 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2982206 : Nat := 118140960795 + 2982206 * 2 ^ 59
def prefixEnd_2982206 : Nat := 4983230072969 + 3 ^ 40 * 2982206 * 2
def baseEnd_2982206 : Nat := 1020870059148176226006727

theorem tailTrace_2982206 : CollatzResearch.WordTrace tailWord_2982206 prefixEnd_2982206 1020870059148176226006727 := by
  unfold tailWord_2982206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13596248579248057135106809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72513325755989638053902981 13596248579248057135106809)
  ·
    refine ⟨10197186434436042851330107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13596248579248057135106809 10197186434436042851330107)
    ·
      refine ⟨15295779651654064276995161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10197186434436042851330107 15295779651654064276995161)
      ·
        refine ⟨11471834738740548207746371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15295779651654064276995161 11471834738740548207746371)
        ·
          refine ⟨17207752108110822311619557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11471834738740548207746371 17207752108110822311619557)
          ·
            refine ⟨3226453520270779183428667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17207752108110822311619557 3226453520270779183428667)
            ·
              refine ⟨4839680280406168775143001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226453520270779183428667 4839680280406168775143001)
              ·
                refine ⟨3629760210304626581357251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4839680280406168775143001 3629760210304626581357251)
                ·
                  refine ⟨5444640315456939872035877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629760210304626581357251 5444640315456939872035877)
                  ·
                    refine ⟨1020870059148176226006727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5444640315456939872035877 1020870059148176226006727)
                    ·
                      rfl

theorem cell22_2982206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2982206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982206 prefixEnd_2982206 := by exact prefixLift 2982206
  have htrace : WordTrace (prefixWord ++ tailWord_2982206) baseStart_2982206 baseEnd_2982206 := by
    simpa [prefixWord, tailWord_2982206, baseEnd_2982206] using wordTrace_append hprefix tailTrace_2982206
  have hstable : (prefixWord ++ tailWord_2982206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982206).length < 2 ^ (prefixWord ++ tailWord_2982206).sum := by decide
  have hdescent : baseEnd_2982206 < baseStart_2982206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982215 : List Nat := [1, 1, 4, 1, 2, 2, 1, 10]
def baseStart_2982215 : Nat := 118140960795 + 2982215 * 2 ^ 59
def prefixEnd_2982215 : Nat := 4983230072969 + 3 ^ 40 * 2982215 * 2
def baseEnd_2982215 : Nat := 113430348892455911392411

theorem tailTrace_2982215 : CollatzResearch.WordTrace tailWord_2982215 prefixEnd_2982215 113430348892455911392411 := by
  unfold tailWord_2982215
  simp only [CollatzResearch.WordTrace]
  refine ⟨108770316890951851617932099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72513544593967901078621399 108770316890951851617932099)
  ·
    refine ⟨163155475336427777426898149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108770316890951851617932099 163155475336427777426898149)
    ·
      refine ⟨30591651625580208267543403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163155475336427777426898149 30591651625580208267543403)
      ·
        refine ⟨45887477438370312401315105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30591651625580208267543403 45887477438370312401315105)
        ·
          refine ⟨34415608078777734300986329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45887477438370312401315105 34415608078777734300986329)
          ·
            refine ⟨25811706059083300725739747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34415608078777734300986329 25811706059083300725739747)
            ·
              refine ⟨38717559088624951088609621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25811706059083300725739747 38717559088624951088609621)
              ·
                refine ⟨113430348892455911392411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38717559088624951088609621 113430348892455911392411)
                ·
                  rfl

theorem cell22_2982215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 10].length) (baseStart_2982215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982215 prefixEnd_2982215 := by exact prefixLift 2982215
  have htrace : WordTrace (prefixWord ++ tailWord_2982215) baseStart_2982215 baseEnd_2982215 := by
    simpa [prefixWord, tailWord_2982215, baseEnd_2982215] using wordTrace_append hprefix tailTrace_2982215
  have hstable : (prefixWord ++ tailWord_2982215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982215).length < 2 ^ (prefixWord ++ tailWord_2982215).sum := by decide
  have hdescent : baseEnd_2982215 < baseStart_2982215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982281 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 1, 3]
def baseStart_2982281 : Nat := 118140960795 + 2982281 * 2 ^ 59
def prefixEnd_2982281 : Nat := 4983230072969 + 3 ^ 40 * 2982281 * 2
def baseEnd_2982281 : Nat := 1020895733180901030381497

theorem tailTrace_2982281 : CollatzResearch.WordTrace tailWord_2982281 prefixEnd_2982281 1020895733180901030381497 := by
  unfold tailWord_2982281
  simp only [CollatzResearch.WordTrace]
  refine ⟨108772724108712744889834697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72515149405808496593223131 108772724108712744889834697)
  ·
    refine ⟨81579543081534558667376023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108772724108712744889834697 81579543081534558667376023)
    ·
      refine ⟨122369314622301838001064035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81579543081534558667376023 122369314622301838001064035)
      ·
        refine ⟨183553971933452757001596053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122369314622301838001064035 183553971933452757001596053)
        ·
          refine ⟨8604092434380597984449815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183553971933452757001596053 8604092434380597984449815)
          ·
            refine ⟨12906138651570896976674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604092434380597984449815 12906138651570896976674723)
            ·
              refine ⟨19359207977356345465012085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906138651570896976674723 19359207977356345465012085)
              ·
                refine ⟨1814925747877157387344883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19359207977356345465012085 1814925747877157387344883)
                ·
                  refine ⟨2722388621815736081017325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814925747877157387344883 2722388621815736081017325)
                  ·
                    refine ⟨1020895733180901030381497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722388621815736081017325 1020895733180901030381497)
                    ·
                      rfl

theorem cell22_2982281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_2982281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982281 prefixEnd_2982281 := by exact prefixLift 2982281
  have htrace : WordTrace (prefixWord ++ tailWord_2982281) baseStart_2982281 baseEnd_2982281 := by
    simpa [prefixWord, tailWord_2982281, baseEnd_2982281] using wordTrace_append hprefix tailTrace_2982281
  have hstable : (prefixWord ++ tailWord_2982281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982281).length < 2 ^ (prefixWord ++ tailWord_2982281).sum := by decide
  have hdescent : baseEnd_2982281 < baseStart_2982281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982311 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 5]
def baseStart_2982311 : Nat := 118140960795 + 2982311 * 2 ^ 59
def prefixEnd_2982311 : Nat := 4983230072969 + 3 ^ 40 * 2982311 * 2
def baseEnd_2982311 : Nat := 340302000931330317377135

theorem tailTrace_2982311 : CollatzResearch.WordTrace tailWord_2982311 prefixEnd_2982311 340302000931330317377135 := by
  unfold tailWord_2982311
  simp only [CollatzResearch.WordTrace]
  refine ⟨108773818298604060013426787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72515878865736040008951191 108773818298604060013426787)
  ·
    refine ⟨163160727447906090020140181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108773818298604060013426787 163160727447906090020140181)
    ·
      refine ⟨7648159099120597969694071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163160727447906090020140181 7648159099120597969694071)
      ·
        refine ⟨11472238648680896954541107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7648159099120597969694071 11472238648680896954541107)
        ·
          refine ⟨17208357973021345431811661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11472238648680896954541107 17208357973021345431811661)
          ·
            refine ⟨6453134239883004536929373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17208357973021345431811661 6453134239883004536929373)
            ·
              refine ⟨2419925339956126701348515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6453134239883004536929373 2419925339956126701348515)
              ·
                refine ⟨3629888009934190052022773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419925339956126701348515 3629888009934190052022773)
                ·
                  refine ⟨340302000931330317377135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3629888009934190052022773 340302000931330317377135)
                  ·
                    rfl

theorem cell22_2982311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 5].length) (baseStart_2982311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982311 prefixEnd_2982311 := by exact prefixLift 2982311
  have htrace : WordTrace (prefixWord ++ tailWord_2982311) baseStart_2982311 baseEnd_2982311 := by
    simpa [prefixWord, tailWord_2982311, baseEnd_2982311] using wordTrace_append hprefix tailTrace_2982311
  have hstable : (prefixWord ++ tailWord_2982311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982311).length < 2 ^ (prefixWord ++ tailWord_2982311).sum := by decide
  have hdescent : baseEnd_2982311 < baseStart_2982311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982322 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_2982322 : Nat := 118140960795 + 2982322 * 2 ^ 59
def prefixEnd_2982322 : Nat := 4983230072969 + 3 ^ 40 * 2982322 * 2
def baseEnd_2982322 : Nat := 340303256106263530035457

theorem tailTrace_2982322 : CollatzResearch.WordTrace tailWord_2982322 prefixEnd_2982322 340303256106263530035457 := by
  unfold tailWord_2982322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27193554875391052223019305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72516146334376139261384813 27193554875391052223019305)
  ·
    refine ⟨20395166156543289167264479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27193554875391052223019305 20395166156543289167264479)
    ·
      refine ⟨30592749234814933750896719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20395166156543289167264479 30592749234814933750896719)
      ·
        refine ⟨45889123852222400626345079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30592749234814933750896719 45889123852222400626345079)
        ·
          refine ⟨68833685778333600939517619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45889123852222400626345079 68833685778333600939517619)
          ·
            refine ⟨103250528667500401409276429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68833685778333600939517619 103250528667500401409276429)
            ·
              refine ⟨38718948250312650528478661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103250528667500401409276429 38718948250312650528478661)
              ·
                refine ⟨7259802796933621974089749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38718948250312650528478661 7259802796933621974089749)
                ·
                  refine ⟨340303256106263530035457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7259802796933621974089749 340303256106263530035457)
                  ·
                    rfl

theorem cell22_2982322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_2982322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982322 prefixEnd_2982322 := by exact prefixLift 2982322
  have htrace : WordTrace (prefixWord ++ tailWord_2982322) baseStart_2982322 baseEnd_2982322 := by
    simpa [prefixWord, tailWord_2982322, baseEnd_2982322] using wordTrace_append hprefix tailTrace_2982322
  have hstable : (prefixWord ++ tailWord_2982322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982322).length < 2 ^ (prefixWord ++ tailWord_2982322).sum := by decide
  have hdescent : baseEnd_2982322 < baseStart_2982322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982356 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2982356 : Nat := 118140960795 + 2982356 * 2 ^ 59
def prefixEnd_2982356 : Nat := 4983230072969 + 3 ^ 40 * 2982356 * 2
def baseEnd_2982356 : Nat := 340307135737875278252089

theorem tailTrace_2982356 : CollatzResearch.WordTrace tailWord_2982356 prefixEnd_2982356 340307135737875278252089 := by
  unfold tailWord_2982356
  simp only [CollatzResearch.WordTrace]
  refine ⟨54387729791720516349407461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72516973055627355132543281 54387729791720516349407461)
  ·
    refine ⟨10197699335947596815513899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54387729791720516349407461 10197699335947596815513899)
    ·
      refine ⟨15296549003921395223270849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10197699335947596815513899 15296549003921395223270849)
      ·
        refine ⟨11472411752941046417453137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15296549003921395223270849 11472411752941046417453137)
        ·
          refine ⟨8604308814705784813089853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11472411752941046417453137 8604308814705784813089853)
          ·
            refine ⟨3226615805514669304908695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8604308814705784813089853 3226615805514669304908695)
            ·
              refine ⟨4839923708272003957363043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226615805514669304908695 4839923708272003957363043)
              ·
                refine ⟨7259885562408005936044565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839923708272003957363043 7259885562408005936044565)
                ·
                  refine ⟨340307135737875278252089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7259885562408005936044565 340307135737875278252089)
                  ·
                    rfl

theorem cell22_2982356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2982356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982356 prefixEnd_2982356 := by exact prefixLift 2982356
  have htrace : WordTrace (prefixWord ++ tailWord_2982356) baseStart_2982356 baseEnd_2982356 := by
    simpa [prefixWord, tailWord_2982356, baseEnd_2982356] using wordTrace_append hprefix tailTrace_2982356
  have hstable : (prefixWord ++ tailWord_2982356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982356).length < 2 ^ (prefixWord ++ tailWord_2982356).sum := by decide
  have hdescent : baseEnd_2982356 < baseStart_2982356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982367 : List Nat := [1, 1, 2, 3, 3, 2, 1, 9]
def baseStart_2982367 : Nat := 118140960795 + 2982367 * 2 ^ 59
def prefixEnd_2982367 : Nat := 4983230072969 + 3 ^ 40 * 2982367 * 2
def baseEnd_2982367 : Nat := 113436130304269496970137

theorem tailTrace_2982367 : CollatzResearch.WordTrace tailWord_2982367 prefixEnd_2982367 113436130304269496970137 := by
  unfold tailWord_2982367
  simp only [CollatzResearch.WordTrace]
  refine ⟨108775860786401181577465355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72517240524267454384976903 108775860786401181577465355)
  ·
    refine ⟨163163791179601772366198033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108775860786401181577465355 163163791179601772366198033)
    ·
      refine ⟨122372843384701329274648525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163163791179601772366198033 122372843384701329274648525)
      ·
        refine ⟨45889816269262998477993197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122372843384701329274648525 45889816269262998477993197)
        ·
          refine ⟨17208681100973624429247449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45889816269262998477993197 17208681100973624429247449)
          ·
            refine ⟨12906510825730218321935587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17208681100973624429247449 12906510825730218321935587)
            ·
              refine ⟨19359766238595327482903381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906510825730218321935587 19359766238595327482903381)
              ·
                refine ⟨113436130304269496970137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19359766238595327482903381 113436130304269496970137)
                ·
                  rfl

theorem cell22_2982367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 9].length) (baseStart_2982367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982367 prefixEnd_2982367 := by exact prefixLift 2982367
  have htrace : WordTrace (prefixWord ++ tailWord_2982367) baseStart_2982367 baseEnd_2982367 := by
    simpa [prefixWord, tailWord_2982367, baseEnd_2982367] using wordTrace_append hprefix tailTrace_2982367
  have hstable : (prefixWord ++ tailWord_2982367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982367).length < 2 ^ (prefixWord ++ tailWord_2982367).sum := by decide
  have hdescent : baseEnd_2982367 < baseStart_2982367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982414 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2982414 : Nat := 118140960795 + 2982414 * 2 ^ 59
def prefixEnd_2982414 : Nat := 4983230072969 + 3 ^ 40 * 2982414 * 2
def baseEnd_2982414 : Nat := 1020941261798933016806089

theorem tailTrace_2982414 : CollatzResearch.WordTrace tailWord_2982414 prefixEnd_2982414 1020941261798933016806089 := by
  unfold tailWord_2982414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13597196877153863575553287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72518383344820605736284197 13597196877153863575553287)
  ·
    refine ⟨20395795315730795363329931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13597196877153863575553287 20395795315730795363329931)
    ·
      refine ⟨30593692973596193044994897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20395795315730795363329931 30593692973596193044994897)
      ·
        refine ⟨22945269730197144783746173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30593692973596193044994897 22945269730197144783746173)
        ·
          refine ⟨8604476148823929293904815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22945269730197144783746173 8604476148823929293904815)
          ·
            refine ⟨12906714223235893940857223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604476148823929293904815 12906714223235893940857223)
            ·
              refine ⟨19360071334853840911285835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906714223235893940857223 19360071334853840911285835)
              ·
                refine ⟨29040107002280761366928753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19360071334853840911285835 29040107002280761366928753)
                ·
                  refine ⟨21780080251710571025196565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29040107002280761366928753 21780080251710571025196565)
                  ·
                    refine ⟨1020941261798933016806089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21780080251710571025196565 1020941261798933016806089)
                    ·
                      rfl

theorem cell22_2982414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2982414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982414 prefixEnd_2982414 := by exact prefixLift 2982414
  have htrace : WordTrace (prefixWord ++ tailWord_2982414) baseStart_2982414 baseEnd_2982414 := by
    simpa [prefixWord, tailWord_2982414, baseEnd_2982414] using wordTrace_append hprefix tailTrace_2982414
  have hstable : (prefixWord ++ tailWord_2982414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982414).length < 2 ^ (prefixWord ++ tailWord_2982414).sum := by decide
  have hdescent : baseEnd_2982414 < baseStart_2982414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982474 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_2982474 : Nat := 118140960795 + 2982474 * 2 ^ 59
def prefixEnd_2982474 : Nat := 4983230072969 + 3 ^ 40 * 2982474 * 2
def baseEnd_2982474 : Nat := 340320600341704286768635

theorem tailTrace_2982474 : CollatzResearch.WordTrace tailWord_2982474 prefixEnd_2982474 340320600341704286768635 := by
  unfold tailWord_2982474
  simp only [CollatzResearch.WordTrace]
  refine ⟨27194940849253384712902619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72519842264675692567740317 27194940849253384712902619)
  ·
    refine ⟨40792411273880077069353929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27194940849253384712902619 40792411273880077069353929)
    ·
      refine ⟨30594308455410057802015447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40792411273880077069353929 30594308455410057802015447)
      ·
        refine ⟨45891462683115086703023171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30594308455410057802015447 45891462683115086703023171)
        ·
          refine ⟨68837194024672630054534757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45891462683115086703023171 68837194024672630054534757)
          ·
            refine ⟨12906973879626118135225267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68837194024672630054534757 12906973879626118135225267)
            ·
              refine ⟨19360460819439177202837901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906973879626118135225267 19360460819439177202837901)
              ·
                refine ⟨7260172807289691451064213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19360460819439177202837901 7260172807289691451064213)
                ·
                  refine ⟨340320600341704286768635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7260172807289691451064213 340320600341704286768635)
                  ·
                    rfl

theorem cell22_2982474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_2982474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982474 prefixEnd_2982474 := by exact prefixLift 2982474
  have htrace : WordTrace (prefixWord ++ tailWord_2982474) baseStart_2982474 baseEnd_2982474 := by
    simpa [prefixWord, tailWord_2982474, baseEnd_2982474] using wordTrace_append hprefix tailTrace_2982474
  have hstable : (prefixWord ++ tailWord_2982474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982474).length < 2 ^ (prefixWord ++ tailWord_2982474).sum := by decide
  have hdescent : baseEnd_2982474 < baseStart_2982474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982506 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2982506 : Nat := 118140960795 + 2982506 * 2 ^ 59
def prefixEnd_2982506 : Nat := 4983230072969 + 3 ^ 40 * 2982506 * 2
def baseEnd_2982506 : Nat := 1020972755279075443505807

theorem tailTrace_2982506 : CollatzResearch.WordTrace tailWord_2982506 prefixEnd_2982506 1020972755279075443505807 := by
  unfold tailWord_2982506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195232633224402079193843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72520620355265072211183581 27195232633224402079193843)
  ·
    refine ⟨40792848949836603118790765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27195232633224402079193843 40792848949836603118790765)
    ·
      refine ⟨15297318356188726169546537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40792848949836603118790765 15297318356188726169546537)
      ·
        refine ⟨11472988767141544627159903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15297318356188726169546537 11472988767141544627159903)
        ·
          refine ⟨17209483150712316940739855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11472988767141544627159903 17209483150712316940739855)
          ·
            refine ⟨25814224726068475411109783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17209483150712316940739855 25814224726068475411109783)
            ·
              refine ⟨38721337089102713116664675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25814224726068475411109783 38721337089102713116664675)
              ·
                refine ⟨58082005633654069674997013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38721337089102713116664675 58082005633654069674997013)
                ·
                  refine ⟨2722594014077534516015485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58082005633654069674997013 2722594014077534516015485)
                  ·
                    refine ⟨1020972755279075443505807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722594014077534516015485 1020972755279075443505807)
                    ·
                      rfl

theorem cell22_2982506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2982506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982506 prefixEnd_2982506 := by exact prefixLift 2982506
  have htrace : WordTrace (prefixWord ++ tailWord_2982506) baseStart_2982506 baseEnd_2982506 := by
    simpa [prefixWord, tailWord_2982506, baseEnd_2982506] using wordTrace_append hprefix tailTrace_2982506
  have hstable : (prefixWord ++ tailWord_2982506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982506).length < 2 ^ (prefixWord ++ tailWord_2982506).sum := by decide
  have hdescent : baseEnd_2982506 < baseStart_2982506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982521 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_2982521 : Nat := 118140960795 + 2982521 * 2 ^ 59
def prefixEnd_2982521 : Nat := 4983230072969 + 3 ^ 40 * 2982521 * 2
def baseEnd_2982521 : Nat := 1020977890085620404380761

theorem tailTrace_2982521 : CollatzResearch.WordTrace tailWord_2982521 prefixEnd_2982521 1020977890085620404380761 := by
  unfold tailWord_2982521
  simp only [CollatzResearch.WordTrace]
  refine ⟨108781477627843265878571417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72520985085228843919047611 108781477627843265878571417)
  ·
    refine ⟨81586108220882449408928563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108781477627843265878571417 81586108220882449408928563)
    ·
      refine ⟨122379162331323674113392845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81586108220882449408928563 122379162331323674113392845)
      ·
        refine ⟨45892185874246377792522317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122379162331323674113392845 45892185874246377792522317)
        ·
          refine ⟨17209569702842391672195869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45892185874246377792522317 17209569702842391672195869)
          ·
            refine ⟨6453588638565896877073451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17209569702842391672195869 6453588638565896877073451)
            ·
              refine ⟨9680382957848845315610177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453588638565896877073451 9680382957848845315610177)
              ·
                refine ⟨7260287218386633986707633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9680382957848845315610177 7260287218386633986707633)
                ·
                  refine ⟨5445215413789975490030725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7260287218386633986707633 5445215413789975490030725)
                  ·
                    refine ⟨1020977890085620404380761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5445215413789975490030725 1020977890085620404380761)
                    ·
                      rfl

theorem cell22_2982521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_2982521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982521 prefixEnd_2982521 := by exact prefixLift 2982521
  have htrace : WordTrace (prefixWord ++ tailWord_2982521) baseStart_2982521 baseEnd_2982521 := by
    simpa [prefixWord, tailWord_2982521, baseEnd_2982521] using wordTrace_append hprefix tailTrace_2982521
  have hstable : (prefixWord ++ tailWord_2982521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982521).length < 2 ^ (prefixWord ++ tailWord_2982521).sum := by decide
  have hdescent : baseEnd_2982521 < baseStart_2982521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982525 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 4]
def baseStart_2982525 : Nat := 118140960795 + 2982525 * 2 ^ 59
def prefixEnd_2982525 : Nat := 4983230072969 + 3 ^ 40 * 2982525 * 2
def baseEnd_2982525 : Nat := 340326419789121909093583

theorem tailTrace_2982525 : CollatzResearch.WordTrace tailWord_2982525 prefixEnd_2982525 340326419789121909093583 := by
  unfold tailWord_2982525
  simp only [CollatzResearch.WordTrace]
  refine ⟨108781623519828774561717029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72521082346552516374478019 108781623519828774561717029)
  ·
    refine ⟨20396554409967895230321943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108781623519828774561717029 20396554409967895230321943)
    ·
      refine ⟨30594831614951842845482915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20396554409967895230321943 30594831614951842845482915)
      ·
        refine ⟨45892247422427764268224373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30594831614951842845482915 45892247422427764268224373)
        ·
          refine ⟨4302398195852602900146035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45892247422427764268224373 4302398195852602900146035)
          ·
            refine ⟨6453597293778904350219053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302398195852602900146035 6453597293778904350219053)
            ·
              refine ⟨2420098985167089131332145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6453597293778904350219053 2420098985167089131332145)
              ·
                refine ⟨1815074238875316848499109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420098985167089131332145 1815074238875316848499109)
                ·
                  refine ⟨340326419789121909093583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815074238875316848499109 340326419789121909093583)
                  ·
                    rfl

theorem cell22_2982525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_2982525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982525 prefixEnd_2982525 := by exact prefixLift 2982525
  have htrace : WordTrace (prefixWord ++ tailWord_2982525) baseStart_2982525 baseEnd_2982525 := by
    simpa [prefixWord, tailWord_2982525, baseEnd_2982525] using wordTrace_append hprefix tailTrace_2982525
  have hstable : (prefixWord ++ tailWord_2982525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982525).length < 2 ^ (prefixWord ++ tailWord_2982525).sum := by decide
  have hdescent : baseEnd_2982525 < baseStart_2982525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982551 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 5, 3]
def baseStart_2982551 : Nat := 118140960795 + 2982551 * 2 ^ 59
def prefixEnd_2982551 : Nat := 4983230072969 + 3 ^ 40 * 2982551 * 2
def baseEnd_2982551 : Nat := 1020988159698710326130669

theorem tailTrace_2982551 : CollatzResearch.WordTrace tailWord_2982551 prefixEnd_2982551 1020988159698710326130669 := by
  unfold tailWord_2982551
  simp only [CollatzResearch.WordTrace]
  refine ⟨108782571817734581002163507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72521714545156387334775671 108782571817734581002163507)
  ·
    refine ⟨163173857726601871503245261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108782571817734581002163507 163173857726601871503245261)
    ·
      refine ⟨61190196647475701813716973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163173857726601871503245261 61190196647475701813716973)
      ·
        refine ⟨22946323742803388180143865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61190196647475701813716973 22946323742803388180143865)
        ·
          refine ⟨17209742807102541135107899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22946323742803388180143865 17209742807102541135107899)
          ·
            refine ⟨25814614210653811702661849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17209742807102541135107899 25814614210653811702661849)
            ·
              refine ⟨19360960657990358776996387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25814614210653811702661849 19360960657990358776996387)
              ·
                refine ⟨29041440986985538165494581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19360960657990358776996387 29041440986985538165494581)
                ·
                  refine ⟨2722635092529894203015117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29041440986985538165494581 2722635092529894203015117)
                  ·
                    refine ⟨1020988159698710326130669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722635092529894203015117 1020988159698710326130669)
                    ·
                      rfl

theorem cell22_2982551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_2982551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982551 prefixEnd_2982551 := by exact prefixLift 2982551
  have htrace : WordTrace (prefixWord ++ tailWord_2982551) baseStart_2982551 baseEnd_2982551 := by
    simpa [prefixWord, tailWord_2982551, baseEnd_2982551] using wordTrace_append hprefix tailTrace_2982551
  have hstable : (prefixWord ++ tailWord_2982551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982551).length < 2 ^ (prefixWord ++ tailWord_2982551).sum := by decide
  have hdescent : baseEnd_2982551 < baseStart_2982551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982596 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2982596 : Nat := 118140960795 + 2982596 * 2 ^ 59
def prefixEnd_2982596 : Nat := 4983230072969 + 3 ^ 40 * 2982596 * 2
def baseEnd_2982596 : Nat := 1021003564118345208755531

theorem tailTrace_2982596 : CollatzResearch.WordTrace tailWord_2982596 prefixEnd_2982596 1021003564118345208755531 := by
  unfold tailWord_2982596
  simp only [CollatzResearch.WordTrace]
  refine ⟨54392106551285776843775821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72522808735047702458367761 54392106551285776843775821)
  ·
    refine ⟨20397039956732166316415933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54392106551285776843775821 20397039956732166316415933)
    ·
      refine ⟨7648889983774562368655975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20397039956732166316415933 7648889983774562368655975)
      ·
        refine ⟨11473334975661843552983963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7648889983774562368655975 11473334975661843552983963)
        ·
          refine ⟨17210002463492765329475945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11473334975661843552983963 17210002463492765329475945)
          ·
            refine ⟨12907501847619573997106959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17210002463492765329475945 12907501847619573997106959)
            ·
              refine ⟨19361252771429360995660439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12907501847619573997106959 19361252771429360995660439)
              ·
                refine ⟨29041879157144041493490659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19361252771429360995660439 29041879157144041493490659)
                ·
                  refine ⟨43562818735716062240235989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29041879157144041493490659 43562818735716062240235989)
                  ·
                    refine ⟨1021003564118345208755531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43562818735716062240235989 1021003564118345208755531)
                    ·
                      rfl

theorem cell22_2982596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2982596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982596 prefixEnd_2982596 := by exact prefixLift 2982596
  have htrace : WordTrace (prefixWord ++ tailWord_2982596) baseStart_2982596 baseEnd_2982596 := by
    simpa [prefixWord, tailWord_2982596, baseEnd_2982596] using wordTrace_append hprefix tailTrace_2982596
  have hstable : (prefixWord ++ tailWord_2982596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982596).length < 2 ^ (prefixWord ++ tailWord_2982596).sum := by decide
  have hdescent : baseEnd_2982596 < baseStart_2982596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982628 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_2982628 : Nat := 118140960795 + 2982628 * 2 ^ 59
def prefixEnd_2982628 : Nat := 4983230072969 + 3 ^ 40 * 2982628 * 2
def baseEnd_2982628 : Nat := 1021014518372307791955433

theorem tailTrace_2982628 : CollatzResearch.WordTrace tailWord_2982628 prefixEnd_2982628 1021014518372307791955433 := by
  unfold tailWord_2982628
  simp only [CollatzResearch.WordTrace]
  refine ⟨54392690119227811576358269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72523586825637082101811025 54392690119227811576358269)
  ·
    refine ⟨20397258794710429341134351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54392690119227811576358269 20397258794710429341134351)
    ·
      refine ⟨30595888192065644011701527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20397258794710429341134351 30595888192065644011701527)
      ·
        refine ⟨45893832288098466017552291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30595888192065644011701527 45893832288098466017552291)
        ·
          refine ⟨68840748432147699026328437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45893832288098466017552291 68840748432147699026328437)
          ·
            refine ⟨6453820165513846783718291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68840748432147699026328437 6453820165513846783718291)
            ·
              refine ⟨9680730248270770175577437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453820165513846783718291 9680730248270770175577437)
              ·
                refine ⟨3630273843101538815841539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9680730248270770175577437 3630273843101538815841539)
                ·
                  refine ⟨5445410764652308223762309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630273843101538815841539 5445410764652308223762309)
                  ·
                    refine ⟨1021014518372307791955433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5445410764652308223762309 1021014518372307791955433)
                    ·
                      rfl

theorem cell22_2982628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_2982628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982628 prefixEnd_2982628 := by exact prefixLift 2982628
  have htrace : WordTrace (prefixWord ++ tailWord_2982628) baseStart_2982628 baseEnd_2982628 := by
    simpa [prefixWord, tailWord_2982628, baseEnd_2982628] using wordTrace_append hprefix tailTrace_2982628
  have hstable : (prefixWord ++ tailWord_2982628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982628).length < 2 ^ (prefixWord ++ tailWord_2982628).sum := by decide
  have hdescent : baseEnd_2982628 < baseStart_2982628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982754 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2982754 : Nat := 118140960795 + 2982754 * 2 ^ 59
def prefixEnd_2982754 : Nat := 4983230072969 + 3 ^ 40 * 2982754 * 2
def baseEnd_2982754 : Nat := 1021057650747285463305047

theorem tailTrace_2982754 : CollatzResearch.WordTrace tailWord_2982754 prefixEnd_2982754 1021057650747285463305047 := by
  unfold tailWord_2982754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27197493958999786667950829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72526650557332764447868877 27197493958999786667950829)
  ·
    refine ⟨10199060234624920000481561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27197493958999786667950829 10199060234624920000481561)
    ·
      refine ⟨7649295175968690000361171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10199060234624920000481561 7649295175968690000361171)
      ·
        refine ⟨11473942763953035000541757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649295175968690000361171 11473942763953035000541757)
        ·
          refine ⟨4302728536482388125203159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11473942763953035000541757 4302728536482388125203159)
          ·
            refine ⟨6454092804723582187804739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302728536482388125203159 6454092804723582187804739)
            ·
              refine ⟨9681139207085373281707109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454092804723582187804739 9681139207085373281707109)
              ·
                refine ⟨1815213601328507490320083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9681139207085373281707109 1815213601328507490320083)
                ·
                  refine ⟨2722820401992761235480125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815213601328507490320083 2722820401992761235480125)
                  ·
                    refine ⟨1021057650747285463305047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722820401992761235480125 1021057650747285463305047)
                    ·
                      rfl

theorem cell22_2982754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2982754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982754 prefixEnd_2982754 := by exact prefixLift 2982754
  have htrace : WordTrace (prefixWord ++ tailWord_2982754) baseStart_2982754 baseEnd_2982754 := by
    simpa [prefixWord, tailWord_2982754, baseEnd_2982754] using wordTrace_append hprefix tailTrace_2982754
  have hstable : (prefixWord ++ tailWord_2982754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982754).length < 2 ^ (prefixWord ++ tailWord_2982754).sum := by decide
  have hdescent : baseEnd_2982754 < baseStart_2982754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982793 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_2982793 : Nat := 118140960795 + 2982793 * 2 ^ 59
def prefixEnd_2982793 : Nat := 4983230072969 + 3 ^ 40 * 2982793 * 2
def baseEnd_2982793 : Nat := 1021071001244302361579927

theorem tailTrace_2982793 : CollatzResearch.WordTrace tailWord_2982793 prefixEnd_2982793 1021071001244302361579927 := by
  unfold tailWord_2982793
  simp only [CollatzResearch.WordTrace]
  refine ⟨108791398282857856332473033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72527598855238570888315355 108791398282857856332473033)
  ·
    refine ⟨81593548712143392249354775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108791398282857856332473033 81593548712143392249354775)
    ·
      refine ⟨122390323068215088374032163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81593548712143392249354775 122390323068215088374032163)
      ·
        refine ⟨183585484602322632561048245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122390323068215088374032163 183585484602322632561048245)
        ·
          refine ⟨17211139181467746802598273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183585484602322632561048245 17211139181467746802598273)
          ·
            refine ⟨12908354386100810101948705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17211139181467746802598273 12908354386100810101948705)
            ·
              refine ⟨9681265789575607576461529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12908354386100810101948705 9681265789575607576461529)
              ·
                refine ⟨7260949342181705682346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9681265789575607576461529 7260949342181705682346147)
                ·
                  refine ⟨10891424013272558523519221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260949342181705682346147 10891424013272558523519221)
                  ·
                    refine ⟨1021071001244302361579927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10891424013272558523519221 1021071001244302361579927)
                    ·
                      rfl

theorem cell22_2982793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_2982793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982793 prefixEnd_2982793 := by exact prefixLift 2982793
  have htrace : WordTrace (prefixWord ++ tailWord_2982793) baseStart_2982793 baseEnd_2982793 := by
    simpa [prefixWord, tailWord_2982793, baseEnd_2982793] using wordTrace_append hprefix tailTrace_2982793
  have hstable : (prefixWord ++ tailWord_2982793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982793).length < 2 ^ (prefixWord ++ tailWord_2982793).sum := by decide
  have hdescent : baseEnd_2982793 < baseStart_2982793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982840 : List Nat := [2, 1, 2, 1, 2, 6, 2, 6]
def baseStart_2982840 : Nat := 118140960795 + 2982840 * 2 ^ 59
def prefixEnd_2982840 : Nat := 4983230072969 + 3 ^ 40 * 2982840 * 2
def baseEnd_2982840 : Nat := 113454121144978878406087

theorem tailTrace_2982840 : CollatzResearch.WordTrace tailWord_2982840 prefixEnd_2982840 113454121144978878406087 := by
  unfold tailWord_2982840
  simp only [CollatzResearch.WordTrace]
  refine ⟨54396556256843791679716987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72528741675791722239622649 54396556256843791679716987)
  ·
    refine ⟨81594834385265687519575481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54396556256843791679716987 81594834385265687519575481)
    ·
      refine ⟨61196125788949265639681611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81594834385265687519575481 61196125788949265639681611)
      ·
        refine ⟨91794188683423898459522417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61196125788949265639681611 91794188683423898459522417)
        ·
          refine ⟨68845641512567923844641813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91794188683423898459522417 68845641512567923844641813)
          ·
            refine ⟨3227139445901621430217585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68845641512567923844641813 3227139445901621430217585)
            ·
              refine ⟨2420354584426216072663189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227139445901621430217585 2420354584426216072663189)
              ·
                refine ⟨113454121144978878406087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2420354584426216072663189 113454121144978878406087)
                ·
                  rfl

theorem cell22_2982840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_2982840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982840 prefixEnd_2982840 := by exact prefixLift 2982840
  have htrace : WordTrace (prefixWord ++ tailWord_2982840) baseStart_2982840 baseEnd_2982840 := by
    simpa [prefixWord, tailWord_2982840, baseEnd_2982840] using wordTrace_append hprefix tailTrace_2982840
  have hstable : (prefixWord ++ tailWord_2982840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982840).length < 2 ^ (prefixWord ++ tailWord_2982840).sum := by decide
  have hdescent : baseEnd_2982840 < baseStart_2982840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982872 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_2982872 : Nat := 118140960795 + 2982872 * 2 ^ 59
def prefixEnd_2982872 : Nat := 4983230072969 + 3 ^ 40 * 2982872 * 2
def baseEnd_2982872 : Nat := 1021098044558772488854685

theorem tailTrace_2982872 : CollatzResearch.WordTrace tailWord_2982872 prefixEnd_2982872 1021098044558772488854685 := by
  unfold tailWord_2982872
  simp only [CollatzResearch.WordTrace]
  refine ⟨54397139824785826412299435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72529519766381101883065913 54397139824785826412299435)
  ·
    refine ⟨81595709737178739618449153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54397139824785826412299435 81595709737178739618449153)
    ·
      refine ⟨61196782302884054713836865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81595709737178739618449153 61196782302884054713836865)
      ·
        refine ⟨45897586727163041035377649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61196782302884054713836865 45897586727163041035377649)
        ·
          refine ⟨34423190045372280776533237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45897586727163041035377649 34423190045372280776533237)
          ·
            refine ⟨3227174066753651322799991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34423190045372280776533237 3227174066753651322799991)
            ·
              refine ⟨4840761100130476984199987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227174066753651322799991 4840761100130476984199987)
              ·
                refine ⟨7261141650195715476299981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840761100130476984199987 7261141650195715476299981)
                ·
                  refine ⟨2722928118823393303612493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7261141650195715476299981 2722928118823393303612493)
                  ·
                    refine ⟨1021098044558772488854685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722928118823393303612493 1021098044558772488854685)
                    ·
                      rfl

theorem cell22_2982872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_2982872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982872 prefixEnd_2982872 := by exact prefixLift 2982872
  have htrace : WordTrace (prefixWord ++ tailWord_2982872) baseStart_2982872 baseEnd_2982872 := by
    simpa [prefixWord, tailWord_2982872, baseEnd_2982872] using wordTrace_append hprefix tailTrace_2982872
  have hstable : (prefixWord ++ tailWord_2982872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982872).length < 2 ^ (prefixWord ++ tailWord_2982872).sum := by decide
  have hdescent : baseEnd_2982872 < baseStart_2982872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982883 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_2982883 : Nat := 118140960795 + 2982883 * 2 ^ 59
def prefixEnd_2982883 : Nat := 4983230072969 + 3 ^ 40 * 2982883 * 2
def baseEnd_2982883 : Nat := 1021101810083572126829651

theorem tailTrace_2982883 : CollatzResearch.WordTrace tailWord_2982883 prefixEnd_2982883 1021101810083572126829651 := by
  unfold tailWord_2982883
  simp only [CollatzResearch.WordTrace]
  refine ⟨108794680852531801703249303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72529787235021201135499535 108794680852531801703249303)
  ·
    refine ⟨163192021278797702554873955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108794680852531801703249303 163192021278797702554873955)
    ·
      refine ⟨244788031918196553832310933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163192021278797702554873955 244788031918196553832310933)
      ·
        refine ⟨11474438996165463460889575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244788031918196553832310933 11474438996165463460889575)
        ·
          refine ⟨17211658494248195191334363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11474438996165463460889575 17211658494248195191334363)
          ·
            refine ⟨25817487741372292787001545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17211658494248195191334363 25817487741372292787001545)
            ·
              refine ⟨19363115806029219590251159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25817487741372292787001545 19363115806029219590251159)
              ·
                refine ⟨29044673709043829385376739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19363115806029219590251159 29044673709043829385376739)
                ·
                  refine ⟨43567010563565744078065109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29044673709043829385376739 43567010563565744078065109)
                  ·
                    refine ⟨1021101810083572126829651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43567010563565744078065109 1021101810083572126829651)
                    ·
                      rfl

theorem cell22_2982883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_2982883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982883 prefixEnd_2982883 := by exact prefixLift 2982883
  have htrace : WordTrace (prefixWord ++ tailWord_2982883) baseStart_2982883 baseEnd_2982883 := by
    simpa [prefixWord, tailWord_2982883, baseEnd_2982883] using wordTrace_append hprefix tailTrace_2982883
  have hstable : (prefixWord ++ tailWord_2982883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982883).length < 2 ^ (prefixWord ++ tailWord_2982883).sum := by decide
  have hdescent : baseEnd_2982883 < baseStart_2982883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982945 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2982945 : Nat := 118140960795 + 2982945 * 2 ^ 59
def prefixEnd_2982945 : Nat := 4983230072969 + 3 ^ 40 * 2982945 * 2
def baseEnd_2982945 : Nat := 1021123033950624631779461

theorem tailTrace_2982945 : CollatzResearch.WordTrace tailWord_2982945 prefixEnd_2982945 1021123033950624631779461 := by
  unfold tailWord_2982945
  simp only [CollatzResearch.WordTrace]
  refine ⟨108796942178307186292006289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72531294785538124194670859 108796942178307186292006289)
  ·
    refine ⟨81597706633730389719004717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108796942178307186292006289 81597706633730389719004717)
    ·
      refine ⟨30599139987648896144626769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81597706633730389719004717 30599139987648896144626769)
      ·
        refine ⟨22949354990736672108470077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30599139987648896144626769 22949354990736672108470077)
        ·
          refine ⟨8606008121526252040676279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22949354990736672108470077 8606008121526252040676279)
          ·
            refine ⟨12909012182289378061014419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606008121526252040676279 12909012182289378061014419)
            ·
              refine ⟨19363518273434067091521629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12909012182289378061014419 19363518273434067091521629)
              ·
                refine ⟨7261319352537775159320611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19363518273434067091521629 7261319352537775159320611)
                ·
                  refine ⟨10891979028806662738980917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7261319352537775159320611 10891979028806662738980917)
                  ·
                    refine ⟨1021123033950624631779461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10891979028806662738980917 1021123033950624631779461)
                    ·
                      rfl

theorem cell22_2982945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2982945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982945 prefixEnd_2982945 := by exact prefixLift 2982945
  have htrace : WordTrace (prefixWord ++ tailWord_2982945) baseStart_2982945 baseEnd_2982945 := by
    simpa [prefixWord, tailWord_2982945, baseEnd_2982945] using wordTrace_append hprefix tailTrace_2982945
  have hstable : (prefixWord ++ tailWord_2982945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982945).length < 2 ^ (prefixWord ++ tailWord_2982945).sum := by decide
  have hdescent : baseEnd_2982945 < baseStart_2982945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982964 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2982964 : Nat := 118140960795 + 2982964 * 2 ^ 59
def prefixEnd_2982964 : Nat := 4983230072969 + 3 ^ 40 * 2982964 * 2
def baseEnd_2982964 : Nat := 340376512679638305184801

theorem tailTrace_2982964 : CollatzResearch.WordTrace tailWord_2982964 prefixEnd_2982964 340376512679638305184801 := by
  unfold tailWord_2982964
  simp only [CollatzResearch.WordTrace]
  refine ⟨54398817582619176268473973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72531756776825568357965297 54398817582619176268473973)
  ·
    refine ⟨5099889148370547775169435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54398817582619176268473973 5099889148370547775169435)
    ·
      refine ⟨7649833722555821662754153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5099889148370547775169435 7649833722555821662754153)
      ·
        refine ⟨5737375291916866247065615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7649833722555821662754153 5737375291916866247065615)
        ·
          refine ⟨8606062937875299370598423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737375291916866247065615 8606062937875299370598423)
          ·
            refine ⟨12909094406812949055897635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606062937875299370598423 12909094406812949055897635)
            ·
              refine ⟨19363641610219423583846453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12909094406812949055897635 19363641610219423583846453)
              ·
                refine ⟨1815341400958070960985605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19363641610219423583846453 1815341400958070960985605)
                ·
                  refine ⟨340376512679638305184801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815341400958070960985605 340376512679638305184801)
                  ·
                    rfl

theorem cell22_2982964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2982964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982964 prefixEnd_2982964 := by exact prefixLift 2982964
  have htrace : WordTrace (prefixWord ++ tailWord_2982964) baseStart_2982964 baseEnd_2982964 := by
    simpa [prefixWord, tailWord_2982964, baseEnd_2982964] using wordTrace_append hprefix tailTrace_2982964
  have hstable : (prefixWord ++ tailWord_2982964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982964).length < 2 ^ (prefixWord ++ tailWord_2982964).sum := by decide
  have hdescent : baseEnd_2982964 < baseStart_2982964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982966 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_2982966 : Nat := 118140960795 + 2982966 * 2 ^ 59
def prefixEnd_2982966 : Nat := 4983230072969 + 3 ^ 40 * 2982966 * 2
def baseEnd_2982966 : Nat := 1021130222679787577004397

theorem tailTrace_2982966 : CollatzResearch.WordTrace tailWord_2982966 prefixEnd_2982966 1021130222679787577004397 := by
  unfold tailWord_2982966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799856756951944179907547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72531805407487404585680501 6799856756951944179907547)
  ·
    refine ⟨10199785135427916269861321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6799856756951944179907547 10199785135427916269861321)
    ·
      refine ⟨7649838851570937202395991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10199785135427916269861321 7649838851570937202395991)
      ·
        refine ⟨11474758277356405803593987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649838851570937202395991 11474758277356405803593987)
        ·
          refine ⟨17212137416034608705390981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11474758277356405803593987 17212137416034608705390981)
          ·
            refine ⟨3227275765506489132260809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17212137416034608705390981 3227275765506489132260809)
            ·
              refine ⟨2420456824129866849195607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227275765506489132260809 2420456824129866849195607)
              ·
                refine ⟨3630685236194800273793411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420456824129866849195607 3630685236194800273793411)
                ·
                  refine ⟨5446027854292200410690117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630685236194800273793411 5446027854292200410690117)
                  ·
                    refine ⟨1021130222679787577004397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446027854292200410690117 1021130222679787577004397)
                    ·
                      rfl

theorem cell22_2982966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_2982966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2982966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2982966 prefixEnd_2982966 := by exact prefixLift 2982966
  have htrace : WordTrace (prefixWord ++ tailWord_2982966) baseStart_2982966 baseEnd_2982966 := by
    simpa [prefixWord, tailWord_2982966, baseEnd_2982966] using wordTrace_append hprefix tailTrace_2982966
  have hstable : (prefixWord ++ tailWord_2982966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982966).length < 2 ^ (prefixWord ++ tailWord_2982966).sum := by decide
  have hdescent : baseEnd_2982966 < baseStart_2982966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983054 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_2983054 : Nat := 118140960795 + 2983054 * 2 ^ 59
def prefixEnd_2983054 : Nat := 4983230072969 + 3 ^ 40 * 2983054 * 2
def baseEnd_2983054 : Nat := 340386782292728226934709

theorem tailTrace_2983054 : CollatzResearch.WordTrace tailWord_2983054 prefixEnd_2983054 340386782292728226934709 := by
  unfold tailWord_2983054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13600114716864037238465527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72533945156608198605149477 13600114716864037238465527)
  ·
    refine ⟨20400172075296055857698291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13600114716864037238465527 20400172075296055857698291)
    ·
      refine ⟨30600258112944083786547437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20400172075296055857698291 30600258112944083786547437)
      ·
        refine ⟨11475096792354031419955289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30600258112944083786547437 11475096792354031419955289)
        ·
          refine ⟨8606322594265523564966467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11475096792354031419955289 8606322594265523564966467)
          ·
            refine ⟨12909483891398285347449701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606322594265523564966467 12909483891398285347449701)
            ·
              refine ⟨2420528229637178502646819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12909483891398285347449701 2420528229637178502646819)
              ·
                refine ⟨3630792344455767753970229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420528229637178502646819 3630792344455767753970229)
                ·
                  refine ⟨340386782292728226934709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3630792344455767753970229 340386782292728226934709)
                  ·
                    rfl

theorem cell22_2983054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_2983054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983054 prefixEnd_2983054 := by exact prefixLift 2983054
  have htrace : WordTrace (prefixWord ++ tailWord_2983054) baseStart_2983054 baseEnd_2983054 := by
    simpa [prefixWord, tailWord_2983054, baseEnd_2983054] using wordTrace_append hprefix tailTrace_2983054
  have hstable : (prefixWord ++ tailWord_2983054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983054).length < 2 ^ (prefixWord ++ tailWord_2983054).sum := by decide
  have hdescent : baseEnd_2983054 < baseStart_2983054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983114 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_2983114 : Nat := 118140960795 + 2983114 * 2 ^ 59
def prefixEnd_2983114 : Nat := 4983230072969 + 3 ^ 40 * 2983114 * 2
def baseEnd_2983114 : Nat := 1021180886104364524303943

theorem tailTrace_2983114 : CollatzResearch.WordTrace tailWord_2983114 prefixEnd_2983114 1021180886104364524303943 := by
  unfold tailWord_2983114
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200776528673732038727099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72535404076463285436605597 27200776528673732038727099)
  ·
    refine ⟨40801164793010598058090649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27200776528673732038727099 40801164793010598058090649)
    ·
      refine ⟨30600873594757948543567987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40801164793010598058090649 30600873594757948543567987)
      ·
        refine ⟨45901310392136922815351981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30600873594757948543567987 45901310392136922815351981)
        ·
          refine ⟨17212991397051346055756993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45901310392136922815351981 17212991397051346055756993)
          ·
            refine ⟨12909743547788509541817745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17212991397051346055756993 12909743547788509541817745)
            ·
              refine ⟨9682307660841382156363309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12909743547788509541817745 9682307660841382156363309)
              ·
                refine ⟨3630865372815518308636241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9682307660841382156363309 3630865372815518308636241)
                ·
                  refine ⟨2723149029611638731477181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630865372815518308636241 2723149029611638731477181)
                  ·
                    refine ⟨1021180886104364524303943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723149029611638731477181 1021180886104364524303943)
                    ·
                      rfl

theorem cell22_2983114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_2983114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983114 prefixEnd_2983114 := by exact prefixLift 2983114
  have htrace : WordTrace (prefixWord ++ tailWord_2983114) baseStart_2983114 baseEnd_2983114 := by
    simpa [prefixWord, tailWord_2983114, baseEnd_2983114] using wordTrace_append hprefix tailTrace_2983114
  have hstable : (prefixWord ++ tailWord_2983114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983114).length < 2 ^ (prefixWord ++ tailWord_2983114).sum := by decide
  have hdescent : baseEnd_2983114 < baseStart_2983114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983210 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2983210 : Nat := 118140960795 + 2983210 * 2 ^ 59
def prefixEnd_2983210 : Nat := 4983230072969 + 3 ^ 40 * 2983210 * 2
def baseEnd_2983210 : Nat := 1021213748866252273903649

theorem tailTrace_2983210 : CollatzResearch.WordTrace tailWord_2983210 prefixEnd_2983210 1021213748866252273903649 := by
  unfold tailWord_2983210
  simp only [CollatzResearch.WordTrace]
  refine ⟨27201651880586784137600771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72537738348231424366935389 27201651880586784137600771)
  ·
    refine ⟨40802477820880176206401157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27201651880586784137600771 40802477820880176206401157)
    ·
      refine ⟨7650464591415033038700217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40802477820880176206401157 7650464591415033038700217)
      ·
        refine ⟨5737848443561274779025163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7650464591415033038700217 5737848443561274779025163)
        ·
          refine ⟨8606772665341912168537745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737848443561274779025163 8606772665341912168537745)
          ·
            refine ⟨6455079499006434126403309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8606772665341912168537745 6455079499006434126403309)
            ·
              refine ⟨2420654812127412797401241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6455079499006434126403309 2420654812127412797401241)
              ·
                refine ⟨1815491109095559598050931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420654812127412797401241 1815491109095559598050931)
                ·
                  refine ⟨2723236663643339397076397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815491109095559598050931 2723236663643339397076397)
                  ·
                    refine ⟨1021213748866252273903649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723236663643339397076397 1021213748866252273903649)
                    ·
                      rfl

theorem cell22_2983210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2983210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983210 prefixEnd_2983210 := by exact prefixLift 2983210
  have htrace : WordTrace (prefixWord ++ tailWord_2983210) baseStart_2983210 baseEnd_2983210 := by
    simpa [prefixWord, tailWord_2983210, baseEnd_2983210] using wordTrace_append hprefix tailTrace_2983210
  have hstable : (prefixWord ++ tailWord_2983210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983210).length < 2 ^ (prefixWord ++ tailWord_2983210).sum := by decide
  have hdescent : baseEnd_2983210 < baseStart_2983210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983232 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_2983232 : Nat := 118140960795 + 2983232 * 2 ^ 59
def prefixEnd_2983232 : Nat := 4983230072969 + 3 ^ 40 * 2983232 * 2
def baseEnd_2983232 : Nat := 1021221279915851549853581

theorem tailTrace_2983232 : CollatzResearch.WordTrace tailWord_2983232 prefixEnd_2983232 1021221279915851549853581 := by
  unfold tailWord_2983232
  simp only [CollatzResearch.WordTrace]
  refine ⟨54403704964133717153851975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72538273285511622871802633 54403704964133717153851975)
  ·
    refine ⟨81605557446200575730777963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54403704964133717153851975 81605557446200575730777963)
    ·
      refine ⟨122408336169300863596166945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81605557446200575730777963 122408336169300863596166945)
      ·
        refine ⟨91806252126975647697125209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122408336169300863596166945 91806252126975647697125209)
        ·
          refine ⟨68854689095231735772843907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91806252126975647697125209 68854689095231735772843907)
          ·
            refine ⟨103282033642847603659265861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68854689095231735772843907 103282033642847603659265861)
            ·
              refine ⟨19365381308033925686112349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103282033642847603659265861 19365381308033925686112349)
              ·
                refine ⟨7262017990512722132292131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19365381308033925686112349 7262017990512722132292131)
                ·
                  refine ⟨10893026985769083198438197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262017990512722132292131 10893026985769083198438197)
                  ·
                    refine ⟨1021221279915851549853581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10893026985769083198438197 1021221279915851549853581)
                    ·
                      rfl

theorem cell22_2983232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_2983232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983232 prefixEnd_2983232 := by exact prefixLift 2983232
  have htrace : WordTrace (prefixWord ++ tailWord_2983232) baseStart_2983232 baseEnd_2983232 := by
    simpa [prefixWord, tailWord_2983232, baseEnd_2983232] using wordTrace_append hprefix tailTrace_2983232
  have hstable : (prefixWord ++ tailWord_2983232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983232).length < 2 ^ (prefixWord ++ tailWord_2983232).sum := by decide
  have hdescent : baseEnd_2983232 < baseStart_2983232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983236 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2983236 : Nat := 118140960795 + 2983236 * 2 ^ 59
def prefixEnd_2983236 : Nat := 4983230072969 + 3 ^ 40 * 2983236 * 2
def baseEnd_2983236 : Nat := 1021222649197596872753569

theorem tailTrace_2983236 : CollatzResearch.WordTrace tailWord_2983236 prefixEnd_2983236 1021222649197596872753569 := by
  unfold tailWord_2983236
  simp only [CollatzResearch.WordTrace]
  refine ⟨54403777910126471495424781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72538370546835295327233041 54403777910126471495424781)
  ·
    refine ⟨20401416716297426810784293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54403777910126471495424781 20401416716297426810784293)
    ·
      refine ⟨3825265634305767527022055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20401416716297426810784293 3825265634305767527022055)
      ·
        refine ⟨5737898451458651290533083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825265634305767527022055 5737898451458651290533083)
        ·
          refine ⟨8606847677187976935799625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737898451458651290533083 8606847677187976935799625)
          ·
            refine ⟨6455135757890982701849719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8606847677187976935799625 6455135757890982701849719)
            ·
              refine ⟨9682703636836474052774579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455135757890982701849719 9682703636836474052774579)
              ·
                refine ⟨14524055455254711079161869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9682703636836474052774579 14524055455254711079161869)
                ·
                  refine ⟨5446520795720516654685701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14524055455254711079161869 5446520795720516654685701)
                  ·
                    refine ⟨1021222649197596872753569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446520795720516654685701 1021222649197596872753569)
                    ·
                      rfl

theorem cell22_2983236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2983236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983236 prefixEnd_2983236 := by exact prefixLift 2983236
  have htrace : WordTrace (prefixWord ++ tailWord_2983236) baseStart_2983236 baseEnd_2983236 := by
    simpa [prefixWord, tailWord_2983236, baseEnd_2983236] using wordTrace_append hprefix tailTrace_2983236
  have hstable : (prefixWord ++ tailWord_2983236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983236).length < 2 ^ (prefixWord ++ tailWord_2983236).sum := by decide
  have hdescent : baseEnd_2983236 < baseStart_2983236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983261 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2983261 : Nat := 118140960795 + 2983261 * 2 ^ 59
def prefixEnd_2983261 : Nat := 4983230072969 + 3 ^ 40 * 2983261 * 2
def baseEnd_2983261 : Nat := 1021231207208505140878493

theorem tailTrace_2983261 : CollatzResearch.WordTrace tailWord_2983261 prefixEnd_2983261 1021231207208505140878493 := by
  unfold tailWord_2983261
  simp only [CollatzResearch.WordTrace]
  refine ⟨108808467645162372260509637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72538978430108248173673091 108808467645162372260509637)
  ·
    refine ⟨20401587683467944798845557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108808467645162372260509637 20401587683467944798845557)
    ·
      refine ⟨1912648845325119824891771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20401587683467944798845557 1912648845325119824891771)
      ·
        refine ⟨2868973267987679737337657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912648845325119824891771 2868973267987679737337657)
        ·
          refine ⟨2151729950990759803003243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868973267987679737337657 2151729950990759803003243)
          ·
            refine ⟨3227594926486139704504865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151729950990759803003243 3227594926486139704504865)
            ·
              refine ⟨2420696194864604778378649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227594926486139704504865 2420696194864604778378649)
              ·
                refine ⟨1815522146148453583783987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420696194864604778378649 1815522146148453583783987)
                ·
                  refine ⟨2723283219222680375675981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815522146148453583783987 2723283219222680375675981)
                  ·
                    refine ⟨1021231207208505140878493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723283219222680375675981 1021231207208505140878493)
                    ·
                      rfl

theorem cell22_2983261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2983261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983261 prefixEnd_2983261 := by exact prefixLift 2983261
  have htrace : WordTrace (prefixWord ++ tailWord_2983261) baseStart_2983261 baseEnd_2983261 := by
    simpa [prefixWord, tailWord_2983261, baseEnd_2983261] using wordTrace_append hprefix tailTrace_2983261
  have hstable : (prefixWord ++ tailWord_2983261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983261).length < 2 ^ (prefixWord ++ tailWord_2983261).sum := by decide
  have hdescent : baseEnd_2983261 < baseStart_2983261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983264 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_2983264 : Nat := 118140960795 + 2983264 * 2 ^ 59
def prefixEnd_2983264 : Nat := 4983230072969 + 3 ^ 40 * 2983264 * 2
def baseEnd_2983264 : Nat := 1021232234169814133053483

theorem tailTrace_2983264 : CollatzResearch.WordTrace tailWord_2983264 prefixEnd_2983264 1021232234169814133053483 := by
  unfold tailWord_2983264
  simp only [CollatzResearch.WordTrace]
  refine ⟨54404288532075751886434423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72539051376101002515245897 54404288532075751886434423)
  ·
    refine ⟨81606432798113627829651635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54404288532075751886434423 81606432798113627829651635)
    ·
      refine ⟨122409649197170441744477453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81606432798113627829651635 122409649197170441744477453)
      ·
        refine ⟨45903618448938915654179045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122409649197170441744477453 45903618448938915654179045)
        ·
          refine ⟨8606928459176046685158571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45903618448938915654179045 8606928459176046685158571)
          ·
            refine ⟨12910392688764070027737857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606928459176046685158571 12910392688764070027737857)
            ·
              refine ⟨9682794516573052520803393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12910392688764070027737857 9682794516573052520803393)
              ·
                refine ⟨7262095887429789390602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9682794516573052520803393 7262095887429789390602545)
                ·
                  refine ⟨5446571915572342042951909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7262095887429789390602545 5446571915572342042951909)
                  ·
                    refine ⟨1021232234169814133053483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446571915572342042951909 1021232234169814133053483)
                    ·
                      rfl

theorem cell22_2983264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_2983264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983264 prefixEnd_2983264 := by exact prefixLift 2983264
  have htrace : WordTrace (prefixWord ++ tailWord_2983264) baseStart_2983264 baseEnd_2983264 := by
    simpa [prefixWord, tailWord_2983264, baseEnd_2983264] using wordTrace_append hprefix tailTrace_2983264
  have hstable : (prefixWord ++ tailWord_2983264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983264).length < 2 ^ (prefixWord ++ tailWord_2983264).sum := by decide
  have hdescent : baseEnd_2983264 < baseStart_2983264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983268 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2983268 : Nat := 118140960795 + 2983268 * 2 ^ 59
def prefixEnd_2983268 : Nat := 4983230072969 + 3 ^ 40 * 2983268 * 2
def baseEnd_2983268 : Nat := 340411201150519818651157

theorem tailTrace_2983268 : CollatzResearch.WordTrace tailWord_2983268 prefixEnd_2983268 340411201150519818651157 := by
  unfold tailWord_2983268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54404361478068506228007229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72539148637424674970676305 54404361478068506228007229)
  ·
    refine ⟨20401635554275689835502711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54404361478068506228007229 20401635554275689835502711)
    ·
      refine ⟨30602453331413534753254067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20401635554275689835502711 30602453331413534753254067)
      ·
        refine ⟨45903679997120302129881101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30602453331413534753254067 45903679997120302129881101)
        ·
          refine ⟨17213879998920113298705413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45903679997120302129881101 17213879998920113298705413)
          ·
            refine ⟨3227602499797521243507265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17213879998920113298705413 3227602499797521243507265)
            ·
              refine ⟨2420701874848140932630449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227602499797521243507265 2420701874848140932630449)
              ·
                refine ⟨1815526406136105699472837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420701874848140932630449 1815526406136105699472837)
                ·
                  refine ⟨340411201150519818651157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815526406136105699472837 340411201150519818651157)
                  ·
                    rfl

theorem cell22_2983268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2983268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983268 prefixEnd_2983268 := by exact prefixLift 2983268
  have htrace : WordTrace (prefixWord ++ tailWord_2983268) baseStart_2983268 baseEnd_2983268 := by
    simpa [prefixWord, tailWord_2983268, baseEnd_2983268] using wordTrace_append hprefix tailTrace_2983268
  have hstable : (prefixWord ++ tailWord_2983268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983268).length < 2 ^ (prefixWord ++ tailWord_2983268).sum := by decide
  have hdescent : baseEnd_2983268 < baseStart_2983268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983292 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_2983292 : Nat := 118140960795 + 2983292 * 2 ^ 59
def prefixEnd_2983292 : Nat := 4983230072969 + 3 ^ 40 * 2983292 * 2
def baseEnd_2983292 : Nat := 1021241819142031393353397

theorem tailTrace_2983292 : CollatzResearch.WordTrace tailWord_2983292 prefixEnd_2983292 1021241819142031393353397 := by
  unfold tailWord_2983292
  simp only [CollatzResearch.WordTrace]
  refine ⟨54404799154025032277444065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72539732205366709703258753 54404799154025032277444065)
  ·
    refine ⟨40803599365518774208083049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54404799154025032277444065 40803599365518774208083049)
    ·
      refine ⟨30602699524139080656062287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40803599365518774208083049 30602699524139080656062287)
      ·
        refine ⟨45904049286208620984093431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30602699524139080656062287 45904049286208620984093431)
        ·
          refine ⟨68856073929312931476140147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45904049286208620984093431 68856073929312931476140147)
          ·
            refine ⟨103284110893969397214210221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68856073929312931476140147 103284110893969397214210221)
            ·
              refine ⟨38731541585238523955328833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103284110893969397214210221 38731541585238523955328833)
              ·
                refine ⟨29048656188928892966496625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38731541585238523955328833 29048656188928892966496625)
                ·
                  refine ⟨21786492141696669724872469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29048656188928892966496625 21786492141696669724872469)
                  ·
                    refine ⟨1021241819142031393353397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21786492141696669724872469 1021241819142031393353397)
                    ·
                      rfl

theorem cell22_2983292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_2983292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983292 prefixEnd_2983292 := by exact prefixLift 2983292
  have htrace : WordTrace (prefixWord ++ tailWord_2983292) baseStart_2983292 baseEnd_2983292 := by
    simpa [prefixWord, tailWord_2983292, baseEnd_2983292] using wordTrace_append hprefix tailTrace_2983292
  have hstable : (prefixWord ++ tailWord_2983292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983292).length < 2 ^ (prefixWord ++ tailWord_2983292).sum := by decide
  have hdescent : baseEnd_2983292 < baseStart_2983292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983298 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2983298 : Nat := 118140960795 + 2983298 * 2 ^ 59
def prefixEnd_2983298 : Nat := 4983230072969 + 3 ^ 40 * 2983298 * 2
def baseEnd_2983298 : Nat := 1021243873064649377703379

theorem tailTrace_2983298 : CollatzResearch.WordTrace tailWord_2983298 prefixEnd_2983298 1021243873064649377703379 := by
  unfold tailWord_2983298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27202454286507081894901637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72539878097352218386404365 27202454286507081894901637)
  ·
    refine ⟨5100460178720077855294057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27202454286507081894901637 5100460178720077855294057)
    ·
      refine ⟨3825345134040058391470543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5100460178720077855294057 3825345134040058391470543)
      ·
        refine ⟨5738017701060087587205815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825345134040058391470543 5738017701060087587205815)
        ·
          refine ⟨8607026551590131380808723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738017701060087587205815 8607026551590131380808723)
          ·
            refine ⟨12910539827385197071213085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607026551590131380808723 12910539827385197071213085)
            ·
              refine ⟨4841452435269448901704907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12910539827385197071213085 4841452435269448901704907)
              ·
                refine ⟨7262178652904173352557361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841452435269448901704907 7262178652904173352557361)
                ·
                  refine ⟨5446633989678130014418021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7262178652904173352557361 5446633989678130014418021)
                  ·
                    refine ⟨1021243873064649377703379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446633989678130014418021 1021243873064649377703379)
                    ·
                      rfl

theorem cell22_2983298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2983298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983298 prefixEnd_2983298 := by exact prefixLift 2983298
  have htrace : WordTrace (prefixWord ++ tailWord_2983298) baseStart_2983298 baseEnd_2983298 := by
    simpa [prefixWord, tailWord_2983298, baseEnd_2983298] using wordTrace_append hprefix tailTrace_2983298
  have hstable : (prefixWord ++ tailWord_2983298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983298).length < 2 ^ (prefixWord ++ tailWord_2983298).sum := by decide
  have hdescent : baseEnd_2983298 < baseStart_2983298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983307 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 7]
def baseStart_2983307 : Nat := 118140960795 + 2983307 * 2 ^ 59
def prefixEnd_2983307 : Nat := 4983230072969 + 3 ^ 40 * 2983307 * 2
def baseEnd_2983307 : Nat := 340415651316192118076117

theorem tailTrace_2983307 : CollatzResearch.WordTrace tailWord_2983307 prefixEnd_2983307 340415651316192118076117 := by
  unfold tailWord_2983307
  simp only [CollatzResearch.WordTrace]
  refine ⟨108810145402995722116684175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72540096935330481411122783 108810145402995722116684175)
  ·
    refine ⟨163215218104493583175026263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108810145402995722116684175 163215218104493583175026263)
    ·
      refine ⟨244822827156740374762539395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163215218104493583175026263 244822827156740374762539395)
      ·
        refine ⟨367234240735110562143809093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244822827156740374762539395 367234240735110562143809093)
        ·
          refine ⟨68856420137833230401964205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367234240735110562143809093 68856420137833230401964205)
          ·
            refine ⟨25821157551687461400736577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68856420137833230401964205 25821157551687461400736577)
            ·
              refine ⟨19365868163765596050552433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25821157551687461400736577 19365868163765596050552433)
              ·
                refine ⟨14524401122824197037914325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19365868163765596050552433 14524401122824197037914325)
                ·
                  refine ⟨340415651316192118076117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14524401122824197037914325 340415651316192118076117)
                  ·
                    rfl

theorem cell22_2983307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_2983307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983307 prefixEnd_2983307 := by exact prefixLift 2983307
  have htrace : WordTrace (prefixWord ++ tailWord_2983307) baseStart_2983307 baseEnd_2983307 := by
    simpa [prefixWord, tailWord_2983307, baseEnd_2983307] using wordTrace_append hprefix tailTrace_2983307
  have hstable : (prefixWord ++ tailWord_2983307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983307).length < 2 ^ (prefixWord ++ tailWord_2983307).sum := by decide
  have hdescent : baseEnd_2983307 < baseStart_2983307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983386 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_2983386 : Nat := 118140960795 + 2983386 * 2 ^ 59
def prefixEnd_2983386 : Nat := 4983230072969 + 3 ^ 40 * 2983386 * 2
def baseEnd_2983386 : Nat := 340424665754348827167703

theorem tailTrace_2983386 : CollatzResearch.WordTrace tailWord_2983386 prefixEnd_2983386 340424665754348827167703 := by
  unfold tailWord_2983386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203256692427379652202503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72542017846473012405873341 27203256692427379652202503)
  ·
    refine ⟨40804885038641069478303755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27203256692427379652202503 40804885038641069478303755)
    ·
      refine ⟨61207327557961604217455633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40804885038641069478303755 61207327557961604217455633)
      ·
        refine ⟨45905495668471203163091725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61207327557961604217455633 45905495668471203163091725)
        ·
          refine ⟨17214560875676701186159397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45905495668471203163091725 17214560875676701186159397)
          ·
            refine ⟨3227730164189381472404887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17214560875676701186159397 3227730164189381472404887)
            ·
              refine ⟨4841595246284072208607331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227730164189381472404887 4841595246284072208607331)
              ·
                refine ⟨7262392869426108312910997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841595246284072208607331 7262392869426108312910997)
                ·
                  refine ⟨340424665754348827167703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7262392869426108312910997 340424665754348827167703)
                  ·
                    rfl

theorem cell22_2983386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_2983386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983386 prefixEnd_2983386 := by exact prefixLift 2983386
  have htrace : WordTrace (prefixWord ++ tailWord_2983386) baseStart_2983386 baseEnd_2983386 := by
    simpa [prefixWord, tailWord_2983386, baseEnd_2983386] using wordTrace_append hprefix tailTrace_2983386
  have hstable : (prefixWord ++ tailWord_2983386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983386).length < 2 ^ (prefixWord ++ tailWord_2983386).sum := by decide
  have hdescent : baseEnd_2983386 < baseStart_2983386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983405 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2983405 : Nat := 118140960795 + 2983405 * 2 ^ 59
def prefixEnd_2983405 : Nat := 4983230072969 + 3 ^ 40 * 2983405 * 2
def baseEnd_2983405 : Nat := 1021280501351336765278051

theorem tailTrace_2983405 : CollatzResearch.WordTrace tailWord_2983405 prefixEnd_2983405 1021280501351336765278051 := by
  unfold tailWord_2983405
  simp only [CollatzResearch.WordTrace]
  refine ⟨108813719756640684853751669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72542479837760456569167779 108813719756640684853751669)
  ·
    refine ⟨10201286227185064205039219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108813719756640684853751669 10201286227185064205039219)
    ·
      refine ⟨15301929340777596307558829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10201286227185064205039219 15301929340777596307558829)
      ·
        refine ⟨5738223502791598615334561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15301929340777596307558829 5738223502791598615334561)
        ·
          refine ⟨4303667627093698961500921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5738223502791598615334561 4303667627093698961500921)
          ·
            refine ⟨3227750720320274221125691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4303667627093698961500921 3227750720320274221125691)
            ·
              refine ⟨4841626080480411331688537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227750720320274221125691 4841626080480411331688537)
              ·
                refine ⟨3631219560360308498766403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4841626080480411331688537 3631219560360308498766403)
                ·
                  refine ⟨5446829340540462748149605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631219560360308498766403 5446829340540462748149605)
                  ·
                    refine ⟨1021280501351336765278051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446829340540462748149605 1021280501351336765278051)
                    ·
                      rfl

theorem cell22_2983405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2983405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983405 prefixEnd_2983405 := by exact prefixLift 2983405
  have htrace : WordTrace (prefixWord ++ tailWord_2983405) baseStart_2983405 baseEnd_2983405 := by
    simpa [prefixWord, tailWord_2983405, baseEnd_2983405] using wordTrace_append hprefix tailTrace_2983405
  have hstable : (prefixWord ++ tailWord_2983405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983405).length < 2 ^ (prefixWord ++ tailWord_2983405).sum := by decide
  have hdescent : baseEnd_2983405 < baseStart_2983405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983416 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_2983416 : Nat := 118140960795 + 2983416 * 2 ^ 59
def prefixEnd_2983416 : Nat := 4983230072969 + 3 ^ 40 * 2983416 * 2
def baseEnd_2983416 : Nat := 1021284266876136403253017

theorem tailTrace_2983416 : CollatzResearch.WordTrace tailWord_2983416 prefixEnd_2983416 1021284266876136403253017 := by
  unfold tailWord_2983416
  simp only [CollatzResearch.WordTrace]
  refine ⟨54407060479800416866201051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72542747306400555821601401 54407060479800416866201051)
  ·
    refine ⟨81610590719700625299301577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54407060479800416866201051 81610590719700625299301577)
    ·
      refine ⟨61207943039775468974476183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81610590719700625299301577 61207943039775468974476183)
      ·
        refine ⟨91811914559663203461714275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61207943039775468974476183 91811914559663203461714275)
        ·
          refine ⟨137717871839494805192571413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91811914559663203461714275 137717871839494805192571413)
          ·
            refine ⟨6455525242476318993401785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137717871839494805192571413 6455525242476318993401785)
            ·
              refine ⟨4841643931857239245051339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455525242476318993401785 4841643931857239245051339)
              ·
                refine ⟨7262465897785858867577009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841643931857239245051339 7262465897785858867577009)
                ·
                  refine ⟨5446849423339394150682757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7262465897785858867577009 5446849423339394150682757)
                  ·
                    refine ⟨1021284266876136403253017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446849423339394150682757 1021284266876136403253017)
                    ·
                      rfl

theorem cell22_2983416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_2983416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983416 prefixEnd_2983416 := by exact prefixLift 2983416
  have htrace : WordTrace (prefixWord ++ tailWord_2983416) baseStart_2983416 baseEnd_2983416 := by
    simpa [prefixWord, tailWord_2983416, baseEnd_2983416] using wordTrace_append hprefix tailTrace_2983416
  have hstable : (prefixWord ++ tailWord_2983416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983416).length < 2 ^ (prefixWord ++ tailWord_2983416).sum := by decide
  have hdescent : baseEnd_2983416 < baseStart_2983416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983422 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2983422 : Nat := 118140960795 + 2983422 * 2 ^ 59
def prefixEnd_2983422 : Nat := 4983230072969 + 3 ^ 40 * 2983422 * 2
def baseEnd_2983422 : Nat := 1021286320798754387602999

theorem tailTrace_2983422 : CollatzResearch.WordTrace tailWord_2983422 prefixEnd_2983422 1021286320798754387602999 := by
  unfold tailWord_2983422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13601792474697387094640065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72542893198386064504747013 13601792474697387094640065)
  ·
    refine ⟨10201344356023040320980049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13601792474697387094640065 10201344356023040320980049)
    ·
      refine ⟨7651008267017280240735037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10201344356023040320980049 7651008267017280240735037)
      ·
        refine ⟨2869128100131480090275639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7651008267017280240735037 2869128100131480090275639)
        ·
          refine ⟨4303692150197220135413459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869128100131480090275639 4303692150197220135413459)
          ·
            refine ⟨6455538225295830203120189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303692150197220135413459 6455538225295830203120189)
            ·
              refine ⟨2420826834485936326170071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6455538225295830203120189 2420826834485936326170071)
              ·
                refine ⟨3631240251728904489255107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420826834485936326170071 3631240251728904489255107)
                ·
                  refine ⟨5446860377593356733882661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631240251728904489255107 5446860377593356733882661)
                  ·
                    refine ⟨1021286320798754387602999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446860377593356733882661 1021286320798754387602999)
                    ·
                      rfl

theorem cell22_2983422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2983422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983422 prefixEnd_2983422 := by exact prefixLift 2983422
  have htrace : WordTrace (prefixWord ++ tailWord_2983422) baseStart_2983422 baseEnd_2983422 := by
    simpa [prefixWord, tailWord_2983422, baseEnd_2983422] using wordTrace_append hprefix tailTrace_2983422
  have hstable : (prefixWord ++ tailWord_2983422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983422).length < 2 ^ (prefixWord ++ tailWord_2983422).sum := by decide
  have hdescent : baseEnd_2983422 < baseStart_2983422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983437 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2983437 : Nat := 118140960795 + 2983437 * 2 ^ 59
def prefixEnd_2983437 : Nat := 4983230072969 + 3 ^ 40 * 2983437 * 2
def baseEnd_2983437 : Nat := 340430485201766449492651

theorem tailTrace_2983437 : CollatzResearch.WordTrace tailWord_2983437 prefixEnd_2983437 340430485201766449492651 := by
  unfold tailWord_2983437
  simp only [CollatzResearch.WordTrace]
  refine ⟨108814886892524754318916565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72543257928349836212611043 108814886892524754318916565)
  ·
    refine ⟨2550348911543548929349607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 108814886892524754318916565 2550348911543548929349607)
    ·
      refine ⟨3825523367315323394024411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550348911543548929349607 3825523367315323394024411)
      ·
        refine ⟨5738285050972985091036617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825523367315323394024411 5738285050972985091036617)
        ·
          refine ⟨4303713788229738818277463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5738285050972985091036617 4303713788229738818277463)
          ·
            refine ⟨6455570682344608227416195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303713788229738818277463 6455570682344608227416195)
            ·
              refine ⟨9683356023516912341124293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455570682344608227416195 9683356023516912341124293)
              ·
                refine ⟨1815629254409421063960805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9683356023516912341124293 1815629254409421063960805)
                ·
                  refine ⟨340430485201766449492651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815629254409421063960805 340430485201766449492651)
                  ·
                    rfl

theorem cell22_2983437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2983437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983437 prefixEnd_2983437 := by exact prefixLift 2983437
  have htrace : WordTrace (prefixWord ++ tailWord_2983437) baseStart_2983437 baseEnd_2983437 := by
    simpa [prefixWord, tailWord_2983437, baseEnd_2983437] using wordTrace_append hprefix tailTrace_2983437
  have hstable : (prefixWord ++ tailWord_2983437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983437).length < 2 ^ (prefixWord ++ tailWord_2983437).sum := by decide
  have hdescent : baseEnd_2983437 < baseStart_2983437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983448 : List Nat := [2, 1, 2, 3, 5, 1, 1, 7]
def baseStart_2983448 : Nat := 118140960795 + 2983448 * 2 ^ 59
def prefixEnd_2983448 : Nat := 4983230072969 + 3 ^ 40 * 2983448 * 2
def baseEnd_2983448 : Nat := 113477246792233220716991

theorem tailTrace_2983448 : CollatzResearch.WordTrace tailWord_2983448 prefixEnd_2983448 113477246792233220716991 := by
  unfold tailWord_2983448
  simp only [CollatzResearch.WordTrace]
  refine ⟨54407644047742451598783499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72543525396989935465044665 54407644047742451598783499)
  ·
    refine ⟨81611466071613677398175249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54407644047742451598783499 81611466071613677398175249)
    ·
      refine ⟨61208599553710258048631437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81611466071613677398175249 61208599553710258048631437)
      ·
        refine ⟨22953224832641346768236789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61208599553710258048631437 22953224832641346768236789)
        ·
          refine ⟨2151864828060126259522199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22953224832641346768236789 2151864828060126259522199)
          ·
            refine ⟨3227797242090189389283299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151864828060126259522199 3227797242090189389283299)
            ·
              refine ⟨4841695863135284083924949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227797242090189389283299 4841695863135284083924949)
              ·
                refine ⟨113477246792233220716991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4841695863135284083924949 113477246792233220716991)
                ·
                  rfl

theorem cell22_2983448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_2983448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983448 prefixEnd_2983448 := by exact prefixLift 2983448
  have htrace : WordTrace (prefixWord ++ tailWord_2983448) baseStart_2983448 baseEnd_2983448 := by
    simpa [prefixWord, tailWord_2983448, baseEnd_2983448] using wordTrace_append hprefix tailTrace_2983448
  have hstable : (prefixWord ++ tailWord_2983448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983448).length < 2 ^ (prefixWord ++ tailWord_2983448).sum := by decide
  have hdescent : baseEnd_2983448 < baseStart_2983448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983474 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_2983474 : Nat := 118140960795 + 2983474 * 2 ^ 59
def prefixEnd_2983474 : Nat := 4983230072969 + 3 ^ 40 * 2983474 * 2
def baseEnd_2983474 : Nat := 1021304121461443585302839

theorem tailTrace_2983474 : CollatzResearch.WordTrace tailWord_2983474 prefixEnd_2983474 1021304121461443585302839 := by
  unfold tailWord_2983474
  simp only [CollatzResearch.WordTrace]
  refine ⟨27204059098347677409503369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72544157595593806425342317 27204059098347677409503369)
  ·
    refine ⟨20403044323760758057127527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27204059098347677409503369 20403044323760758057127527)
    ·
      refine ⟨30604566485641137085691291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20403044323760758057127527 30604566485641137085691291)
      ·
        refine ⟨45906849728461705628536937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30604566485641137085691291 45906849728461705628536937)
        ·
          refine ⟨34430137296346279221402703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45906849728461705628536937 34430137296346279221402703)
          ·
            refine ⟨51645205944519418832104055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34430137296346279221402703 51645205944519418832104055)
            ·
              refine ⟨77467808916779128248156083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51645205944519418832104055 77467808916779128248156083)
              ·
                refine ⟨116201713375168692372234125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77467808916779128248156083 116201713375168692372234125)
                ·
                  refine ⟨43575642515688259639587797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116201713375168692372234125 43575642515688259639587797)
                  ·
                    refine ⟨1021304121461443585302839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43575642515688259639587797 1021304121461443585302839)
                    ·
                      rfl

theorem cell22_2983474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_2983474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983474 prefixEnd_2983474 := by exact prefixLift 2983474
  have htrace : WordTrace (prefixWord ++ tailWord_2983474) baseStart_2983474 baseEnd_2983474 := by
    simpa [prefixWord, tailWord_2983474, baseEnd_2983474] using wordTrace_append hprefix tailTrace_2983474
  have hstable : (prefixWord ++ tailWord_2983474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983474).length < 2 ^ (prefixWord ++ tailWord_2983474).sum := by decide
  have hdescent : baseEnd_2983474 < baseStart_2983474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983480 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 1, 3]
def baseStart_2983480 : Nat := 118140960795 + 2983480 * 2 ^ 59
def prefixEnd_2983480 : Nat := 4983230072969 + 3 ^ 40 * 2983480 * 2
def baseEnd_2983480 : Nat := 1021306175384061569652821

theorem tailTrace_2983480 : CollatzResearch.WordTrace tailWord_2983480 prefixEnd_2983480 1021306175384061569652821 := by
  unfold tailWord_2983480
  simp only [CollatzResearch.WordTrace]
  refine ⟨54408227615684486331365947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72544303487579315108487929 54408227615684486331365947)
  ·
    refine ⟨81612341423526729497048921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54408227615684486331365947 81612341423526729497048921)
    ·
      refine ⟨61209256067645047122786691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81612341423526729497048921 61209256067645047122786691)
      ·
        refine ⟨91813884101467570684180037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61209256067645047122786691 91813884101467570684180037)
        ·
          refine ⟨17215103269025169503283757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91813884101467570684180037 17215103269025169503283757)
          ·
            refine ⟨6455663725884438563731409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17215103269025169503283757 6455663725884438563731409)
            ·
              refine ⟨4841747794413328922798557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455663725884438563731409 4841747794413328922798557)
              ·
                refine ⟨1815655422904998346049459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4841747794413328922798557 1815655422904998346049459)
                ·
                  refine ⟨2723483134357497519074189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815655422904998346049459 2723483134357497519074189)
                  ·
                    refine ⟨1021306175384061569652821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723483134357497519074189 1021306175384061569652821)
                    ·
                      rfl

theorem cell22_2983480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_2983480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983480 prefixEnd_2983480 := by exact prefixLift 2983480
  have htrace : WordTrace (prefixWord ++ tailWord_2983480) baseStart_2983480 baseEnd_2983480 := by
    simpa [prefixWord, tailWord_2983480, baseEnd_2983480] using wordTrace_append hprefix tailTrace_2983480
  have hstable : (prefixWord ++ tailWord_2983480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983480).length < 2 ^ (prefixWord ++ tailWord_2983480).sum := by decide
  have hdescent : baseEnd_2983480 < baseStart_2983480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983523 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 1, 4]
def baseStart_2983523 : Nat := 118140960795 + 2983523 * 2 ^ 59
def prefixEnd_2983523 : Nat := 4983230072969 + 3 ^ 40 * 2983523 * 2
def baseEnd_2983523 : Nat := 1021320895162823790827689

theorem tailTrace_2983523 : CollatzResearch.WordTrace tailWord_2983523 prefixEnd_2983523 1021320895162823790827689 := by
  unfold tailWord_2983523
  simp only [CollatzResearch.WordTrace]
  refine ⟨108818023570213191006547223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72545349046808794004364815 108818023570213191006547223)
  ·
    refine ⟨163227035355319786509820835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108818023570213191006547223 163227035355319786509820835)
    ·
      refine ⟨244840553032979679764731253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163227035355319786509820835 244840553032979679764731253)
      ·
        refine ⟨22953801846841844977943555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244840553032979679764731253 22953801846841844977943555)
        ·
          refine ⟨34430702770262767466915333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22953801846841844977943555 34430702770262767466915333)
          ·
            refine ⟨6455756769424268900046625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34430702770262767466915333 6455756769424268900046625)
            ·
              refine ⟨4841817577068201675034969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455756769424268900046625 4841817577068201675034969)
              ·
                refine ⟨3631363182801151256276227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4841817577068201675034969 3631363182801151256276227)
                ·
                  refine ⟨5447044774201726884414341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631363182801151256276227 5447044774201726884414341)
                  ·
                    refine ⟨1021320895162823790827689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447044774201726884414341 1021320895162823790827689)
                    ·
                      rfl

theorem cell22_2983523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 4].length) (baseStart_2983523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983523 prefixEnd_2983523 := by exact prefixLift 2983523
  have htrace : WordTrace (prefixWord ++ tailWord_2983523) baseStart_2983523 baseEnd_2983523 := by
    simpa [prefixWord, tailWord_2983523, baseEnd_2983523] using wordTrace_append hprefix tailTrace_2983523
  have hstable : (prefixWord ++ tailWord_2983523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983523).length < 2 ^ (prefixWord ++ tailWord_2983523).sum := by decide
  have hdescent : baseEnd_2983523 < baseStart_2983523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983553 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2983553 : Nat := 118140960795 + 2983553 * 2 ^ 59
def prefixEnd_2983553 : Nat := 4983230072969 + 3 ^ 40 * 2983553 * 2
def baseEnd_2983553 : Nat := 1021331164775913712577597

theorem tailTrace_2983553 : CollatzResearch.WordTrace tailWord_2983553 prefixEnd_2983553 1021331164775913712577597 := by
  unfold tailWord_2983553
  simp only [CollatzResearch.WordTrace]
  refine ⟨108819117760104506130139313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72546078506736337420092875 108819117760104506130139313)
  ·
    refine ⟨81614338320078379597604485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108819117760104506130139313 81614338320078379597604485)
    ·
      refine ⟨15302688435014696174550841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81614338320078379597604485 15302688435014696174550841)
      ·
        refine ⟨11477016326261022130913131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15302688435014696174550841 11477016326261022130913131)
        ·
          refine ⟨17215524489391533196369697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477016326261022130913131 17215524489391533196369697)
          ·
            refine ⟨12911643367043649897277273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17215524489391533196369697 12911643367043649897277273)
            ·
              refine ⟨9683732525282737422957955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12911643367043649897277273 9683732525282737422957955)
              ·
                refine ⟨14525598787924106134436933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9683732525282737422957955 14525598787924106134436933)
                ·
                  refine ⟨2723549772735769900206925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14525598787924106134436933 2723549772735769900206925)
                  ·
                    refine ⟨1021331164775913712577597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723549772735769900206925 1021331164775913712577597)
                    ·
                      rfl

theorem cell22_2983553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2983553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983553 prefixEnd_2983553 := by exact prefixLift 2983553
  have htrace : WordTrace (prefixWord ++ tailWord_2983553) baseStart_2983553 baseEnd_2983553 := by
    simpa [prefixWord, tailWord_2983553, baseEnd_2983553] using wordTrace_append hprefix tailTrace_2983553
  have hstable : (prefixWord ++ tailWord_2983553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983553).length < 2 ^ (prefixWord ++ tailWord_2983553).sum := by decide
  have hdescent : baseEnd_2983553 < baseStart_2983553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983566 : List Nat := [4, 1, 1, 3, 1, 2, 1, 9]
def baseStart_2983566 : Nat := 118140960795 + 2983566 * 2 ^ 59
def prefixEnd_2983566 : Nat := 4983230072969 + 3 ^ 40 * 2983566 * 2
def baseEnd_2983566 : Nat := 113481734993509556889173

theorem tailTrace_2983566 : CollatzResearch.WordTrace tailWord_2983566 prefixEnd_2983566 113481734993509556889173 := by
  unfold tailWord_2983566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13602448988632176168795319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72546394606038272900241701 13602448988632176168795319)
  ·
    refine ⟨20403673482948264253192979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13602448988632176168795319 20403673482948264253192979)
    ·
      refine ⟨30605510224422396379789469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20403673482948264253192979 30605510224422396379789469)
      ·
        refine ⟨11477066334158398642421051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30605510224422396379789469 11477066334158398642421051)
        ·
          refine ⟨17215599501237597963631577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477066334158398642421051 17215599501237597963631577)
          ·
            refine ⟨12911699625928198472723683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17215599501237597963631577 12911699625928198472723683)
            ·
              refine ⟨19367549438892297709085525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12911699625928198472723683 19367549438892297709085525)
              ·
                refine ⟨113481734993509556889173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19367549438892297709085525 113481734993509556889173)
                ·
                  rfl

theorem cell22_2983566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_2983566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983566 prefixEnd_2983566 := by exact prefixLift 2983566
  have htrace : WordTrace (prefixWord ++ tailWord_2983566) baseStart_2983566 baseEnd_2983566 := by
    simpa [prefixWord, tailWord_2983566, baseEnd_2983566] using wordTrace_append hprefix tailTrace_2983566
  have hstable : (prefixWord ++ tailWord_2983566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983566).length < 2 ^ (prefixWord ++ tailWord_2983566).sum := by decide
  have hdescent : baseEnd_2983566 < baseStart_2983566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983615 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 1, 3]
def baseStart_2983615 : Nat := 118140960795 + 2983615 * 2 ^ 59
def prefixEnd_2983615 : Nat := 4983230072969 + 3 ^ 40 * 2983615 * 2
def baseEnd_2983615 : Nat := 1021352388642966217527407

theorem tailTrace_2983615 : CollatzResearch.WordTrace tailWord_2983615 prefixEnd_2983615 1021352388642966217527407 := by
  unfold tailWord_2983615
  simp only [CollatzResearch.WordTrace]
  refine ⟨108821379085879890718896299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72547586057253260479264199 108821379085879890718896299)
  ·
    refine ⟨163232068628819836078344449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108821379085879890718896299 163232068628819836078344449)
    ·
      refine ⟨122424051471614877058758337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163232068628819836078344449 122424051471614877058758337)
      ·
        refine ⟨91818038603711157794068753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122424051471614877058758337 91818038603711157794068753)
        ·
          refine ⟨68863528952783368345551565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91818038603711157794068753 68863528952783368345551565)
          ·
            refine ⟨25823823357293763129581837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68863528952783368345551565 25823823357293763129581837)
            ·
              refine ⟨9683933758985161173593189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25823823357293763129581837 9683933758985161173593189)
              ·
                refine ⟨1815737579809717720048723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9683933758985161173593189 1815737579809717720048723)
                ·
                  refine ⟨2723606369714576580073085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815737579809717720048723 2723606369714576580073085)
                  ·
                    refine ⟨1021352388642966217527407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723606369714576580073085 1021352388642966217527407)
                    ·
                      rfl

theorem cell22_2983615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_2983615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983615 prefixEnd_2983615 := by exact prefixLift 2983615
  have htrace : WordTrace (prefixWord ++ tailWord_2983615) baseStart_2983615 baseEnd_2983615 := by
    simpa [prefixWord, tailWord_2983615, baseEnd_2983615] using wordTrace_append hprefix tailTrace_2983615
  have hstable : (prefixWord ++ tailWord_2983615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983615).length < 2 ^ (prefixWord ++ tailWord_2983615).sum := by decide
  have hdescent : baseEnd_2983615 < baseStart_2983615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983671 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_2983671 : Nat := 118140960795 + 2983671 * 2 ^ 59
def prefixEnd_2983671 : Nat := 4983230072969 + 3 ^ 40 * 2983671 * 2
def baseEnd_2983671 : Nat := 1021371558587400738127235

theorem tailTrace_2983671 : CollatzResearch.WordTrace tailWord_2983671 prefixEnd_2983671 1021371558587400738127235 := by
  unfold tailWord_2983671
  simp only [CollatzResearch.WordTrace]
  refine ⟨108823421573677012282934867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72548947715784674855289911 108823421573677012282934867)
  ·
    refine ⟨163235132360515518424402301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108823421573677012282934867 163235132360515518424402301)
    ·
      refine ⟨61213174635193319409150863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163235132360515518424402301 61213174635193319409150863)
      ·
        refine ⟨91819761952789979113726295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61213174635193319409150863 91819761952789979113726295)
        ·
          refine ⟨137729642929184968670589443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91819761952789979113726295 137729642929184968670589443)
          ·
            refine ⟨206594464393777453005884165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137729642929184968670589443 206594464393777453005884165)
            ·
              refine ⟨38736462073833272438603281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206594464393777453005884165 38736462073833272438603281)
              ·
                refine ⟨29052346555374954328952461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38736462073833272438603281 29052346555374954328952461)
                ·
                  refine ⟨10894629958265607873357173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29052346555374954328952461 10894629958265607873357173)
                  ·
                    refine ⟨1021371558587400738127235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10894629958265607873357173 1021371558587400738127235)
                    ·
                      rfl

theorem cell22_2983671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_2983671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983671 prefixEnd_2983671 := by exact prefixLift 2983671
  have htrace : WordTrace (prefixWord ++ tailWord_2983671) baseStart_2983671 baseEnd_2983671 := by
    simpa [prefixWord, tailWord_2983671, baseEnd_2983671] using wordTrace_append hprefix tailTrace_2983671
  have hstable : (prefixWord ++ tailWord_2983671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983671).length < 2 ^ (prefixWord ++ tailWord_2983671).sum := by decide
  have hdescent : baseEnd_2983671 < baseStart_2983671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983700 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2983700 : Nat := 118140960795 + 2983700 * 2 ^ 59
def prefixEnd_2983700 : Nat := 4983230072969 + 3 ^ 40 * 2983700 * 2
def baseEnd_2983700 : Nat := 1021381485880054329152147

theorem tailTrace_2983700 : CollatzResearch.WordTrace tailWord_2983700 prefixEnd_2983700 1021381485880054329152147 := by
  unfold tailWord_2983700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54412239645285975117870277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72549652860381300157160369 54412239645285975117870277)
  ·
    refine ⟨10202294933491120334600677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54412239645285975117870277 10202294933491120334600677)
    ·
      refine ⟨1912930300029585062737627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10202294933491120334600677 1912930300029585062737627)
      ·
        refine ⟨2869395450044377594106441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912930300029585062737627 2869395450044377594106441)
        ·
          refine ⟨2152046587533283195579831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869395450044377594106441 2152046587533283195579831)
          ·
            refine ⟨3228069881299924793369747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152046587533283195579831 3228069881299924793369747)
            ·
              refine ⟨4842104821949887190054621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228069881299924793369747 4842104821949887190054621)
              ·
                refine ⟨1815789308231207696270483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4842104821949887190054621 1815789308231207696270483)
                ·
                  refine ⟨2723683962346811544405725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815789308231207696270483 2723683962346811544405725)
                  ·
                    refine ⟨1021381485880054329152147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723683962346811544405725 1021381485880054329152147)
                    ·
                      rfl

theorem cell22_2983700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2983700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983700 prefixEnd_2983700 := by exact prefixLift 2983700
  have htrace : WordTrace (prefixWord ++ tailWord_2983700) baseStart_2983700 baseEnd_2983700 := by
    simpa [prefixWord, tailWord_2983700, baseEnd_2983700] using wordTrace_append hprefix tailTrace_2983700
  have hstable : (prefixWord ++ tailWord_2983700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983700).length < 2 ^ (prefixWord ++ tailWord_2983700).sum := by decide
  have hdescent : baseEnd_2983700 < baseStart_2983700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983703 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 1, 6]
def baseStart_2983703 : Nat := 118140960795 + 2983703 * 2 ^ 59
def prefixEnd_2983703 : Nat := 4983230072969 + 3 ^ 40 * 2983703 * 2
def baseEnd_2983703 : Nat := 1021382512841363321327137

theorem tailTrace_2983703 : CollatzResearch.WordTrace tailWord_2983703 prefixEnd_2983703 1021382512841363321327137 := by
  unfold tailWord_2983703
  simp only [CollatzResearch.WordTrace]
  refine ⟨108824588709561081748099763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72549725806374054498733175 108824588709561081748099763)
  ·
    refine ⟨163236883064341622622149645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108824588709561081748099763 163236883064341622622149645)
    ·
      refine ⟨61213831149128108483306117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163236883064341622622149645 61213831149128108483306117)
      ·
        refine ⟨11477593340461520340619897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61213831149128108483306117 11477593340461520340619897)
        ·
          refine ⟨8608195005346140255464923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11477593340461520340619897 8608195005346140255464923)
          ·
            refine ⟨12912292508019210383197385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608195005346140255464923 12912292508019210383197385)
            ·
              refine ⟨9684219381014407787398039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12912292508019210383197385 9684219381014407787398039)
              ·
                refine ⟨14526329071521611681097059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684219381014407787398039 14526329071521611681097059)
                ·
                  refine ⟨21789493607282417521645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14526329071521611681097059 21789493607282417521645589)
                  ·
                    refine ⟨1021382512841363321327137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21789493607282417521645589 1021382512841363321327137)
                    ·
                      rfl

theorem cell22_2983703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_2983703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983703 prefixEnd_2983703 := by exact prefixLift 2983703
  have htrace : WordTrace (prefixWord ++ tailWord_2983703) baseStart_2983703 baseEnd_2983703 := by
    simpa [prefixWord, tailWord_2983703, baseEnd_2983703] using wordTrace_append hprefix tailTrace_2983703
  have hstable : (prefixWord ++ tailWord_2983703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983703).length < 2 ^ (prefixWord ++ tailWord_2983703).sum := by decide
  have hdescent : baseEnd_2983703 < baseStart_2983703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983720 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2983720 : Nat := 118140960795 + 2983720 * 2 ^ 59
def prefixEnd_2983720 : Nat := 4983230072969 + 3 ^ 40 * 2983720 * 2
def baseEnd_2983720 : Nat := 1021388332288780943652085

theorem tailTrace_2983720 : CollatzResearch.WordTrace tailWord_2983720 prefixEnd_2983720 1021388332288780943652085 := by
  unfold tailWord_2983720
  simp only [CollatzResearch.WordTrace]
  refine ⟨54412604375249746825734307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72550139166999662434312409 54412604375249746825734307)
  ·
    refine ⟨81618906562874620238601461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54412604375249746825734307 81618906562874620238601461)
    ·
      refine ⟨7651772490269495647368887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81618906562874620238601461 7651772490269495647368887)
      ·
        refine ⟨11477658735404243471053331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7651772490269495647368887 11477658735404243471053331)
        ·
          refine ⟨17216488103106365206579997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477658735404243471053331 17216488103106365206579997)
          ·
            refine ⟨6456183038664886952467499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17216488103106365206579997 6456183038664886952467499)
            ·
              refine ⟨9684274557997330428701249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456183038664886952467499 9684274557997330428701249)
              ·
                refine ⟨7263205918497997821525937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9684274557997330428701249 7263205918497997821525937)
                ·
                  refine ⟨5447404438873498366144453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7263205918497997821525937 5447404438873498366144453)
                  ·
                    refine ⟨1021388332288780943652085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447404438873498366144453 1021388332288780943652085)
                    ·
                      rfl

theorem cell22_2983720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2983720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983720 prefixEnd_2983720 := by exact prefixLift 2983720
  have htrace : WordTrace (prefixWord ++ tailWord_2983720) baseStart_2983720 baseEnd_2983720 := by
    simpa [prefixWord, tailWord_2983720, baseEnd_2983720] using wordTrace_append hprefix tailTrace_2983720
  have hstable : (prefixWord ++ tailWord_2983720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983720).length < 2 ^ (prefixWord ++ tailWord_2983720).sum := by decide
  have hdescent : baseEnd_2983720 < baseStart_2983720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983793 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_2983793 : Nat := 118140960795 + 2983793 * 2 ^ 59
def prefixEnd_2983793 : Nat := 4983230072969 + 3 ^ 40 * 2983793 * 2
def baseEnd_2983793 : Nat := 1021413321680633086576861

theorem tailTrace_2983793 : CollatzResearch.WordTrace tailWord_2983793 prefixEnd_2983793 1021413321680633086576861 := by
  unfold tailWord_2983793
  simp only [CollatzResearch.WordTrace]
  refine ⟨108827871279235027118876033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72551914186156684745917355 108827871279235027118876033)
  ·
    refine ⟨81620903459426270339157025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108827871279235027118876033 81620903459426270339157025)
    ·
      refine ⟨61215677594569702754367769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81620903459426270339157025 61215677594569702754367769)
      ·
        refine ⟨45911758195927277065775827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61215677594569702754367769 45911758195927277065775827)
        ·
          refine ⟨68867637293890915598663741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45911758195927277065775827 68867637293890915598663741)
          ·
            refine ⟨25825363985209093349498903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68867637293890915598663741 25825363985209093349498903)
            ·
              refine ⟨38738045977813640024248355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25825363985209093349498903 38738045977813640024248355)
              ·
                refine ⟨58107068966720460036372533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38738045977813640024248355 58107068966720460036372533)
                ·
                  refine ⟨5447537715630043128409925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58107068966720460036372533 5447537715630043128409925)
                  ·
                    refine ⟨1021413321680633086576861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447537715630043128409925 1021413321680633086576861)
                    ·
                      rfl

theorem cell22_2983793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_2983793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983793 prefixEnd_2983793 := by exact prefixLift 2983793
  have htrace : WordTrace (prefixWord ++ tailWord_2983793) baseStart_2983793 baseEnd_2983793 := by
    simpa [prefixWord, tailWord_2983793, baseEnd_2983793] using wordTrace_append hprefix tailTrace_2983793
  have hstable : (prefixWord ++ tailWord_2983793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983793).length < 2 ^ (prefixWord ++ tailWord_2983793).sum := by decide
  have hdescent : baseEnd_2983793 < baseStart_2983793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983808 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_2983808 : Nat := 118140960795 + 2983808 * 2 ^ 59
def prefixEnd_2983808 : Nat := 4983230072969 + 3 ^ 40 * 2983808 * 2
def baseEnd_2983808 : Nat := 340472818829059349150605

theorem tailTrace_2983808 : CollatzResearch.WordTrace tailWord_2983808 prefixEnd_2983808 340472818829059349150605 := by
  unfold tailWord_2983808
  simp only [CollatzResearch.WordTrace]
  refine ⟨54414209187090342340336039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72552278916120456453781385 54414209187090342340336039)
  ·
    refine ⟨81621313780635513510504059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54414209187090342340336039 81621313780635513510504059)
    ·
      refine ⟨122431970670953270265756089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81621313780635513510504059 122431970670953270265756089)
      ·
        refine ⟨91823978003214952699317067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122431970670953270265756089 91823978003214952699317067)
        ·
          refine ⟨137735967004822429048975601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91823978003214952699317067 137735967004822429048975601)
          ·
            refine ⟨103301975253616821786731701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137735967004822429048975601 103301975253616821786731701)
            ·
              refine ⟨9684560180026577042506097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103301975253616821786731701 9684560180026577042506097)
              ·
                refine ⟨7263420135019932781879573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9684560180026577042506097 7263420135019932781879573)
                ·
                  refine ⟨340472818829059349150605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7263420135019932781879573 340472818829059349150605)
                  ·
                    rfl

theorem cell22_2983808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_2983808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983808 prefixEnd_2983808 := by exact prefixLift 2983808
  have htrace : WordTrace (prefixWord ++ tailWord_2983808) baseStart_2983808 baseEnd_2983808 := by
    simpa [prefixWord, tailWord_2983808, baseEnd_2983808] using wordTrace_append hprefix tailTrace_2983808
  have hstable : (prefixWord ++ tailWord_2983808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983808).length < 2 ^ (prefixWord ++ tailWord_2983808).sum := by decide
  have hdescent : baseEnd_2983808 < baseStart_2983808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983825 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 4]
def baseStart_2983825 : Nat := 118140960795 + 2983825 * 2 ^ 59
def prefixEnd_2983825 : Nat := 4983230072969 + 3 ^ 40 * 2983825 * 2
def baseEnd_2983825 : Nat := 340474758644865223258921

theorem tailTrace_2983825 : CollatzResearch.WordTrace tailWord_2983825 prefixEnd_2983825 340474758644865223258921 := by
  unfold tailWord_2983825
  simp only [CollatzResearch.WordTrace]
  refine ⟨108829038415119096584040929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72552692276746064389360619 108829038415119096584040929)
  ·
    refine ⟨81621778811339322438030697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108829038415119096584040929 81621778811339322438030697)
    ·
      refine ⟨61216334108504491828523023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81621778811339322438030697 61216334108504491828523023)
      ·
        refine ⟨91824501162756737742784535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61216334108504491828523023 91824501162756737742784535)
        ·
          refine ⟨137736751744135106614176803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91824501162756737742784535 137736751744135106614176803)
          ·
            refine ⟨206605127616202659921265205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137736751744135106614176803 206605127616202659921265205)
            ·
              refine ⟨19369230714018999367618613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206605127616202659921265205 19369230714018999367618613)
              ·
                refine ⟨1815865379439281190714245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19369230714018999367618613 1815865379439281190714245)
                ·
                  refine ⟨340474758644865223258921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815865379439281190714245 340474758644865223258921)
                  ·
                    rfl

theorem cell22_2983825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_2983825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983825 prefixEnd_2983825 := by exact prefixLift 2983825
  have htrace : WordTrace (prefixWord ++ tailWord_2983825) baseStart_2983825 baseEnd_2983825 := by
    simpa [prefixWord, tailWord_2983825, baseEnd_2983825] using wordTrace_append hprefix tailTrace_2983825
  have hstable : (prefixWord ++ tailWord_2983825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983825).length < 2 ^ (prefixWord ++ tailWord_2983825).sum := by decide
  have hdescent : baseEnd_2983825 < baseStart_2983825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983842 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2983842 : Nat := 118140960795 + 2983842 * 2 ^ 59
def prefixEnd_2983842 : Nat := 4983230072969 + 3 ^ 40 * 2983842 * 2
def baseEnd_2983842 : Nat := 340476698460671097367237

theorem tailTrace_2983842 : CollatzResearch.WordTrace tailWord_2983842 prefixEnd_2983842 340476698460671097367237 := by
  unfold tailWord_2983842
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207414614014377121852445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72553105637371672324939853 27207414614014377121852445)
  ·
    refine ⟨10202780480255391420694667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27207414614014377121852445 10202780480255391420694667)
    ·
      refine ⟨15304170720383087131042001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10202780480255391420694667 15304170720383087131042001)
      ·
        refine ⟨11478128040287315348281501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15304170720383087131042001 11478128040287315348281501)
        ·
          refine ⟨4304298015107743255605563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11478128040287315348281501 4304298015107743255605563)
          ·
            refine ⟨6456447022661614883408345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304298015107743255605563 6456447022661614883408345)
            ·
              refine ⟨4842335266996211162556259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6456447022661614883408345 4842335266996211162556259)
              ·
                refine ⟨7263502900494316743834389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842335266996211162556259 7263502900494316743834389)
                ·
                  refine ⟨340476698460671097367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7263502900494316743834389 340476698460671097367237)
                  ·
                    rfl

theorem cell22_2983842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2983842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983842 prefixEnd_2983842 := by exact prefixLift 2983842
  have htrace : WordTrace (prefixWord ++ tailWord_2983842) baseStart_2983842 baseEnd_2983842 := by
    simpa [prefixWord, tailWord_2983842, baseEnd_2983842] using wordTrace_append hprefix tailTrace_2983842
  have hstable : (prefixWord ++ tailWord_2983842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983842).length < 2 ^ (prefixWord ++ tailWord_2983842).sum := by decide
  have hdescent : baseEnd_2983842 < baseStart_2983842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983857 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_2983857 : Nat := 118140960795 + 2983857 * 2 ^ 59
def prefixEnd_2983857 : Nat := 4983230072969 + 3 ^ 40 * 2983857 * 2
def baseEnd_2983857 : Nat := 1021435230188558252976665

theorem tailTrace_2983857 : CollatzResearch.WordTrace tailWord_2983857 prefixEnd_2983857 1021435230188558252976665 := by
  unfold tailWord_2983857
  simp only [CollatzResearch.WordTrace]
  refine ⟨108830205551003166049205825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72553470367335444032803883 108830205551003166049205825)
  ·
    refine ⟨81622654163252374536904369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108830205551003166049205825 81622654163252374536904369)
    ·
      refine ⟨61216990622439280902678277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81622654163252374536904369 61216990622439280902678277)
      ·
        refine ⟨11478185741707365169252177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61216990622439280902678277 11478185741707365169252177)
        ·
          refine ⟨8608639306280523876939133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11478185741707365169252177 8608639306280523876939133)
          ·
            refine ⟨3228239739855196453852175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8608639306280523876939133 3228239739855196453852175)
            ·
              refine ⟨4842359609782794680778263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228239739855196453852175 4842359609782794680778263)
              ·
                refine ⟨7263539414674192021167395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842359609782794680778263 7263539414674192021167395)
                ·
                  refine ⟨10895309122011288031751093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263539414674192021167395 10895309122011288031751093)
                  ·
                    refine ⟨1021435230188558252976665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10895309122011288031751093 1021435230188558252976665)
                    ·
                      rfl

theorem cell22_2983857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_2983857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983857 prefixEnd_2983857 := by exact prefixLift 2983857
  have htrace : WordTrace (prefixWord ++ tailWord_2983857) baseStart_2983857 baseEnd_2983857 := by
    simpa [prefixWord, tailWord_2983857, baseEnd_2983857] using wordTrace_append hprefix tailTrace_2983857
  have hstable : (prefixWord ++ tailWord_2983857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983857).length < 2 ^ (prefixWord ++ tailWord_2983857).sum := by decide
  have hdescent : baseEnd_2983857 < baseStart_2983857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983870 : List Nat := [4, 2, 1, 1, 1, 4, 1, 8]
def baseStart_2983870 : Nat := 118140960795 + 2983870 * 2 ^ 59
def prefixEnd_2983870 : Nat := 4983230072969 + 3 ^ 40 * 2983870 * 2
def baseEnd_2983870 : Nat := 113493297817136728044625

theorem tailTrace_2983870 : CollatzResearch.WordTrace tailWord_2983870 prefixEnd_2983870 113493297817136728044625 := by
  unfold tailWord_2983870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603834962494508658678633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72553786466637379512952709 13603834962494508658678633)
  ·
    refine ⟨10202876221870881494008975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13603834962494508658678633 10202876221870881494008975)
    ·
      refine ⟨15304314332806322241013463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10202876221870881494008975 15304314332806322241013463)
      ·
        refine ⟨22956471499209483361520195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15304314332806322241013463 22956471499209483361520195)
        ·
          refine ⟨34434707248814225042280293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22956471499209483361520195 34434707248814225042280293)
          ·
            refine ⟨6456507609152667195427555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34434707248814225042280293 6456507609152667195427555)
            ·
              refine ⟨9684761413729000793141333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456507609152667195427555 9684761413729000793141333)
              ·
                refine ⟨113493297817136728044625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9684761413729000793141333 113493297817136728044625)
                ·
                  rfl

theorem cell22_2983870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_2983870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983870 prefixEnd_2983870 := by exact prefixLift 2983870
  have htrace : WordTrace (prefixWord ++ tailWord_2983870) baseStart_2983870 baseEnd_2983870 := by
    simpa [prefixWord, tailWord_2983870, baseEnd_2983870] using wordTrace_append hprefix tailTrace_2983870
  have hstable : (prefixWord ++ tailWord_2983870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983870).length < 2 ^ (prefixWord ++ tailWord_2983870).sum := by decide
  have hdescent : baseEnd_2983870 < baseStart_2983870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983960 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_2983960 : Nat := 118140960795 + 2983960 * 2 ^ 59
def prefixEnd_2983960 : Nat := 4983230072969 + 3 ^ 40 * 2983960 * 2
def baseEnd_2983960 : Nat := 340490163064500105883783

theorem tailTrace_2983960 : CollatzResearch.WordTrace tailWord_2983960 prefixEnd_2983960 340490163064500105883783 := by
  unfold tailWord_2983960
  simp only [CollatzResearch.WordTrace]
  refine ⟨54416981134815007320102667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72555974846420009760136889 54416981134815007320102667)
  ·
    refine ⟨81625471702222510980154001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54416981134815007320102667 81625471702222510980154001)
    ·
      refine ⟨61219103776666883235115501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81625471702222510980154001 61219103776666883235115501)
      ·
        refine ⟨22957163916250081213168313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61219103776666883235115501 22957163916250081213168313)
        ·
          refine ⟨17217872937187560909876235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22957163916250081213168313 17217872937187560909876235)
          ·
            refine ⟨25826809405781341364814353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17217872937187560909876235 25826809405781341364814353)
            ·
              refine ⟨19370107054336006023610765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25826809405781341364814353 19370107054336006023610765)
              ·
                refine ⟨7263790145376002258854037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19370107054336006023610765 7263790145376002258854037)
                ·
                  refine ⟨340490163064500105883783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7263790145376002258854037 340490163064500105883783)
                  ·
                    rfl

theorem cell22_2983960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_2983960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2983960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2983960 prefixEnd_2983960 := by exact prefixLift 2983960
  have htrace : WordTrace (prefixWord ++ tailWord_2983960) baseStart_2983960 baseEnd_2983960 := by
    simpa [prefixWord, tailWord_2983960, baseEnd_2983960] using wordTrace_append hprefix tailTrace_2983960
  have hstable : (prefixWord ++ tailWord_2983960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983960).length < 2 ^ (prefixWord ++ tailWord_2983960).sum := by decide
  have hdescent : baseEnd_2983960 < baseStart_2983960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984035 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_2984035 : Nat := 118140960795 + 2984035 * 2 ^ 59
def prefixEnd_2984035 : Nat := 4983230072969 + 3 ^ 40 * 2984035 * 2
def baseEnd_2984035 : Nat := 1021496163226225122026119

theorem tailTrace_2984035 : CollatzResearch.WordTrace tailWord_2984035 prefixEnd_2984035 1021496163226225122026119 := by
  unfold tailWord_2984035
  simp only [CollatzResearch.WordTrace]
  refine ⟨108836697744358302449185559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72557798496238868299457039 108836697744358302449185559)
  ·
    refine ⟨163255046616537453673778339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108836697744358302449185559 163255046616537453673778339)
    ·
      refine ⟨244882569924806180510667509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163255046616537453673778339 244882569924806180510667509)
      ·
        refine ⟨22957740930450579422875079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244882569924806180510667509 22957740930450579422875079)
        ·
          refine ⟨34436611395675869134312619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22957740930450579422875079 34436611395675869134312619)
          ·
            refine ⟨51654917093513803701468929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34436611395675869134312619 51654917093513803701468929)
            ·
              refine ⟨38741187820135352776101697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51654917093513803701468929 38741187820135352776101697)
              ·
                refine ⟨29055890865101514582076273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38741187820135352776101697 29055890865101514582076273)
                ·
                  refine ⟨21791918148826135936557205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29055890865101514582076273 21791918148826135936557205)
                  ·
                    refine ⟨1021496163226225122026119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21791918148826135936557205 1021496163226225122026119)
                    ·
                      rfl

theorem cell22_2984035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_2984035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984035 prefixEnd_2984035 := by exact prefixLift 2984035
  have htrace : WordTrace (prefixWord ++ tailWord_2984035) baseStart_2984035 baseEnd_2984035 := by
    simpa [prefixWord, tailWord_2984035, baseEnd_2984035] using wordTrace_append hprefix tailTrace_2984035
  have hstable : (prefixWord ++ tailWord_2984035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984035).length < 2 ^ (prefixWord ++ tailWord_2984035).sum := by decide
  have hdescent : baseEnd_2984035 < baseStart_2984035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984082 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2984082 : Nat := 118140960795 + 2984082 * 2 ^ 59
def prefixEnd_2984082 : Nat := 4983230072969 + 3 ^ 40 * 2984082 * 2
def baseEnd_2984082 : Nat := 1021512252286732666100975

theorem tailTrace_2984082 : CollatzResearch.WordTrace tailWord_2984082 prefixEnd_2984082 1021512252286732666100975 := by
  unfold tailWord_2984082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209602993797007369036625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72558941316792019650764333 27209602993797007369036625)
  ·
    refine ⟨20407202245347755526777469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27209602993797007369036625 20407202245347755526777469)
    ·
      refine ⟨7652700842005408322541551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20407202245347755526777469 7652700842005408322541551)
      ·
        refine ⟨11479051263008112483812327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7652700842005408322541551 11479051263008112483812327)
        ·
          refine ⟨17218576894512168725718491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11479051263008112483812327 17218576894512168725718491)
          ·
            refine ⟨25827865341768253088577737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17218576894512168725718491 25827865341768253088577737)
            ·
              refine ⟨19370899006326189816433303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25827865341768253088577737 19370899006326189816433303)
              ·
                refine ⟨29056348509489284724649955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19370899006326189816433303 29056348509489284724649955)
                ·
                  refine ⟨43584522764233927086974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29056348509489284724649955 43584522764233927086974933)
                  ·
                    refine ⟨1021512252286732666100975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43584522764233927086974933 1021512252286732666100975)
                    ·
                      rfl

theorem cell22_2984082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2984082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984082 prefixEnd_2984082 := by exact prefixLift 2984082
  have htrace : WordTrace (prefixWord ++ tailWord_2984082) baseStart_2984082 baseEnd_2984082 := by
    simpa [prefixWord, tailWord_2984082, baseEnd_2984082] using wordTrace_append hprefix tailTrace_2984082
  have hstable : (prefixWord ++ tailWord_2984082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984082).length < 2 ^ (prefixWord ++ tailWord_2984082).sum := by decide
  have hdescent : baseEnd_2984082 < baseStart_2984082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984163 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 4]
def baseStart_2984163 : Nat := 118140960795 + 2984163 * 2 ^ 59
def prefixEnd_2984163 : Nat := 4983230072969 + 3 ^ 40 * 2984163 * 2
def baseEnd_2984163 : Nat := 340513326747358484941909

theorem tailTrace_2984163 : CollatzResearch.WordTrace tailWord_2984163 prefixEnd_2984163 340513326747358484941909 := by
  unfold tailWord_2984163
  simp only [CollatzResearch.WordTrace]
  refine ⟨108841366287894580309845143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72560910858596386873230095 108841366287894580309845143)
  ·
    refine ⟨163262049431841870464767715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108841366287894580309845143 163262049431841870464767715)
    ·
      refine ⟨244893074147762805697151573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163262049431841870464767715 244893074147762805697151573)
      ·
        refine ⟨2869840712669095379263495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 244893074147762805697151573 2869840712669095379263495)
        ·
          refine ⟨4304761069003643068895243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869840712669095379263495 4304761069003643068895243)
          ·
            refine ⟨6457141603505464603342865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304761069003643068895243 6457141603505464603342865)
            ·
              refine ⟨4842856202629098452507149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6457141603505464603342865 4842856202629098452507149)
              ·
                refine ⟨1816071075985911919690181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4842856202629098452507149 1816071075985911919690181)
                ·
                  refine ⟨340513326747358484941909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816071075985911919690181 340513326747358484941909)
                  ·
                    rfl

theorem cell22_2984163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 4].length) (baseStart_2984163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984163 prefixEnd_2984163 := by exact prefixLift 2984163
  have htrace : WordTrace (prefixWord ++ tailWord_2984163) baseStart_2984163 baseEnd_2984163 := by
    simpa [prefixWord, tailWord_2984163, baseEnd_2984163] using wordTrace_append hprefix tailTrace_2984163
  have hstable : (prefixWord ++ tailWord_2984163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984163).length < 2 ^ (prefixWord ++ tailWord_2984163).sum := by decide
  have hdescent : baseEnd_2984163 < baseStart_2984163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984178 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2984178 : Nat := 118140960795 + 2984178 * 2 ^ 59
def prefixEnd_2984178 : Nat := 4983230072969 + 3 ^ 40 * 2984178 * 2
def baseEnd_2984178 : Nat := 1021545115048620415700681

theorem tailTrace_2984178 : CollatzResearch.WordTrace tailWord_2984178 prefixEnd_2984178 1021545115048620415700681 := by
  unfold tailWord_2984178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27210478345710059467910297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72561275588560158581094125 27210478345710059467910297)
  ·
    refine ⟨20407858759282544600932723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27210478345710059467910297 20407858759282544600932723)
    ·
      refine ⟨30611788138923816901399085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20407858759282544600932723 30611788138923816901399085)
      ·
        refine ⟨11479420552096431338024657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30611788138923816901399085 11479420552096431338024657)
        ·
          refine ⟨8609565414072323503518493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11479420552096431338024657 8609565414072323503518493)
          ·
            refine ⟨3228587030277121313819435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8609565414072323503518493 3228587030277121313819435)
            ·
              refine ⟨4842880545415681970729153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228587030277121313819435 4842880545415681970729153)
              ·
                refine ⟨3632160409061761478046865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842880545415681970729153 3632160409061761478046865)
                ·
                  refine ⟨2724120306796321108535149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3632160409061761478046865 2724120306796321108535149)
                  ·
                    refine ⟨1021545115048620415700681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724120306796321108535149 1021545115048620415700681)
                    ·
                      rfl

theorem cell22_2984178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2984178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984178 prefixEnd_2984178 := by exact prefixLift 2984178
  have htrace : WordTrace (prefixWord ++ tailWord_2984178) baseStart_2984178 baseEnd_2984178 := by
    simpa [prefixWord, tailWord_2984178, baseEnd_2984178] using wordTrace_append hprefix tailTrace_2984178
  have hstable : (prefixWord ++ tailWord_2984178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984178).length < 2 ^ (prefixWord ++ tailWord_2984178).sum := by decide
  have hdescent : baseEnd_2984178 < baseStart_2984178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984223 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 1, 3]
def baseStart_2984223 : Nat := 118140960795 + 2984223 * 2 ^ 59
def prefixEnd_2984223 : Nat := 4983230072969 + 3 ^ 40 * 2984223 * 2
def baseEnd_2984223 : Nat := 1021560519468255298325543

theorem tailTrace_2984223 : CollatzResearch.WordTrace tailWord_2984223 prefixEnd_2984223 1021560519468255298325543 := by
  unfold tailWord_2984223
  simp only [CollatzResearch.WordTrace]
  refine ⟨108843554667677210557029323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72562369778451473704686215 108843554667677210557029323)
  ·
    refine ⟨163265332001515815835543985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108843554667677210557029323 163265332001515815835543985)
    ·
      refine ⟨122448999001136861876657989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163265332001515815835543985 122448999001136861876657989)
      ·
        refine ⟨22959187312713161601873373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122448999001136861876657989 22959187312713161601873373)
        ·
          refine ⟨8609695242267435600702515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22959187312713161601873373 8609695242267435600702515)
          ·
            refine ⟨12914542863401153401053773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609695242267435600702515 12914542863401153401053773)
            ·
              refine ⟨4842953573775432525395165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12914542863401153401053773 4842953573775432525395165)
              ·
                refine ⟨1816107590165787197023187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4842953573775432525395165 1816107590165787197023187)
                ·
                  refine ⟨2724161385248680795534781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816107590165787197023187 2724161385248680795534781)
                  ·
                    refine ⟨1021560519468255298325543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724161385248680795534781 1021560519468255298325543)
                    ·
                      rfl

theorem cell22_2984223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_2984223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984223 prefixEnd_2984223 := by exact prefixLift 2984223
  have htrace : WordTrace (prefixWord ++ tailWord_2984223) baseStart_2984223 baseEnd_2984223 := by
    simpa [prefixWord, tailWord_2984223, baseEnd_2984223] using wordTrace_append hprefix tailTrace_2984223
  have hstable : (prefixWord ++ tailWord_2984223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984223).length < 2 ^ (prefixWord ++ tailWord_2984223).sum := by decide
  have hdescent : baseEnd_2984223 < baseStart_2984223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984279 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 1, 5]
def baseStart_2984279 : Nat := 118140960795 + 2984279 * 2 ^ 59
def prefixEnd_2984279 : Nat := 4983230072969 + 3 ^ 40 * 2984279 * 2
def baseEnd_2984279 : Nat := 1021579689412689818925371

theorem tailTrace_2984279 : CollatzResearch.WordTrace tailWord_2984279 prefixEnd_2984279 1021579689412689818925371 := by
  unfold tailWord_2984279
  simp only [CollatzResearch.WordTrace]
  refine ⟨108845597155474332121067891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72563731436982888080711927 108845597155474332121067891)
  ·
    refine ⟨163268395733211498181601837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108845597155474332121067891 163268395733211498181601837)
    ·
      refine ⟨61225648399954311818100689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163268395733211498181601837 61225648399954311818100689)
      ·
        refine ⟨45919236299965733863575517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61225648399954311818100689 45919236299965733863575517)
        ·
          refine ⟨17219713612487150198840819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45919236299965733863575517 17219713612487150198840819)
          ·
            refine ⟨25829570418730725298261229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17219713612487150198840819 25829570418730725298261229)
            ·
              refine ⟨9686088907024021986847961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25829570418730725298261229 9686088907024021986847961)
              ·
                refine ⟨7264566680268016490135971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9686088907024021986847961 7264566680268016490135971)
                ·
                  refine ⟨10896850020402024735203957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7264566680268016490135971 10896850020402024735203957)
                  ·
                    refine ⟨1021579689412689818925371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10896850020402024735203957 1021579689412689818925371)
                    ·
                      rfl

theorem cell22_2984279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_2984279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984279 prefixEnd_2984279 := by exact prefixLift 2984279
  have htrace : WordTrace (prefixWord ++ tailWord_2984279) baseStart_2984279 baseEnd_2984279 := by
    simpa [prefixWord, tailWord_2984279, baseEnd_2984279] using wordTrace_append hprefix tailTrace_2984279
  have hstable : (prefixWord ++ tailWord_2984279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984279).length < 2 ^ (prefixWord ++ tailWord_2984279).sum := by decide
  have hdescent : baseEnd_2984279 < baseStart_2984279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984298 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_2984298 : Nat := 118140960795 + 2984298 * 2 ^ 59
def prefixEnd_2984298 : Nat := 4983230072969 + 3 ^ 40 * 2984298 * 2
def baseEnd_2984298 : Nat := 340528731166993367566771

theorem tailTrace_2984298 : CollatzResearch.WordTrace tailWord_2984298 prefixEnd_2984298 340528731166993367566771 := by
  unfold tailWord_2984298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211572535601374591502387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72564193428270332244006365 27211572535601374591502387)
  ·
    refine ⟨40817358803402061887253581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27211572535601374591502387 40817358803402061887253581)
    ·
      refine ⟨15306509551275773207720093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40817358803402061887253581 15306509551275773207720093)
      ·
        refine ⟨5739941081728414952895035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15306509551275773207720093 5739941081728414952895035)
        ·
          refine ⟨8609911622592622429342553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739941081728414952895035 8609911622592622429342553)
          ·
            refine ⟨6457433716944466822006915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8609911622592622429342553 6457433716944466822006915)
            ·
              refine ⟨9686150575416700233010373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457433716944466822006915 9686150575416700233010373)
              ·
                refine ⟨1816153232890631293689445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9686150575416700233010373 1816153232890631293689445)
                ·
                  refine ⟨340528731166993367566771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816153232890631293689445 340528731166993367566771)
                  ·
                    rfl

theorem cell22_2984298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_2984298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984298 prefixEnd_2984298 := by exact prefixLift 2984298
  have htrace : WordTrace (prefixWord ++ tailWord_2984298) baseStart_2984298 baseEnd_2984298 := by
    simpa [prefixWord, tailWord_2984298, baseEnd_2984298] using wordTrace_append hprefix tailTrace_2984298
  have hstable : (prefixWord ++ tailWord_2984298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984298).length < 2 ^ (prefixWord ++ tailWord_2984298).sum := by decide
  have hdescent : baseEnd_2984298 < baseStart_2984298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984516 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2984516 : Nat := 118140960795 + 2984516 * 2 ^ 59
def prefixEnd_2984516 : Nat := 4983230072969 + 3 ^ 40 * 2984516 * 2
def baseEnd_2984516 : Nat := 1021660819356100200749645

theorem tailTrace_2984516 : CollatzResearch.WordTrace tailWord_2984516 prefixEnd_2984516 1021660819356100200749645 := by
  unfold tailWord_2984516
  simp only [CollatzResearch.WordTrace]
  refine ⟨54427120627807860798722701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72569494170410481064963601 54427120627807860798722701)
  ·
    refine ⟨20410170235427947799521013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54427120627807860798722701 20410170235427947799521013)
    ·
      refine ⟨1913453459571370106205095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20410170235427947799521013 1913453459571370106205095)
      ·
        refine ⟨2870180189357055159307643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913453459571370106205095 2870180189357055159307643)
        ·
          refine ⟨4305270284035582738961465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870180189357055159307643 4305270284035582738961465)
          ·
            refine ⟨3228952713026687054221099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4305270284035582738961465 3228952713026687054221099)
            ·
              refine ⟨4843429069540030581331649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228952713026687054221099 4843429069540030581331649)
              ·
                refine ⟨3632571802155022935998737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4843429069540030581331649 3632571802155022935998737)
                ·
                  refine ⟨2724428851616267201999053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3632571802155022935998737 2724428851616267201999053)
                  ·
                    refine ⟨1021660819356100200749645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724428851616267201999053 1021660819356100200749645)
                    ·
                      rfl

theorem cell22_2984516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2984516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984516 prefixEnd_2984516 := by exact prefixLift 2984516
  have htrace : WordTrace (prefixWord ++ tailWord_2984516) baseStart_2984516 baseEnd_2984516 := by
    simpa [prefixWord, tailWord_2984516, baseEnd_2984516] using wordTrace_append hprefix tailTrace_2984516
  have hstable : (prefixWord ++ tailWord_2984516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984516).length < 2 ^ (prefixWord ++ tailWord_2984516).sum := by decide
  have hdescent : baseEnd_2984516 < baseStart_2984516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984536 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_2984536 : Nat := 118140960795 + 2984536 * 2 ^ 59
def prefixEnd_2984536 : Nat := 4983230072969 + 3 ^ 40 * 2984536 * 2
def baseEnd_2984536 : Nat := 1021667665764826815249583

theorem tailTrace_2984536 : CollatzResearch.WordTrace tailWord_2984536 prefixEnd_2984536 1021667665764826815249583 := by
  unfold tailWord_2984536
  simp only [CollatzResearch.WordTrace]
  refine ⟨54427485357771632506586731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72569980477028843342115641 54427485357771632506586731)
  ·
    refine ⟨81641228036657448759880097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54427485357771632506586731 81641228036657448759880097)
    ·
      refine ⟨61230921027493086569910073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81641228036657448759880097 61230921027493086569910073)
      ·
        refine ⟨45923190770619814927432555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61230921027493086569910073 45923190770619814927432555)
        ·
          refine ⟨68884786155929722391148833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45923190770619814927432555 68884786155929722391148833)
          ·
            refine ⟨51663589616947291793361625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68884786155929722391148833 51663589616947291793361625)
            ·
              refine ⟨38747692212710468845021219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51663589616947291793361625 38747692212710468845021219)
              ·
                refine ⟨58121538319065703267531829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38747692212710468845021219 58121538319065703267531829)
                ·
                  refine ⟨5448894217412409681331109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58121538319065703267531829 5448894217412409681331109)
                  ·
                    refine ⟨1021667665764826815249583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5448894217412409681331109 1021667665764826815249583)
                    ·
                      rfl

theorem cell22_2984536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_2984536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984536 prefixEnd_2984536 := by exact prefixLift 2984536
  have htrace : WordTrace (prefixWord ++ tailWord_2984536) baseStart_2984536 baseEnd_2984536 := by
    simpa [prefixWord, tailWord_2984536, baseEnd_2984536] using wordTrace_append hprefix tailTrace_2984536
  have hstable : (prefixWord ++ tailWord_2984536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984536).length < 2 ^ (prefixWord ++ tailWord_2984536).sum := by decide
  have hdescent : baseEnd_2984536 < baseStart_2984536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984578 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2984578 : Nat := 118140960795 + 2984578 * 2 ^ 59
def prefixEnd_2984578 : Nat := 4983230072969 + 3 ^ 40 * 2984578 * 2
def baseEnd_2984578 : Nat := 1021682043223152705699455

theorem tailTrace_2984578 : CollatzResearch.WordTrace tailWord_2984578 prefixEnd_2984578 1021682043223152705699455 := by
  unfold tailWord_2984578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214125645347776546550597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72571001720927404124134925 27214125645347776546550597)
  ·
    refine ⟨5102648558502708102478237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27214125645347776546550597 5102648558502708102478237)
    ·
      refine ⟨1913493209438515538429339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5102648558502708102478237 1913493209438515538429339)
      ·
        refine ⟨2870239814157773307644009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913493209438515538429339 2870239814157773307644009)
        ·
          refine ⟨2152679860618329980733007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2870239814157773307644009 2152679860618329980733007)
          ·
            refine ⟨3229019790927494971099511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152679860618329980733007 3229019790927494971099511)
            ·
              refine ⟨4843529686391242456649267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3229019790927494971099511 4843529686391242456649267)
              ·
                refine ⟨7265294529586863684973901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843529686391242456649267 7265294529586863684973901)
                ·
                  refine ⟨2724485448595073881865213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7265294529586863684973901 2724485448595073881865213)
                  ·
                    refine ⟨1021682043223152705699455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724485448595073881865213 1021682043223152705699455)
                    ·
                      rfl

theorem cell22_2984578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2984578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984578 prefixEnd_2984578 := by exact prefixLift 2984578
  have htrace : WordTrace (prefixWord ++ tailWord_2984578) baseStart_2984578 baseEnd_2984578 := by
    simpa [prefixWord, tailWord_2984578, baseEnd_2984578] using wordTrace_append hprefix tailTrace_2984578
  have hstable : (prefixWord ++ tailWord_2984578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984578).length < 2 ^ (prefixWord ++ tailWord_2984578).sum := by decide
  have hdescent : baseEnd_2984578 < baseStart_2984578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984583 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 4, 3]
def baseStart_2984583 : Nat := 118140960795 + 2984583 * 2 ^ 59
def prefixEnd_2984583 : Nat := 4983230072969 + 3 ^ 40 * 2984583 * 2
def baseEnd_2984583 : Nat := 1021683754825334359324439

theorem tailTrace_2984583 : CollatzResearch.WordTrace tailWord_2984583 prefixEnd_2984583 1021683754825334359324439 := by
  unfold tailWord_2984583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108856684946372992040134403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72571123297581994693422935 108856684946372992040134403)
  ·
    refine ⟨163285027419559488060201605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108856684946372992040134403 163285027419559488060201605)
    ·
      refine ⟨30615942641167404011287801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163285027419559488060201605 30615942641167404011287801)
      ·
        refine ⟨22961956980875553008465851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30615942641167404011287801 22961956980875553008465851)
        ·
          refine ⟨34442935471313329512698777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22961956980875553008465851 34442935471313329512698777)
          ·
            refine ⟨25832201603484997134524083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34442935471313329512698777 25832201603484997134524083)
            ·
              refine ⟨38748302405227495701786125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25832201603484997134524083 38748302405227495701786125)
              ·
                refine ⟨14530613401960310888169797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38748302405227495701786125 14530613401960310888169797)
                ·
                  refine ⟨2724490012867558291531837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14530613401960310888169797 2724490012867558291531837)
                  ·
                    refine ⟨1021683754825334359324439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724490012867558291531837 1021683754825334359324439)
                    ·
                      rfl

theorem cell22_2984583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_2984583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984583 prefixEnd_2984583 := by exact prefixLift 2984583
  have htrace : WordTrace (prefixWord ++ tailWord_2984583) baseStart_2984583 baseEnd_2984583 := by
    simpa [prefixWord, tailWord_2984583, baseEnd_2984583] using wordTrace_append hprefix tailTrace_2984583
  have hstable : (prefixWord ++ tailWord_2984583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984583).length < 2 ^ (prefixWord ++ tailWord_2984583).sum := by decide
  have hdescent : baseEnd_2984583 < baseStart_2984583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984600 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_2984600 : Nat := 118140960795 + 2984600 * 2 ^ 59
def prefixEnd_2984600 : Nat := 4983230072969 + 3 ^ 40 * 2984600 * 2
def baseEnd_2984600 : Nat := 1021689574272751981649387

theorem tailTrace_2984600 : CollatzResearch.WordTrace tailWord_2984600 prefixEnd_2984600 1021689574272751981649387 := by
  unfold tailWord_2984600
  simp only [CollatzResearch.WordTrace]
  refine ⟨54428652493655701971751627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72571536658207602629002169 54428652493655701971751627)
  ·
    refine ⟨81642978740483552957627441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54428652493655701971751627 81642978740483552957627441)
    ·
      refine ⟨61232234055362664718220581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81642978740483552957627441 61232234055362664718220581)
      ·
        refine ⟨11481043885380499634666359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61232234055362664718220581 11481043885380499634666359)
        ·
          refine ⟨17221565828070749451999539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11481043885380499634666359 17221565828070749451999539)
          ·
            refine ⟨25832348742106124177999309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17221565828070749451999539 25832348742106124177999309)
            ·
              refine ⟨9687130778289796566749741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25832348742106124177999309 9687130778289796566749741)
              ·
                refine ⟨3632674041858673712531153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9687130778289796566749741 3632674041858673712531153)
                ·
                  refine ⟨2724505531394005284398365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3632674041858673712531153 2724505531394005284398365)
                  ·
                    refine ⟨1021689574272751981649387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724505531394005284398365 1021689574272751981649387)
                    ·
                      rfl

theorem cell22_2984600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_2984600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984600 prefixEnd_2984600 := by exact prefixLift 2984600
  have htrace : WordTrace (prefixWord ++ tailWord_2984600) baseStart_2984600 baseEnd_2984600 := by
    simpa [prefixWord, tailWord_2984600, baseEnd_2984600] using wordTrace_append hprefix tailTrace_2984600
  have hstable : (prefixWord ++ tailWord_2984600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984600).length < 2 ^ (prefixWord ++ tailWord_2984600).sum := by decide
  have hdescent : baseEnd_2984600 < baseStart_2984600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984630 : List Nat := [5, 1, 3, 1, 2, 10]
def baseStart_2984630 : Nat := 118140960795 + 2984630 * 2 ^ 59
def prefixEnd_2984630 : Nat := 4983230072969 + 3 ^ 40 * 2984630 * 2
def baseEnd_2984630 : Nat := 12613578319578295103695

theorem tailTrace_2984630 : CollatzResearch.WordTrace tailWord_2984630 prefixEnd_2984630 12613578319578295103695 := by
  unfold tailWord_2984630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6803649948575169941693459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72572266118135146044730229 6803649948575169941693459)
  ·
    refine ⟨10205474922862754912540189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6803649948575169941693459 10205474922862754912540189)
    ·
      refine ⟨3827053096073533092202571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10205474922862754912540189 3827053096073533092202571)
      ·
        refine ⟨5740579644110299638303857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827053096073533092202571 5740579644110299638303857)
        ·
          refine ⟨4305434733082724728727893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5740579644110299638303857 4305434733082724728727893)
          ·
            refine ⟨12613578319578295103695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4305434733082724728727893 12613578319578295103695)
            ·
              rfl

theorem cell22_2984630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 10].length) (baseStart_2984630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984630 prefixEnd_2984630 := by exact prefixLift 2984630
  have htrace : WordTrace (prefixWord ++ tailWord_2984630) baseStart_2984630 baseEnd_2984630 := by
    simpa [prefixWord, tailWord_2984630, baseEnd_2984630] using wordTrace_append hprefix tailTrace_2984630
  have hstable : (prefixWord ++ tailWord_2984630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984630).length < 2 ^ (prefixWord ++ tailWord_2984630).sum := by decide
  have hdescent : baseEnd_2984630 < baseStart_2984630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984735 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 4, 3]
def baseStart_2984735 : Nat := 118140960795 + 2984735 * 2 ^ 59
def prefixEnd_2984735 : Nat := 4983230072969 + 3 ^ 40 * 2984735 * 2
def baseEnd_2984735 : Nat := 1021735787531656629523973

theorem tailTrace_2984735 : CollatzResearch.WordTrace tailWord_2984735 prefixEnd_2984735 1021735787531656629523973 := by
  unfold tailWord_2984735
  simp only [CollatzResearch.WordTrace]
  refine ⟨108862228841822321999667659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72574819227881547999778439 108862228841822321999667659)
  ·
    refine ⟨163293343262733482999501489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108862228841822321999667659 163293343262733482999501489)
    ·
      refine ⟨122470007447050112249626117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163293343262733482999501489 122470007447050112249626117)
      ·
        refine ⟨22963126396321896046804897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122470007447050112249626117 22963126396321896046804897)
        ·
          refine ⟨17222344797241422035103673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22963126396321896046804897 17222344797241422035103673)
          ·
            refine ⟨12916758597931066526327755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17222344797241422035103673 12916758597931066526327755)
            ·
              refine ⟨19375137896896599789491633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12916758597931066526327755 19375137896896599789491633)
              ·
                refine ⟨14531353422672449842118725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19375137896896599789491633 14531353422672449842118725)
                ·
                  refine ⟨2724628766751084345397261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14531353422672449842118725 2724628766751084345397261)
                  ·
                    refine ⟨1021735787531656629523973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724628766751084345397261 1021735787531656629523973)
                    ·
                      rfl

theorem cell22_2984735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_2984735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984735 prefixEnd_2984735 := by exact prefixLift 2984735
  have htrace : WordTrace (prefixWord ++ tailWord_2984735) baseStart_2984735 baseEnd_2984735 := by
    simpa [prefixWord, tailWord_2984735, baseEnd_2984735] using wordTrace_append hprefix tailTrace_2984735
  have hstable : (prefixWord ++ tailWord_2984735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984735).length < 2 ^ (prefixWord ++ tailWord_2984735).sum := by decide
  have hdescent : baseEnd_2984735 < baseStart_2984735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984778 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2984778 : Nat := 118140960795 + 2984778 * 2 ^ 59
def prefixEnd_2984778 : Nat := 4983230072969 + 3 ^ 40 * 2984778 * 2
def baseEnd_2984778 : Nat := 1021750507310418850698841

theorem tailTrace_2984778 : CollatzResearch.WordTrace tailWord_2984778 prefixEnd_2984778 1021750507310418850698841 := by
  unfold tailWord_2984778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27215949295166635085870747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72575864787111026895655325 27215949295166635085870747)
  ·
    refine ⟨40823923942749952628806121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27215949295166635085870747 40823923942749952628806121)
    ·
      refine ⟨30617942957062464471604591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40823923942749952628806121 30617942957062464471604591)
      ·
        refine ⟨45926914435593696707406887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30617942957062464471604591 45926914435593696707406887)
        ·
          refine ⟨68890371653390545061110331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45926914435593696707406887 68890371653390545061110331)
          ·
            refine ⟨103335557480085817591665497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68890371653390545061110331 103335557480085817591665497)
            ·
              refine ⟨77501668110064363193749123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103335557480085817591665497 77501668110064363193749123)
              ·
                refine ⟨116252502165096544790623685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77501668110064363193749123 116252502165096544790623685)
                ·
                  refine ⟨21797344155955602148241941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116252502165096544790623685 21797344155955602148241941)
                  ·
                    refine ⟨1021750507310418850698841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21797344155955602148241941 1021750507310418850698841)
                    ·
                      rfl

theorem cell22_2984778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2984778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984778 prefixEnd_2984778 := by exact prefixLift 2984778
  have htrace : WordTrace (prefixWord ++ tailWord_2984778) baseStart_2984778 baseEnd_2984778 := by
    simpa [prefixWord, tailWord_2984778, baseEnd_2984778] using wordTrace_append hprefix tailTrace_2984778
  have hstable : (prefixWord ++ tailWord_2984778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984778).length < 2 ^ (prefixWord ++ tailWord_2984778).sum := by decide
  have hdescent : baseEnd_2984778 < baseStart_2984778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984825 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_2984825 : Nat := 118140960795 + 2984825 * 2 ^ 59
def prefixEnd_2984825 : Nat := 4983230072969 + 3 ^ 40 * 2984825 * 2
def baseEnd_2984825 : Nat := 1021766596370926394773697

theorem tailTrace_2984825 : CollatzResearch.WordTrace tailWord_2984825 prefixEnd_2984825 1021766596370926394773697 := by
  unfold tailWord_2984825
  simp only [CollatzResearch.WordTrace]
  refine ⟨108865511411496267370443929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72577007607664178246962619 108865511411496267370443929)
  ·
    refine ⟨81649133558622200527832947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108865511411496267370443929 81649133558622200527832947)
    ·
      refine ⟨122473700337933300791749421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81649133558622200527832947 122473700337933300791749421)
      ·
        refine ⟨45927637626724987796906033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122473700337933300791749421 45927637626724987796906033)
        ·
          refine ⟨34445728220043740847679525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45927637626724987796906033 34445728220043740847679525)
          ·
            refine ⟨6458574041258201408939911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34445728220043740847679525 6458574041258201408939911)
            ·
              refine ⟨9687861061887302113409867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458574041258201408939911 9687861061887302113409867)
              ·
                refine ⟨14531791592830953170114801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687861061887302113409867 14531791592830953170114801)
                ·
                  refine ⟨10898843694623214877586101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14531791592830953170114801 10898843694623214877586101)
                  ·
                    refine ⟨1021766596370926394773697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10898843694623214877586101 1021766596370926394773697)
                    ·
                      rfl

theorem cell22_2984825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_2984825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984825 prefixEnd_2984825 := by exact prefixLift 2984825
  have htrace : WordTrace (prefixWord ++ tailWord_2984825) baseStart_2984825 baseEnd_2984825 := by
    simpa [prefixWord, tailWord_2984825, baseEnd_2984825] using wordTrace_append hprefix tailTrace_2984825
  have hstable : (prefixWord ++ tailWord_2984825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984825).length < 2 ^ (prefixWord ++ tailWord_2984825).sum := by decide
  have hdescent : baseEnd_2984825 < baseStart_2984825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984885 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2984885 : Nat := 118140960795 + 2984885 * 2 ^ 59
def prefixEnd_2984885 : Nat := 4983230072969 + 3 ^ 40 * 2984885 * 2
def baseEnd_2984885 : Nat := 1021787135597106238273513

theorem tailTrace_2984885 : CollatzResearch.WordTrace tailWord_2984885 prefixEnd_2984885 1021787135597106238273513 := by
  unfold tailWord_2984885
  simp only [CollatzResearch.WordTrace]
  refine ⟨108867699791278897617628109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72578466527519265078418739 108867699791278897617628109)
  ·
    refine ⟨40825387421729586606610541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108867699791278897617628109 40825387421729586606610541)
    ·
      refine ⟨15309520283148594977478953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40825387421729586606610541 15309520283148594977478953)
      ·
        refine ⟨11482140212361446233109215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15309520283148594977478953 11482140212361446233109215)
        ·
          refine ⟨17223210318542169349663823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11482140212361446233109215 17223210318542169349663823)
          ·
            refine ⟨25834815477813254024495735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17223210318542169349663823 25834815477813254024495735)
            ·
              refine ⟨38752223216719881036743603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25834815477813254024495735 38752223216719881036743603)
              ·
                refine ⟨58128334825079821555115405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38752223216719881036743603 58128334825079821555115405)
                ·
                  refine ⟨21798125559404933083168277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58128334825079821555115405 21798125559404933083168277)
                  ·
                    refine ⟨1021787135597106238273513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21798125559404933083168277 1021787135597106238273513)
                    ·
                      rfl

theorem cell22_2984885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2984885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984885 prefixEnd_2984885 := by exact prefixLift 2984885
  have htrace : WordTrace (prefixWord ++ tailWord_2984885) baseStart_2984885 baseEnd_2984885 := by
    simpa [prefixWord, tailWord_2984885, baseEnd_2984885] using wordTrace_append hprefix tailTrace_2984885
  have hstable : (prefixWord ++ tailWord_2984885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984885).length < 2 ^ (prefixWord ++ tailWord_2984885).sum := by decide
  have hdescent : baseEnd_2984885 < baseStart_2984885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984887 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 2, 3]
def baseStart_2984887 : Nat := 118140960795 + 2984887 * 2 ^ 59
def prefixEnd_2984887 : Nat := 4983230072969 + 3 ^ 40 * 2984887 * 2
def baseEnd_2984887 : Nat := 1021787820237978899723507

theorem tailTrace_2984887 : CollatzResearch.WordTrace tailWord_2984887 prefixEnd_2984887 1021787820237978899723507 := by
  unfold tailWord_2984887
  simp only [CollatzResearch.WordTrace]
  refine ⟨108867772737271651959200915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72578515158181101306133943 108867772737271651959200915)
  ·
    refine ⟨163301659105907477938801373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108867772737271651959200915 163301659105907477938801373)
    ·
      refine ⟨61238122164715304227050515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163301659105907477938801373 61238122164715304227050515)
      ·
        refine ⟨91857183247072956340575773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61238122164715304227050515 91857183247072956340575773)
        ·
          refine ⟨34446443717652358627715915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91857183247072956340575773 34446443717652358627715915)
          ·
            refine ⟨51669665576478537941573873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34446443717652358627715915 51669665576478537941573873)
            ·
              refine ⟨38752249182358903456180405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51669665576478537941573873 38752249182358903456180405)
              ·
                refine ⟨3633023360846147199016913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38752249182358903456180405 3633023360846147199016913)
                ·
                  refine ⟨2724767520634610399262685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3633023360846147199016913 2724767520634610399262685)
                  ·
                    refine ⟨1021787820237978899723507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724767520634610399262685 1021787820237978899723507)
                    ·
                      rfl

theorem cell22_2984887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_2984887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984887 prefixEnd_2984887 := by exact prefixLift 2984887
  have htrace : WordTrace (prefixWord ++ tailWord_2984887) baseStart_2984887 baseEnd_2984887 := by
    simpa [prefixWord, tailWord_2984887, baseEnd_2984887] using wordTrace_append hprefix tailTrace_2984887
  have hstable : (prefixWord ++ tailWord_2984887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984887).length < 2 ^ (prefixWord ++ tailWord_2984887).sum := by decide
  have hdescent : baseEnd_2984887 < baseStart_2984887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984917 : List Nat := [1, 3, 2, 3, 3, 2, 8]
def baseStart_2984917 : Nat := 118140960795 + 2984917 * 2 ^ 59
def prefixEnd_2984917 : Nat := 4983230072969 + 3 ^ 40 * 2984917 * 2
def baseEnd_2984917 : Nat := 37844373698187734128645

theorem tailTrace_2984917 : CollatzResearch.WordTrace tailWord_2984917 prefixEnd_2984917 37844373698187734128645 := by
  unfold tailWord_2984917
  simp only [CollatzResearch.WordTrace]
  refine ⟨108868866927162967082793005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72579244618108644721862003 108868866927162967082793005)
  ·
    refine ⟨40825825097686112656047377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108868866927162967082793005 40825825097686112656047377)
    ·
      refine ⟨30619368823264584492035533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40825825097686112656047377 30619368823264584492035533)
      ·
        refine ⟨11482263308724219184513325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30619368823264584492035533 11482263308724219184513325)
        ·
          refine ⟨4305848740771582194192497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11482263308724219184513325 4305848740771582194192497)
          ·
            refine ⟨3229386555578686645644373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4305848740771582194192497 3229386555578686645644373)
            ·
              refine ⟨37844373698187734128645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3229386555578686645644373 37844373698187734128645)
              ·
                rfl

theorem cell22_2984917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 8].length) (baseStart_2984917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984917 prefixEnd_2984917 := by exact prefixLift 2984917
  have htrace : WordTrace (prefixWord ++ tailWord_2984917) baseStart_2984917 baseEnd_2984917 := by
    simpa [prefixWord, tailWord_2984917, baseEnd_2984917] using wordTrace_append hprefix tailTrace_2984917
  have hstable : (prefixWord ++ tailWord_2984917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984917).length < 2 ^ (prefixWord ++ tailWord_2984917).sum := by decide
  have hdescent : baseEnd_2984917 < baseStart_2984917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984932 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_2984932 : Nat := 118140960795 + 2984932 * 2 ^ 59
def prefixEnd_2984932 : Nat := 4983230072969 + 3 ^ 40 * 2984932 * 2
def baseEnd_2984932 : Nat := 1021803224657613782348369

theorem tailTrace_2984932 : CollatzResearch.WordTrace tailWord_2984932 prefixEnd_2984932 1021803224657613782348369 := by
  unfold tailWord_2984932
  simp only [CollatzResearch.WordTrace]
  refine ⟨54434707011054312322294525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72579609348072416429726033 54434707011054312322294525)
  ·
    refine ⟨20413015129145367120860447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54434707011054312322294525 20413015129145367120860447)
    ·
      refine ⟨30619522693718050681290671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20413015129145367120860447 30619522693718050681290671)
      ·
        refine ⟨45929284040577076021936007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30619522693718050681290671 45929284040577076021936007)
        ·
          refine ⟨68893926060865614032904011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45929284040577076021936007 68893926060865614032904011)
          ·
            refine ⟨103340889091298421049356017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68893926060865614032904011 103340889091298421049356017)
            ·
              refine ⟨77505666818473815787017013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103340889091298421049356017 77505666818473815787017013)
              ·
                refine ⟨7266156264231920230032845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77505666818473815787017013 7266156264231920230032845)
                ·
                  refine ⟨2724808599086970086262317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7266156264231920230032845 2724808599086970086262317)
                  ·
                    refine ⟨1021803224657613782348369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724808599086970086262317 1021803224657613782348369)
                    ·
                      rfl

theorem cell22_2984932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_2984932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984932 prefixEnd_2984932 := by exact prefixLift 2984932
  have htrace : WordTrace (prefixWord ++ tailWord_2984932) baseStart_2984932 baseEnd_2984932 := by
    simpa [prefixWord, tailWord_2984932, baseEnd_2984932] using wordTrace_append hprefix tailTrace_2984932
  have hstable : (prefixWord ++ tailWord_2984932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984932).length < 2 ^ (prefixWord ++ tailWord_2984932).sum := by decide
  have hdescent : baseEnd_2984932 < baseStart_2984932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984983 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 1, 3]
def baseStart_2984983 : Nat := 118140960795 + 2984983 * 2 ^ 59
def prefixEnd_2984983 : Nat := 4983230072969 + 3 ^ 40 * 2984983 * 2
def baseEnd_2984983 : Nat := 1021820682999866649323213

theorem tailTrace_2984983 : CollatzResearch.WordTrace tailWord_2984983 prefixEnd_2984983 1021820682999866649323213 := by
  unfold tailWord_2984983
  simp only [CollatzResearch.WordTrace]
  refine ⟨108871274144923860354695603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72580849429949240236463735 108871274144923860354695603)
  ·
    refine ⟨163306911217385790532043405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108871274144923860354695603 163306911217385790532043405)
    ·
      refine ⟨61240091706519671449516277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163306911217385790532043405 61240091706519671449516277)
      ·
        refine ⟨5741258597486219198392151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61240091706519671449516277 5741258597486219198392151)
        ·
          refine ⟨8611887896229328797588227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741258597486219198392151 8611887896229328797588227)
          ·
            refine ⟨12917831844343993196382341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8611887896229328797588227 12917831844343993196382341)
            ·
              refine ⟨2422093470814498724321689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12917831844343993196382341 2422093470814498724321689)
              ·
                refine ⟨1816570103110874043241267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422093470814498724321689 1816570103110874043241267)
                ·
                  refine ⟨2724855154666311064861901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816570103110874043241267 2724855154666311064861901)
                  ·
                    refine ⟨1021820682999866649323213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724855154666311064861901 1021820682999866649323213)
                    ·
                      rfl

theorem cell22_2984983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_2984983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2984983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2984983 prefixEnd_2984983 := by exact prefixLift 2984983
  have htrace : WordTrace (prefixWord ++ tailWord_2984983) baseStart_2984983 baseEnd_2984983 := by
    simpa [prefixWord, tailWord_2984983, baseEnd_2984983] using wordTrace_append hprefix tailTrace_2984983
  have hstable : (prefixWord ++ tailWord_2984983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984983).length < 2 ^ (prefixWord ++ tailWord_2984983).sum := by decide
  have hdescent : baseEnd_2984983 < baseStart_2984983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985024 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 4]
def baseStart_2985024 : Nat := 118140960795 + 2985024 * 2 ^ 59
def prefixEnd_2985024 : Nat := 4983230072969 + 3 ^ 40 * 2985024 * 2
def baseEnd_2985024 : Nat := 340611572712585403016029

theorem tailTrace_2985024 : CollatzResearch.WordTrace tailWord_2985024 prefixEnd_2985024 340611572712585403016029 := by
  unfold tailWord_2985024
  simp only [CollatzResearch.WordTrace]
  refine ⟨54436384768887662178469063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72581846358516882904625417 54436384768887662178469063)
  ·
    refine ⟨81654577153331493267703595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54436384768887662178469063 81654577153331493267703595)
    ·
      refine ⟨122481865729997239901555393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81654577153331493267703595 122481865729997239901555393)
      ·
        refine ⟨91861399297497929926166545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122481865729997239901555393 91861399297497929926166545)
        ·
          refine ⟨68896049473123447444624909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91861399297497929926166545 68896049473123447444624909)
          ·
            refine ⟨25836018552421292791734341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68896049473123447444624909 25836018552421292791734341)
            ·
              refine ⟨4844253478578992398450189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25836018552421292791734341 4844253478578992398450189)
              ·
                refine ⟨1816595054467122149418821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4844253478578992398450189 1816595054467122149418821)
                ·
                  refine ⟨340611572712585403016029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816595054467122149418821 340611572712585403016029)
                  ·
                    rfl

theorem cell22_2985024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_2985024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985024 prefixEnd_2985024 := by exact prefixLift 2985024
  have htrace : WordTrace (prefixWord ++ tailWord_2985024) baseStart_2985024 baseEnd_2985024 := by
    simpa [prefixWord, tailWord_2985024, baseEnd_2985024] using wordTrace_append hprefix tailTrace_2985024
  have hstable : (prefixWord ++ tailWord_2985024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985024).length < 2 ^ (prefixWord ++ tailWord_2985024).sum := by decide
  have hdescent : baseEnd_2985024 < baseStart_2985024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985052 : List Nat := [2, 2, 4, 1, 1, 1, 2, 9]
def baseStart_2985052 : Nat := 118140960795 + 2985052 * 2 ^ 59
def prefixEnd_2985052 : Nat := 4983230072969 + 3 ^ 40 * 2985052 * 2
def baseEnd_2985052 : Nat := 113538255901108163260889

theorem tailTrace_2985052 : CollatzResearch.WordTrace tailWord_2985052 prefixEnd_2985052 113538255901108163260889 := by
  unfold tailWord_2985052
  simp only [CollatzResearch.WordTrace]
  refine ⟨54436895390836942569478705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72582527187782590092638273 54436895390836942569478705)
  ·
    refine ⟨40827671543127706927109029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54436895390836942569478705 40827671543127706927109029)
    ·
      refine ⟨7655188414336445048832943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40827671543127706927109029 7655188414336445048832943)
      ·
        refine ⟨11482782621504667573249415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7655188414336445048832943 11482782621504667573249415)
        ·
          refine ⟨17224173932257001359874123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11482782621504667573249415 17224173932257001359874123)
          ·
            refine ⟨25836260898385502039811185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17224173932257001359874123 25836260898385502039811185)
            ·
              refine ⟨19377195673789126529858389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25836260898385502039811185 19377195673789126529858389)
              ·
                refine ⟨113538255901108163260889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19377195673789126529858389 113538255901108163260889)
                ·
                  rfl

theorem cell22_2985052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_2985052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985052 prefixEnd_2985052 := by exact prefixLift 2985052
  have htrace : WordTrace (prefixWord ++ tailWord_2985052) baseStart_2985052 baseEnd_2985052 := by
    simpa [prefixWord, tailWord_2985052, baseEnd_2985052] using wordTrace_append hprefix tailTrace_2985052
  have hstable : (prefixWord ++ tailWord_2985052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985052).length < 2 ^ (prefixWord ++ tailWord_2985052).sum := by decide
  have hdescent : baseEnd_2985052 < baseStart_2985052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985056 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 2, 3]
def baseStart_2985056 : Nat := 118140960795 + 2985056 * 2 ^ 59
def prefixEnd_2985056 : Nat := 4983230072969 + 3 ^ 40 * 2985056 * 2
def baseEnd_2985056 : Nat := 1021845672391718792247989

theorem tailTrace_2985056 : CollatzResearch.WordTrace tailWord_2985056 prefixEnd_2985056 1021845672391718792247989 := by
  unfold tailWord_2985056
  simp only [CollatzResearch.WordTrace]
  refine ⟨54436968336829696911051511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72582624449106262548068681 54436968336829696911051511)
  ·
    refine ⟨81655452505244545366577267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54436968336829696911051511 81655452505244545366577267)
    ·
      refine ⟨122483178757866818049865901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81655452505244545366577267 122483178757866818049865901)
      ·
        refine ⟨45931192034200056768699713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122483178757866818049865901 45931192034200056768699713)
        ·
          refine ⟨34448394025650042576524785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45931192034200056768699713 34448394025650042576524785)
          ·
            refine ⟨25836295519237531932393589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34448394025650042576524785 25836295519237531932393589)
            ·
              refine ⟨2422152704928518618661899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25836295519237531932393589 2422152704928518618661899)
              ·
                refine ⟨3633229057392777927992849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422152704928518618661899 3633229057392777927992849)
                ·
                  refine ⟨2724921793044583445994637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3633229057392777927992849 2724921793044583445994637)
                  ·
                    refine ⟨1021845672391718792247989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724921793044583445994637 1021845672391718792247989)
                    ·
                      rfl

theorem cell22_2985056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_2985056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985056 prefixEnd_2985056 := by exact prefixLift 2985056
  have htrace : WordTrace (prefixWord ++ tailWord_2985056) baseStart_2985056 baseEnd_2985056 := by
    simpa [prefixWord, tailWord_2985056, baseEnd_2985056] using wordTrace_append hprefix tailTrace_2985056
  have hstable : (prefixWord ++ tailWord_2985056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985056).length < 2 ^ (prefixWord ++ tailWord_2985056).sum := by decide
  have hdescent : baseEnd_2985056 < baseStart_2985056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985069 : List Nat := [1, 5, 1, 1, 2, 2, 4, 6]
def baseStart_2985069 : Nat := 118140960795 + 2985069 * 2 ^ 59
def prefixEnd_2985069 : Nat := 4983230072969 + 3 ^ 40 * 2985069 * 2
def baseEnd_2985069 : Nat := 113538902506376787963661

theorem tailTrace_2985069 : CollatzResearch.WordTrace tailWord_2985069 prefixEnd_2985069 113538902506376787963661 := by
  unfold tailWord_2985069
  simp only [CollatzResearch.WordTrace]
  refine ⟨108874410822612297042326261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72582940548408198028217507 108874410822612297042326261)
  ·
    refine ⟨10206976014619902847718087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108874410822612297042326261 10206976014619902847718087)
    ·
      refine ⟨15310464021929854271577131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10206976014619902847718087 15310464021929854271577131)
      ·
        refine ⟨22965696032894781407365697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15310464021929854271577131 22965696032894781407365697)
        ·
          refine ⟨17224272024671086055524273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22965696032894781407365697 17224272024671086055524273)
          ·
            refine ⟨12918204018503314541643205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17224272024671086055524273 12918204018503314541643205)
            ·
              refine ⟨2422163253469371476558101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12918204018503314541643205 2422163253469371476558101)
              ·
                refine ⟨113538902506376787963661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2422163253469371476558101 113538902506376787963661)
                ·
                  rfl

theorem cell22_2985069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 6].length) (baseStart_2985069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985069 prefixEnd_2985069 := by exact prefixLift 2985069
  have htrace : WordTrace (prefixWord ++ tailWord_2985069) baseStart_2985069 baseEnd_2985069 := by
    simpa [prefixWord, tailWord_2985069, baseEnd_2985069] using wordTrace_append hprefix tailTrace_2985069
  have hstable : (prefixWord ++ tailWord_2985069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985069).length < 2 ^ (prefixWord ++ tailWord_2985069).sum := by decide
  have hdescent : baseEnd_2985069 < baseStart_2985069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985097 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 7]
def baseStart_2985097 : Nat := 118140960795 + 2985097 * 2 ^ 59
def prefixEnd_2985097 : Nat := 4983230072969 + 3 ^ 40 * 2985097 * 2
def baseEnd_2985097 : Nat := 340619902509869450657621

theorem tailTrace_2985097 : CollatzResearch.WordTrace tailWord_2985097 prefixEnd_2985097 340619902509869450657621 := by
  unfold tailWord_2985097
  simp only [CollatzResearch.WordTrace]
  refine ⟨108875432066510857824345545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72583621377673905216230363 108875432066510857824345545)
  ·
    refine ⟨81656574049883143368259159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108875432066510857824345545 81656574049883143368259159)
    ·
      refine ⟨122484861074824715052388739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81656574049883143368259159 122484861074824715052388739)
      ·
        refine ⟨183727291612237072578583109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122484861074824715052388739 183727291612237072578583109)
        ·
          refine ⟨34448867177294451108484333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183727291612237072578583109 34448867177294451108484333)
          ·
            refine ⟨12918325191485419165681625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34448867177294451108484333 12918325191485419165681625)
            ·
              refine ⟨9688743893614064374261219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12918325191485419165681625 9688743893614064374261219)
              ·
                refine ⟨14533115840421096561391829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9688743893614064374261219 14533115840421096561391829)
                ·
                  refine ⟨340619902509869450657621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14533115840421096561391829 340619902509869450657621)
                  ·
                    rfl

theorem cell22_2985097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_2985097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985097 prefixEnd_2985097 := by exact prefixLift 2985097
  have htrace : WordTrace (prefixWord ++ tailWord_2985097) baseStart_2985097 baseEnd_2985097 := by
    simpa [prefixWord, tailWord_2985097, baseEnd_2985097] using wordTrace_append hprefix tailTrace_2985097
  have hstable : (prefixWord ++ tailWord_2985097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985097).length < 2 ^ (prefixWord ++ tailWord_2985097).sum := by decide
  have hdescent : baseEnd_2985097 < baseStart_2985097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985152 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 1, 3]
def baseStart_2985152 : Nat := 118140960795 + 2985152 * 2 ^ 59
def prefixEnd_2985152 : Nat := 4983230072969 + 3 ^ 40 * 2985152 * 2
def baseEnd_2985152 : Nat := 1021878535153606541847695

theorem tailTrace_2985152 : CollatzResearch.WordTrace tailWord_2985152 prefixEnd_2985152 1021878535153606541847695 := by
  unfold tailWord_2985152
  simp only [CollatzResearch.WordTrace]
  refine ⟨54438719040655801108798855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72584958720874401478398473 54438719040655801108798855)
  ·
    refine ⟨81658078560983701663198283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54438719040655801108798855 81658078560983701663198283)
    ·
      refine ⟨122487117841475552494797425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81658078560983701663198283 122487117841475552494797425)
      ·
        refine ⟨91865338381106664371098069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122487117841475552494797425 91865338381106664371098069)
        ·
          refine ⟨2153093868307187446197611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91865338381106664371098069 2153093868307187446197611)
          ·
            refine ⟨3229640802460781169296417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153093868307187446197611 3229640802460781169296417)
            ·
              refine ⟨2422230601845585876972313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229640802460781169296417 2422230601845585876972313)
              ·
                refine ⟨1816672951384189407729235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422230601845585876972313 1816672951384189407729235)
                ·
                  refine ⟨2725009427076284111593853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816672951384189407729235 2725009427076284111593853)
                  ·
                    refine ⟨1021878535153606541847695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2725009427076284111593853 1021878535153606541847695)
                    ·
                      rfl

theorem cell22_2985152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_2985152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985152 prefixEnd_2985152 := by exact prefixLift 2985152
  have htrace : WordTrace (prefixWord ++ tailWord_2985152) baseStart_2985152 baseEnd_2985152 := by
    simpa [prefixWord, tailWord_2985152, baseEnd_2985152] using wordTrace_append hprefix tailTrace_2985152
  have hstable : (prefixWord ++ tailWord_2985152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985152).length < 2 ^ (prefixWord ++ tailWord_2985152).sum := by decide
  have hdescent : baseEnd_2985152 < baseStart_2985152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985157 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2985157 : Nat := 118140960795 + 2985157 * 2 ^ 59
def prefixEnd_2985157 : Nat := 4983230072969 + 3 ^ 40 * 2985157 * 2
def baseEnd_2985157 : Nat := 1021880246755788195472679

theorem tailTrace_2985157 : CollatzResearch.WordTrace tailWord_2985157 prefixEnd_2985157 1021880246755788195472679 := by
  unfold tailWord_2985157
  simp only [CollatzResearch.WordTrace]
  refine ⟨108877620446293488071529725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72585080297528992047686483 108877620446293488071529725)
  ·
    refine ⟨40829107667360058026823647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108877620446293488071529725 40829107667360058026823647)
    ·
      refine ⟨61243661501040087040235471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40829107667360058026823647 61243661501040087040235471)
      ·
        refine ⟨91865492251560130560353207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61243661501040087040235471 91865492251560130560353207)
        ·
          refine ⟨137798238377340195840529811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91865492251560130560353207 137798238377340195840529811)
          ·
            refine ⟨206697357566010293760794717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137798238377340195840529811 206697357566010293760794717)
            ·
              refine ⟨77511509087253860160298019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206697357566010293760794717 77511509087253860160298019)
              ·
                refine ⟨116267263630880790240447029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77511509087253860160298019 116267263630880790240447029)
                ·
                  refine ⟨10900055965395074085041909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116267263630880790240447029 10900055965395074085041909)
                  ·
                    refine ⟨1021880246755788195472679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10900055965395074085041909 1021880246755788195472679)
                    ·
                      rfl

theorem cell22_2985157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2985157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985157 prefixEnd_2985157 := by exact prefixLift 2985157
  have htrace : WordTrace (prefixWord ++ tailWord_2985157) baseStart_2985157 baseEnd_2985157 := by
    simpa [prefixWord, tailWord_2985157, baseEnd_2985157] using wordTrace_append hprefix tailTrace_2985157
  have hstable : (prefixWord ++ tailWord_2985157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985157).length < 2 ^ (prefixWord ++ tailWord_2985157).sum := by decide
  have hdescent : baseEnd_2985157 < baseStart_2985157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985294 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2985294 : Nat := 118140960795 + 2985294 * 2 ^ 59
def prefixEnd_2985294 : Nat := 4983230072969 + 3 ^ 40 * 2985294 * 2
def baseEnd_2985294 : Nat := 340642381551855168265753

theorem tailTrace_2985294 : CollatzResearch.WordTrace tailWord_2985294 prefixEnd_2985294 340642381551855168265753 := by
  unfold tailWord_2985294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610327155849645058658367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72588411497864773646177957 13610327155849645058658367)
  ·
    refine ⟨20415490733774467587987551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610327155849645058658367 20415490733774467587987551)
    ·
      refine ⟨30623236100661701381981327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415490733774467587987551 30623236100661701381981327)
      ·
        refine ⟨45934854150992552072971991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30623236100661701381981327 45934854150992552072971991)
        ·
          refine ⟨68902281226488828109457987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45934854150992552072971991 68902281226488828109457987)
          ·
            refine ⟨103353421839733242164186981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68902281226488828109457987 103353421839733242164186981)
            ·
              refine ⟨19378766594949982905785059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103353421839733242164186981 19378766594949982905785059)
              ·
                refine ⟨29068149892424974358677589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19378766594949982905785059 29068149892424974358677589)
                ·
                  refine ⟨340642381551855168265753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29068149892424974358677589 340642381551855168265753)
                  ·
                    rfl

theorem cell22_2985294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2985294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985294 prefixEnd_2985294 := by exact prefixLift 2985294
  have htrace : WordTrace (prefixWord ++ tailWord_2985294) baseStart_2985294 baseEnd_2985294 := by
    simpa [prefixWord, tailWord_2985294, baseEnd_2985294] using wordTrace_append hprefix tailTrace_2985294
  have hstable : (prefixWord ++ tailWord_2985294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985294).length < 2 ^ (prefixWord ++ tailWord_2985294).sum := by decide
  have hdescent : baseEnd_2985294 < baseStart_2985294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985311 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 4]
def baseStart_2985311 : Nat := 118140960795 + 2985311 * 2 ^ 59
def prefixEnd_2985311 : Nat := 4983230072969 + 3 ^ 40 * 2985311 * 2
def baseEnd_2985311 : Nat := 340644321367661042374069

theorem tailTrace_2985311 : CollatzResearch.WordTrace tailWord_2985311 prefixEnd_2985311 340644321367661042374069 := by
  unfold tailWord_2985311
  simp only [CollatzResearch.WordTrace]
  refine ⟨108883237287735572372635787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72588824858490381581757191 108883237287735572372635787)
  ·
    refine ⟨163324855931603358558953681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108883237287735572372635787 163324855931603358558953681)
    ·
      refine ⟨122493641948702518919215261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163324855931603358558953681 122493641948702518919215261)
      ·
        refine ⟨45935115730763444594705723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122493641948702518919215261 45935115730763444594705723)
        ·
          refine ⟨68902673596145166892058585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45935115730763444594705723 68902673596145166892058585)
          ·
            refine ⟨51677005197108875169043939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68902673596145166892058585 51677005197108875169043939)
            ·
              refine ⟨77515507795663312753565909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51677005197108875169043939 77515507795663312753565909)
              ·
                refine ⟨1816769713960858892661701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77515507795663312753565909 1816769713960858892661701)
                ·
                  refine ⟨340644321367661042374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816769713960858892661701 340644321367661042374069)
                  ·
                    rfl

theorem cell22_2985311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 4].length) (baseStart_2985311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985311 prefixEnd_2985311 := by exact prefixLift 2985311
  have htrace : WordTrace (prefixWord ++ tailWord_2985311) baseStart_2985311 baseEnd_2985311 := by
    simpa [prefixWord, tailWord_2985311, baseEnd_2985311] using wordTrace_append hprefix tailTrace_2985311
  have hstable : (prefixWord ++ tailWord_2985311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985311).length < 2 ^ (prefixWord ++ tailWord_2985311).sum := by decide
  have hdescent : baseEnd_2985311 < baseStart_2985311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985356 : List Nat := [2, 2, 1, 2, 1, 3, 5, 6]
def baseStart_2985356 : Nat := 118140960795 + 2985356 * 2 ^ 59
def prefixEnd_2985356 : Nat := 4983230072969 + 3 ^ 40 * 2985356 * 2
def baseEnd_2985356 : Nat := 113549818724735334416341

theorem tailTrace_2985356 : CollatzResearch.WordTrace tailWord_2985356 prefixEnd_2985356 113549818724735334416341 := by
  unfold tailWord_2985356
  simp only [CollatzResearch.WordTrace]
  refine ⟨54442439286286272529011961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72589919048381696705349281 54442439286286272529011961)
  ·
    refine ⟨40831829464714704396758971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54442439286286272529011961 40831829464714704396758971)
    ·
      refine ⟨61247744197072056595138457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40831829464714704396758971 61247744197072056595138457)
      ·
        refine ⟨45935808147804042446353843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61247744197072056595138457 45935808147804042446353843)
        ·
          refine ⟨68903712221706063669530765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45935808147804042446353843 68903712221706063669530765)
          ·
            refine ⟨25838892083139773876074037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68903712221706063669530765 25838892083139773876074037)
            ·
              refine ⟨2422396132794353800881941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25838892083139773876074037 2422396132794353800881941)
              ·
                refine ⟨113549818724735334416341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2422396132794353800881941 113549818724735334416341)
                ·
                  rfl

theorem cell22_2985356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 6].length) (baseStart_2985356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985356 prefixEnd_2985356 := by exact prefixLift 2985356
  have htrace : WordTrace (prefixWord ++ tailWord_2985356) baseStart_2985356 baseEnd_2985356 := by
    simpa [prefixWord, tailWord_2985356, baseEnd_2985356] using wordTrace_append hprefix tailTrace_2985356
  have hstable : (prefixWord ++ tailWord_2985356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985356).length < 2 ^ (prefixWord ++ tailWord_2985356).sum := by decide
  have hdescent : baseEnd_2985356 < baseStart_2985356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985358 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2985358 : Nat := 118140960795 + 2985358 * 2 ^ 59
def prefixEnd_2985358 : Nat := 4983230072969 + 3 ^ 40 * 2985358 * 2
def baseEnd_2985358 : Nat := 1021949053163490671197063

theorem tailTrace_2985358 : CollatzResearch.WordTrace tailWord_2985358 prefixEnd_2985358 1021949053163490671197063 := by
  unfold tailWord_2985358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610618939820662424949591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72589967679043532933064485 13610618939820662424949591)
  ·
    refine ⟨20415928409730993637424387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610618939820662424949591 20415928409730993637424387)
    ·
      refine ⟨30623892614596490456136581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415928409730993637424387 30623892614596490456136581)
      ·
        refine ⟨5741979865236841960525609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30623892614596490456136581 5741979865236841960525609)
        ·
          refine ⟨4306484898927631470394207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5741979865236841960525609 4306484898927631470394207)
          ·
            refine ⟨6459727348391447205591311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306484898927631470394207 6459727348391447205591311)
            ·
              refine ⟨9689591022587170808386967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459727348391447205591311 9689591022587170808386967)
              ·
                refine ⟨14534386533880756212580451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9689591022587170808386967 14534386533880756212580451)
                ·
                  refine ⟨21801579800821134318870677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14534386533880756212580451 21801579800821134318870677)
                  ·
                    refine ⟨1021949053163490671197063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21801579800821134318870677 1021949053163490671197063)
                    ·
                      rfl

theorem cell22_2985358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2985358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985358 prefixEnd_2985358 := by exact prefixLift 2985358
  have htrace : WordTrace (prefixWord ++ tailWord_2985358) baseStart_2985358 baseEnd_2985358 := by
    simpa [prefixWord, tailWord_2985358, baseEnd_2985358] using wordTrace_append hprefix tailTrace_2985358
  have hstable : (prefixWord ++ tailWord_2985358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985358).length < 2 ^ (prefixWord ++ tailWord_2985358).sum := by decide
  have hdescent : baseEnd_2985358 < baseStart_2985358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985362 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2985362 : Nat := 118140960795 + 2985362 * 2 ^ 59
def prefixEnd_2985362 : Nat := 4983230072969 + 3 ^ 40 * 2985362 * 2
def baseEnd_2985362 : Nat := 340650140815078664699017

theorem tailTrace_2985362 : CollatzResearch.WordTrace tailWord_2985362 prefixEnd_2985362 340650140815078664699017 := by
  unfold tailWord_2985362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221274352637702020685585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72590064940367205388494893 27221274352637702020685585)
  ·
    refine ⟨20415955764478276515514189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27221274352637702020685585 20415955764478276515514189)
    ·
      refine ⟨7655983411679353693317821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20415955764478276515514189 7655983411679353693317821)
      ·
        refine ⟨2870993779379757634994183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7655983411679353693317821 2870993779379757634994183)
        ·
          refine ⟨4306490669069636452491275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870993779379757634994183 4306490669069636452491275)
          ·
            refine ⟨6459736003604454678736913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306490669069636452491275 6459736003604454678736913)
            ·
              refine ⟨4844802002703341009052685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6459736003604454678736913 4844802002703341009052685)
              ·
                refine ⟨1816800751013752878394757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4844802002703341009052685 1816800751013752878394757)
                ·
                  refine ⟨340650140815078664699017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816800751013752878394757 340650140815078664699017)
                  ·
                    rfl

theorem cell22_2985362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2985362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985362 prefixEnd_2985362 := by exact prefixLift 2985362
  have htrace : WordTrace (prefixWord ++ tailWord_2985362) baseStart_2985362 baseEnd_2985362 := by
    simpa [prefixWord, tailWord_2985362, baseEnd_2985362] using wordTrace_append hprefix tailTrace_2985362
  have hstable : (prefixWord ++ tailWord_2985362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985362).length < 2 ^ (prefixWord ++ tailWord_2985362).sum := by decide
  have hdescent : baseEnd_2985362 < baseStart_2985362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985493 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2985493 : Nat := 118140960795 + 2985493 * 2 ^ 59
def prefixEnd_2985493 : Nat := 4983230072969 + 3 ^ 40 * 2985493 * 2
def baseEnd_2985493 : Nat := 1021995266422395319071649

theorem tailTrace_2985493 : CollatzResearch.WordTrace tailWord_2985493 prefixEnd_2985493 1021995266422395319071649 := by
  unfold tailWord_2985493
  simp only [CollatzResearch.WordTrace]
  refine ⟨108889875373076217455761133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72593250248717478303840755 108889875373076217455761133)
  ·
    refine ⟨40833703264903581545910425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108889875373076217455761133 40833703264903581545910425)
    ·
      refine ⟨30625277448677686159432819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40833703264903581545910425 30625277448677686159432819)
      ·
        refine ⟨45937916173016529239149229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30625277448677686159432819 45937916173016529239149229)
        ·
          refine ⟨17226718564881198464680961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45937916173016529239149229 17226718564881198464680961)
          ·
            refine ⟨12920038923660898848510721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17226718564881198464680961 12920038923660898848510721)
            ·
              refine ⟨9690029192745674136383041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12920038923660898848510721 9690029192745674136383041)
              ·
                refine ⟨7267521894559255602287281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690029192745674136383041 7267521894559255602287281)
                ·
                  refine ⟨5450641420919441701715461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7267521894559255602287281 5450641420919441701715461)
                  ·
                    refine ⟨1021995266422395319071649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5450641420919441701715461 1021995266422395319071649)
                    ·
                      rfl

theorem cell22_2985493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2985493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985493 prefixEnd_2985493 := by exact prefixLift 2985493
  have htrace : WordTrace (prefixWord ++ tailWord_2985493) baseStart_2985493 baseEnd_2985493 := by
    simpa [prefixWord, tailWord_2985493, baseEnd_2985493] using wordTrace_append hprefix tailTrace_2985493
  have hstable : (prefixWord ++ tailWord_2985493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985493).length < 2 ^ (prefixWord ++ tailWord_2985493).sum := by decide
  have hdescent : baseEnd_2985493 < baseStart_2985493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985521 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_2985521 : Nat := 118140960795 + 2985521 * 2 ^ 59
def prefixEnd_2985521 : Nat := 4983230072969 + 3 ^ 40 * 2985521 * 2
def baseEnd_2985521 : Nat := 1022004851394612579371563

theorem tailTrace_2985521 : CollatzResearch.WordTrace tailWord_2985521 prefixEnd_2985521 1022004851394612579371563 := by
  unfold tailWord_2985521
  simp only [CollatzResearch.WordTrace]
  refine ⟨108890896616974778237780417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72593931077983185491853611 108890896616974778237780417)
  ·
    refine ⟨81668172462731083678335313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108890896616974778237780417 81668172462731083678335313)
    ·
      refine ⟨61251129347048312758751485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81668172462731083678335313 61251129347048312758751485)
      ·
        refine ⟨22969173505143117284531807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61251129347048312758751485 22969173505143117284531807)
        ·
          refine ⟨34453760257714675926797711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22969173505143117284531807 34453760257714675926797711)
          ·
            refine ⟨51680640386572013890196567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34453760257714675926797711 51680640386572013890196567)
            ·
              refine ⟨77520960579858020835294851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51680640386572013890196567 77520960579858020835294851)
              ·
                refine ⟨116281440869787031252942277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77520960579858020835294851 116281440869787031252942277)
                ·
                  refine ⟨21802770163085068359926677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116281440869787031252942277 21802770163085068359926677)
                  ·
                    refine ⟨1022004851394612579371563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21802770163085068359926677 1022004851394612579371563)
                    ·
                      rfl

theorem cell22_2985521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_2985521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985521 prefixEnd_2985521 := by exact prefixLift 2985521
  have htrace : WordTrace (prefixWord ++ tailWord_2985521) baseStart_2985521 baseEnd_2985521 := by
    simpa [prefixWord, tailWord_2985521, baseEnd_2985521] using wordTrace_append hprefix tailTrace_2985521
  have hstable : (prefixWord ++ tailWord_2985521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985521).length < 2 ^ (prefixWord ++ tailWord_2985521).sum := by decide
  have hdescent : baseEnd_2985521 < baseStart_2985521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985523 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 5, 3]
def baseStart_2985523 : Nat := 118140960795 + 2985523 * 2 ^ 59
def prefixEnd_2985523 : Nat := 4983230072969 + 3 ^ 40 * 2985523 * 2
def baseEnd_2985523 : Nat := 1022005536035485240821557

theorem tailTrace_2985523 : CollatzResearch.WordTrace tailWord_2985523 prefixEnd_2985523 1022005536035485240821557 := by
  unfold tailWord_2985523
  simp only [CollatzResearch.WordTrace]
  refine ⟨108890969562967532579353223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72593979708645021719568815 108890969562967532579353223)
  ·
    refine ⟨163336454344451298869029835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108890969562967532579353223 163336454344451298869029835)
    ·
      refine ⟨245004681516676948303544753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163336454344451298869029835 245004681516676948303544753)
      ·
        refine ⟨183753511137507711227658565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245004681516676948303544753 183753511137507711227658565)
        ·
          refine ⟨34453783338282695855185981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183753511137507711227658565 34453783338282695855185981)
          ·
            refine ⟨12920168751856010945694743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34453783338282695855185981 12920168751856010945694743)
            ·
              refine ⟨19380253127784016418542115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920168751856010945694743 19380253127784016418542115)
              ·
                refine ⟨29070379691676024627813173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19380253127784016418542115 29070379691676024627813173)
                ·
                  refine ⟨2725348096094627308857485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29070379691676024627813173 2725348096094627308857485)
                  ·
                    refine ⟨1022005536035485240821557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2725348096094627308857485 1022005536035485240821557)
                    ·
                      rfl

theorem cell22_2985523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 3].length) (baseStart_2985523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985523 prefixEnd_2985523 := by exact prefixLift 2985523
  have htrace : WordTrace (prefixWord ++ tailWord_2985523) baseStart_2985523 baseEnd_2985523 := by
    simpa [prefixWord, tailWord_2985523, baseEnd_2985523] using wordTrace_append hprefix tailTrace_2985523
  have hstable : (prefixWord ++ tailWord_2985523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985523).length < 2 ^ (prefixWord ++ tailWord_2985523).sum := by decide
  have hdescent : baseEnd_2985523 < baseStart_2985523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985536 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_2985536 : Nat := 118140960795 + 2985536 * 2 ^ 59
def prefixEnd_2985536 : Nat := 4983230072969 + 3 ^ 40 * 2985536 * 2
def baseEnd_2985536 : Nat := 340669995400385846748839

theorem tailTrace_2985536 : CollatzResearch.WordTrace tailWord_2985536 prefixEnd_2985536 340669995400385846748839 := by
  unfold tailWord_2985536
  simp only [CollatzResearch.WordTrace]
  refine ⟨54445721855960217899788231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72594295807946957199717641 54445721855960217899788231)
  ·
    refine ⟨81668582783940326849682347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54445721855960217899788231 81668582783940326849682347)
    ·
      refine ⟨122502874175910490274523521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81668582783940326849682347 122502874175910490274523521)
      ·
        refine ⟨91877155631932867705892641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122502874175910490274523521 91877155631932867705892641)
        ·
          refine ⟨68907866723949650779419481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91877155631932867705892641 68907866723949650779419481)
          ·
            refine ⟨51680900042962238084564611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68907866723949650779419481 51680900042962238084564611)
            ·
              refine ⟨77521350064443357126846917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51680900042962238084564611 77521350064443357126846917)
              ·
                refine ⟨14535253137083129461283797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77521350064443357126846917 14535253137083129461283797)
                ·
                  refine ⟨340669995400385846748839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14535253137083129461283797 340669995400385846748839)
                  ·
                    rfl

theorem cell22_2985536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_2985536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985536 prefixEnd_2985536 := by exact prefixLift 2985536
  have htrace : WordTrace (prefixWord ++ tailWord_2985536) baseStart_2985536 baseEnd_2985536 := by
    simpa [prefixWord, tailWord_2985536, baseEnd_2985536] using wordTrace_append hprefix tailTrace_2985536
  have hstable : (prefixWord ++ tailWord_2985536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985536).length < 2 ^ (prefixWord ++ tailWord_2985536).sum := by decide
  have hdescent : baseEnd_2985536 < baseStart_2985536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985677 : List Nat := [1, 6, 2, 1, 1, 1, 3, 7]
def baseStart_2985677 : Nat := 118140960795 + 2985677 * 2 ^ 59
def prefixEnd_2985677 : Nat := 4983230072969 + 3 ^ 40 * 2985677 * 2
def baseEnd_2985677 : Nat := 113562028153631130274565

theorem tailTrace_2985677 : CollatzResearch.WordTrace tailWord_2985677 prefixEnd_2985677 113562028153631130274565 := by
  unfold tailWord_2985677
  simp only [CollatzResearch.WordTrace]
  refine ⟨108896586404409616880459285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72597724269606411253639523 108896586404409616880459285)
  ·
    refine ⟨5104527487706700791271529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108896586404409616880459285 5104527487706700791271529)
    ·
      refine ⟨3828395615780025593453647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5104527487706700791271529 3828395615780025593453647)
      ·
        refine ⟨5742593423670038390180471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828395615780025593453647 5742593423670038390180471)
        ·
          refine ⟨8613890135505057585270707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5742593423670038390180471 8613890135505057585270707)
          ·
            refine ⟨12920835203257586377906061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8613890135505057585270707 12920835203257586377906061)
            ·
              refine ⟨4845313201221594891714773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12920835203257586377906061 4845313201221594891714773)
              ·
                refine ⟨113562028153631130274565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4845313201221594891714773 113562028153631130274565)
                ·
                  rfl

theorem cell22_2985677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 7].length) (baseStart_2985677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985677 prefixEnd_2985677 := by exact prefixLift 2985677
  have htrace : WordTrace (prefixWord ++ tailWord_2985677) baseStart_2985677 baseEnd_2985677 := by
    simpa [prefixWord, tailWord_2985677, baseEnd_2985677] using wordTrace_append hprefix tailTrace_2985677
  have hstable : (prefixWord ++ tailWord_2985677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985677).length < 2 ^ (prefixWord ++ tailWord_2985677).sum := by decide
  have hdescent : baseEnd_2985677 < baseStart_2985677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985709 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2985709 : Nat := 118140960795 + 2985709 * 2 ^ 59
def prefixEnd_2985709 : Nat := 4983230072969 + 3 ^ 40 * 2985709 * 2
def baseEnd_2985709 : Nat := 1022069207636642755670987

theorem tailTrace_2985709 : CollatzResearch.WordTrace tailWord_2985709 prefixEnd_2985709 1022069207636642755670987 := by
  unfold tailWord_2985709
  simp only [CollatzResearch.WordTrace]
  refine ⟨108897753540293686345624181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72598502360195790897082787 108897753540293686345624181)
  ·
    refine ⟨10209164394402533094902267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108897753540293686345624181 10209164394402533094902267)
    ·
      refine ⟨15313746591603799642353401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10209164394402533094902267 15313746591603799642353401)
      ·
        refine ⟨11485309943702849731765051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15313746591603799642353401 11485309943702849731765051)
        ·
          refine ⟨17227964915554274597647577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11485309943702849731765051 17227964915554274597647577)
          ·
            refine ⟨12920973686665705948235683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17227964915554274597647577 12920973686665705948235683)
            ·
              refine ⟨19381460529998558922353525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920973686665705948235683 19381460529998558922353525)
              ·
                refine ⟨1817011924687364898970643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19381460529998558922353525 1817011924687364898970643)
                ·
                  refine ⟨2725517887031047348455965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817011924687364898970643 2725517887031047348455965)
                  ·
                    refine ⟨1022069207636642755670987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2725517887031047348455965 1022069207636642755670987)
                    ·
                      rfl

theorem cell22_2985709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2985709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985709 prefixEnd_2985709 := by exact prefixLift 2985709
  have htrace : WordTrace (prefixWord ++ tailWord_2985709) baseStart_2985709 baseEnd_2985709 := by
    simpa [prefixWord, tailWord_2985709, baseEnd_2985709] using wordTrace_append hprefix tailTrace_2985709
  have hstable : (prefixWord ++ tailWord_2985709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985709).length < 2 ^ (prefixWord ++ tailWord_2985709).sum := by decide
  have hdescent : baseEnd_2985709 < baseStart_2985709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985784 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 4]
def baseStart_2985784 : Nat := 118140960795 + 2985784 * 2 ^ 59
def prefixEnd_2985784 : Nat := 4983230072969 + 3 ^ 40 * 2985784 * 2
def baseEnd_2985784 : Nat := 340698293889789186681919

theorem tailTrace_2985784 : CollatzResearch.WordTrace tailWord_2985784 prefixEnd_2985784 340698293889789186681919 := by
  unfold tailWord_2985784
  simp only [CollatzResearch.WordTrace]
  refine ⟨54450244507510987077302203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72600326010014649436402937 54450244507510987077302203)
  ·
    refine ⟨81675366761266480615953305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54450244507510987077302203 81675366761266480615953305)
    ·
      refine ⟨61256525070949860461964979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81675366761266480615953305 61256525070949860461964979)
      ·
        refine ⟨91884787606424790692947469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61256525070949860461964979 91884787606424790692947469)
        ·
          refine ⟨34456795352409296509855301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91884787606424790692947469 34456795352409296509855301)
          ·
            refine ⟨6460649128576743095597869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34456795352409296509855301 6460649128576743095597869)
            ·
              refine ⟨2422743423216278660849201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6460649128576743095597869 2422743423216278660849201)
              ·
                refine ⟨1817057567412208995636901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422743423216278660849201 1817057567412208995636901)
                ·
                  refine ⟨340698293889789186681919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1817057567412208995636901 340698293889789186681919)
                  ·
                    rfl

theorem cell22_2985784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_2985784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985784 prefixEnd_2985784 := by exact prefixLift 2985784
  have htrace : WordTrace (prefixWord ++ tailWord_2985784) baseStart_2985784 baseEnd_2985784 := by
    simpa [prefixWord, tailWord_2985784, baseEnd_2985784] using wordTrace_append hprefix tailTrace_2985784
  have hstable : (prefixWord ++ tailWord_2985784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985784).length < 2 ^ (prefixWord ++ tailWord_2985784).sum := by decide
  have hdescent : baseEnd_2985784 < baseStart_2985784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985795 : List Nat := [1, 1, 1, 3, 1, 6, 2, 7]
def baseStart_2985795 : Nat := 118140960795 + 2985795 * 2 ^ 59
def prefixEnd_2985795 : Nat := 4983230072969 + 3 ^ 40 * 2985795 * 2
def baseEnd_2985795 : Nat := 113566516354907466446747

theorem tailTrace_2985795 : CollatzResearch.WordTrace tailWord_2985795 prefixEnd_2985795 113566516354907466446747 := by
  unfold tailWord_2985795
  simp only [CollatzResearch.WordTrace]
  refine ⟨108900890217982123033254839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72600593478654748688836559 108900890217982123033254839)
  ·
    refine ⟨163351335326973184549882259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108900890217982123033254839 163351335326973184549882259)
    ·
      refine ⟨245027002990459776824823389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163351335326973184549882259 245027002990459776824823389)
      ·
        refine ⟨91885126121422416309308771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245027002990459776824823389 91885126121422416309308771)
        ·
          refine ⟨137827689182133624463963157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91885126121422416309308771 137827689182133624463963157)
          ·
            refine ⟨6460672930412513646748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137827689182133624463963157 6460672930412513646748273)
            ·
              refine ⟨4845504697809385235061205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6460672930412513646748273 4845504697809385235061205)
              ·
                refine ⟨113566516354907466446747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4845504697809385235061205 113566516354907466446747)
                ·
                  rfl

theorem cell22_2985795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 7].length) (baseStart_2985795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985795 prefixEnd_2985795 := by exact prefixLift 2985795
  have htrace : WordTrace (prefixWord ++ tailWord_2985795) baseStart_2985795 baseEnd_2985795 := by
    simpa [prefixWord, tailWord_2985795, baseEnd_2985795] using wordTrace_append hprefix tailTrace_2985795
  have hstable : (prefixWord ++ tailWord_2985795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985795).length < 2 ^ (prefixWord ++ tailWord_2985795).sum := by decide
  have hdescent : baseEnd_2985795 < baseStart_2985795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985799 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 2, 3]
def baseStart_2985799 : Nat := 118140960795 + 2985799 * 2 ^ 59
def prefixEnd_2985799 : Nat := 4983230072969 + 3 ^ 40 * 2985799 * 2
def baseEnd_2985799 : Nat := 1022100016475912520920711

theorem tailTrace_2985799 : CollatzResearch.WordTrace tailWord_2985799 prefixEnd_2985799 1022100016475912520920711 := by
  unfold tailWord_2985799
  simp only [CollatzResearch.WordTrace]
  refine ⟨108901036109967631716400451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72600690739978421144266967 108901036109967631716400451)
  ·
    refine ⟨163351554164951447574600677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108901036109967631716400451 163351554164951447574600677)
    ·
      refine ⟨30628416405928396420237627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163351554164951447574600677 30628416405928396420237627)
      ·
        refine ⟨45942624608892594630356441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30628416405928396420237627 45942624608892594630356441)
        ·
          refine ⟨34456968456669445972767331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45942624608892594630356441 34456968456669445972767331)
          ·
            refine ⟨51685452685004168959150997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34456968456669445972767331 51685452685004168959150997)
            ·
              refine ⟨2422755594609570419960203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51685452685004168959150997 2422755594609570419960203)
              ·
                refine ⟨3634133391914355629940305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422755594609570419960203 3634133391914355629940305)
                ·
                  refine ⟨2725600043935766722455229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634133391914355629940305 2725600043935766722455229)
                  ·
                    refine ⟨1022100016475912520920711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2725600043935766722455229 1022100016475912520920711)
                    ·
                      rfl

theorem cell22_2985799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_2985799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985799 prefixEnd_2985799 := by exact prefixLift 2985799
  have htrace : WordTrace (prefixWord ++ tailWord_2985799) baseStart_2985799 baseEnd_2985799 := by
    simpa [prefixWord, tailWord_2985799, baseEnd_2985799] using wordTrace_append hprefix tailTrace_2985799
  have hstable : (prefixWord ++ tailWord_2985799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985799).length < 2 ^ (prefixWord ++ tailWord_2985799).sum := by decide
  have hdescent : baseEnd_2985799 < baseStart_2985799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985846 : List Nat := [5, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2985846 : Nat := 118140960795 + 2985846 * 2 ^ 59
def prefixEnd_2985846 : Nat := 4983230072969 + 3 ^ 40 * 2985846 * 2
def baseEnd_2985846 : Nat := 113568456170713340555063

theorem tailTrace_2985846 : CollatzResearch.WordTrace tailWord_2985846 prefixEnd_2985846 113568456170713340555063 := by
  unfold tailWord_2985846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806421896299834921460087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72601833560531572495574261 6806421896299834921460087)
  ·
    refine ⟨10209632844449752382190131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806421896299834921460087 10209632844449752382190131)
    ·
      refine ⟨15314449266674628573285197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10209632844449752382190131 15314449266674628573285197)
      ·
        refine ⟨5742918475002985714981949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15314449266674628573285197 5742918475002985714981949)
        ·
          refine ⟨2153594428126119643118231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5742918475002985714981949 2153594428126119643118231)
          ·
            refine ⟨3230391642189179464677347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153594428126119643118231 3230391642189179464677347)
            ·
              refine ⟨4845587463283769197016021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230391642189179464677347 4845587463283769197016021)
              ·
                refine ⟨113568456170713340555063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4845587463283769197016021 113568456170713340555063)
                ·
                  rfl

theorem cell22_2985846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2985846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985846 prefixEnd_2985846 := by exact prefixLift 2985846
  have htrace : WordTrace (prefixWord ++ tailWord_2985846) baseStart_2985846 baseEnd_2985846 := by
    simpa [prefixWord, tailWord_2985846, baseEnd_2985846] using wordTrace_append hprefix tailTrace_2985846
  have hstable : (prefixWord ++ tailWord_2985846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985846).length < 2 ^ (prefixWord ++ tailWord_2985846).sum := by decide
  have hdescent : baseEnd_2985846 < baseStart_2985846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985908 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2985908 : Nat := 118140960795 + 2985908 * 2 ^ 59
def prefixEnd_2985908 : Nat := 4983230072969 + 3 ^ 40 * 2985908 * 2
def baseEnd_2985908 : Nat := 340712443134490856648459

theorem tailTrace_2985908 : CollatzResearch.WordTrace tailWord_2985908 prefixEnd_2985908 340712443134490856648459 := by
  unfold tailWord_2985908
  simp only [CollatzResearch.WordTrace]
  refine ⟨54452505833286371666059189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72603341111048495554745585 54452505833286371666059189)
  ·
    refine ⟨5104922421870597343693049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54452505833286371666059189 5104922421870597343693049)
    ·
      refine ⟨3828691816402948007769787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5104922421870597343693049 3828691816402948007769787)
      ·
        refine ⟨5743037724604422011654681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828691816402948007769787 5743037724604422011654681)
        ·
          refine ⟨4307278293453316508741011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5743037724604422011654681 4307278293453316508741011)
          ·
            refine ⟨6460917440179974763111517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307278293453316508741011 6460917440179974763111517)
            ·
              refine ⟨2422844040067490536166819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6460917440179974763111517 2422844040067490536166819)
              ·
                refine ⟨3634266060101235804250229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422844040067490536166819 3634266060101235804250229)
                ·
                  refine ⟨340712443134490856648459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3634266060101235804250229 340712443134490856648459)
                  ·
                    rfl

theorem cell22_2985908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2985908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985908 prefixEnd_2985908 := by exact prefixLift 2985908
  have htrace : WordTrace (prefixWord ++ tailWord_2985908) baseStart_2985908 baseEnd_2985908 := by
    simpa [prefixWord, tailWord_2985908, baseEnd_2985908] using wordTrace_append hprefix tailTrace_2985908
  have hstable : (prefixWord ++ tailWord_2985908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985908).length < 2 ^ (prefixWord ++ tailWord_2985908).sum := by decide
  have hdescent : baseEnd_2985908 < baseStart_2985908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985915 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_2985915 : Nat := 118140960795 + 2985915 * 2 ^ 59
def prefixEnd_2985915 : Nat := 4983230072969 + 3 ^ 40 * 2985915 * 2
def baseEnd_2985915 : Nat := 1022139725646526885020355

theorem tailTrace_2985915 : CollatzResearch.WordTrace tailWord_2985915 prefixEnd_2985915 1022139725646526885020355 := by
  unfold tailWord_2985915
  simp only [CollatzResearch.WordTrace]
  refine ⟨108905266977547383527623199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72603511318364922351748799 108905266977547383527623199)
  ·
    refine ⟨163357900466321075291434799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108905266977547383527623199 163357900466321075291434799)
    ·
      refine ⟨245036850699481612937152199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163357900466321075291434799 245036850699481612937152199)
      ·
        refine ⟨367555276049222419405728299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245036850699481612937152199 367555276049222419405728299)
        ·
          refine ⟨551332914073833629108592449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367555276049222419405728299 551332914073833629108592449)
          ·
            refine ⟨413499685555375221831444337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551332914073833629108592449 413499685555375221831444337)
            ·
              refine ⟨310124764166531416373583253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413499685555375221831444337 310124764166531416373583253)
              ·
                refine ⟨14537098320306160142511715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 310124764166531416373583253 14537098320306160142511715)
                ·
                  refine ⟨21805647480459240213767573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14537098320306160142511715 21805647480459240213767573)
                  ·
                    refine ⟨1022139725646526885020355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21805647480459240213767573 1022139725646526885020355)
                    ·
                      rfl

theorem cell22_2985915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_2985915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985915 prefixEnd_2985915 := by exact prefixLift 2985915
  have htrace : WordTrace (prefixWord ++ tailWord_2985915) baseStart_2985915 baseEnd_2985915 := by
    simpa [prefixWord, tailWord_2985915, baseEnd_2985915] using wordTrace_append hprefix tailTrace_2985915
  have hstable : (prefixWord ++ tailWord_2985915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985915).length < 2 ^ (prefixWord ++ tailWord_2985915).sum := by decide
  have hdescent : baseEnd_2985915 < baseStart_2985915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985932 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_2985932 : Nat := 118140960795 + 2985932 * 2 ^ 59
def prefixEnd_2985932 : Nat := 4983230072969 + 3 ^ 40 * 2985932 * 2
def baseEnd_2985932 : Nat := 1022145545093944507345303

theorem tailTrace_2985932 : CollatzResearch.WordTrace tailWord_2985932 prefixEnd_2985932 1022145545093944507345303 := by
  unfold tailWord_2985932
  simp only [CollatzResearch.WordTrace]
  refine ⟨54452943509242897715496025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72603924678990530287328033 54452943509242897715496025)
  ·
    refine ⟨40839707631932173286622019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54452943509242897715496025 40839707631932173286622019)
    ·
      refine ⟨61259561447898259929933029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40839707631932173286622019 61259561447898259929933029)
      ·
        refine ⟨11486167771480923736862443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61259561447898259929933029 11486167771480923736862443)
        ·
          refine ⟨17229251657221385605293665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11486167771480923736862443 17229251657221385605293665)
          ·
            refine ⟨12921938742916039203970249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17229251657221385605293665 12921938742916039203970249)
            ·
              refine ⟨9691454057187029402977687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12921938742916039203970249 9691454057187029402977687)
              ·
                refine ⟨14537181085780544104466531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9691454057187029402977687 14537181085780544104466531)
                ·
                  refine ⟨21805771628670816156699797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14537181085780544104466531 21805771628670816156699797)
                  ·
                    refine ⟨1022145545093944507345303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21805771628670816156699797 1022145545093944507345303)
                    ·
                      rfl

theorem cell22_2985932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_2985932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985932 prefixEnd_2985932 := by exact prefixLift 2985932
  have htrace : WordTrace (prefixWord ++ tailWord_2985932) baseStart_2985932 baseEnd_2985932 := by
    simpa [prefixWord, tailWord_2985932, baseEnd_2985932] using wordTrace_append hprefix tailTrace_2985932
  have hstable : (prefixWord ++ tailWord_2985932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985932).length < 2 ^ (prefixWord ++ tailWord_2985932).sum := by decide
  have hdescent : baseEnd_2985932 < baseStart_2985932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985996 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_2985996 : Nat := 118140960795 + 2985996 * 2 ^ 59
def prefixEnd_2985996 : Nat := 4983230072969 + 3 ^ 40 * 2985996 * 2
def baseEnd_2985996 : Nat := 1022167453601869673745107

theorem tailTrace_2985996 : CollatzResearch.WordTrace tailWord_2985996 prefixEnd_2985996 1022167453601869673745107 := by
  unfold tailWord_2985996
  simp only [CollatzResearch.WordTrace]
  refine ⟨54454110645126967180660921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72605480860169289574214561 54454110645126967180660921)
  ·
    refine ⟨40840582983845225385495691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54454110645126967180660921 40840582983845225385495691)
    ·
      refine ⟨61260874475767838078243537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40840582983845225385495691 61260874475767838078243537)
      ·
        refine ⟨45945655856825878558682653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61260874475767838078243537 45945655856825878558682653)
        ·
          refine ⟨17229620946309704459505995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45945655856825878558682653 17229620946309704459505995)
          ·
            refine ⟨25844431419464556689258993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17229620946309704459505995 25844431419464556689258993)
            ·
              refine ⟨19383323564598417516944245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25844431419464556689258993 19383323564598417516944245)
              ·
                refine ⟨1817186584181101642213523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19383323564598417516944245 1817186584181101642213523)
                ·
                  refine ⟨2725779876271652463320285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817186584181101642213523 2725779876271652463320285)
                  ·
                    refine ⟨1022167453601869673745107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2725779876271652463320285 1022167453601869673745107)
                    ·
                      rfl

theorem cell22_2985996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_2985996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2985996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2985996 prefixEnd_2985996 := by exact prefixLift 2985996
  have htrace : WordTrace (prefixWord ++ tailWord_2985996) baseStart_2985996 baseEnd_2985996 := by
    simpa [prefixWord, tailWord_2985996, baseEnd_2985996] using wordTrace_append hprefix tailTrace_2985996
  have hstable : (prefixWord ++ tailWord_2985996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985996).length < 2 ^ (prefixWord ++ tailWord_2985996).sum := by decide
  have hdescent : baseEnd_2985996 < baseStart_2985996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986013 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2986013 : Nat := 118140960795 + 2986013 * 2 ^ 59
def prefixEnd_2986013 : Nat := 4983230072969 + 3 ^ 40 * 2986013 * 2
def baseEnd_2986013 : Nat := 1022173273049287296070055

theorem tailTrace_2986013 : CollatzResearch.WordTrace tailWord_2986013 prefixEnd_2986013 1022173273049287296070055 := by
  unfold tailWord_2986013
  simp only [CollatzResearch.WordTrace]
  refine ⟨108908841331192346264690693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72605894220794897509793795 108908841331192346264690693)
  ·
    refine ⟨20420407749598564924629505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108908841331192346264690693 20420407749598564924629505)
    ·
      refine ⟨15315305812198923693472129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20420407749598564924629505 15315305812198923693472129)
      ·
        refine ⟨11486479359149192770104097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15315305812198923693472129 11486479359149192770104097)
        ·
          refine ⟨8614859519361894577578073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11486479359149192770104097 8614859519361894577578073)
          ·
            refine ⟨6461144639521420933183555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8614859519361894577578073 6461144639521420933183555)
            ·
              refine ⟨9691716959282131399775333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461144639521420933183555 9691716959282131399775333)
              ·
                refine ⟨1817196929865399637457875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9691716959282131399775333 1817196929865399637457875)
                ·
                  refine ⟨2725795394798099456186813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817196929865399637457875 2725795394798099456186813)
                  ·
                    refine ⟨1022173273049287296070055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2725795394798099456186813 1022173273049287296070055)
                    ·
                      rfl

theorem cell22_2986013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2986013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986013 prefixEnd_2986013 := by exact prefixLift 2986013
  have htrace : WordTrace (prefixWord ++ tailWord_2986013) baseStart_2986013 baseEnd_2986013 := by
    simpa [prefixWord, tailWord_2986013, baseEnd_2986013] using wordTrace_append hprefix tailTrace_2986013
  have hstable : (prefixWord ++ tailWord_2986013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986013).length < 2 ^ (prefixWord ++ tailWord_2986013).sum := by decide
  have hdescent : baseEnd_2986013 < baseStart_2986013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986037 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 8]
def baseStart_2986037 : Nat := 118140960795 + 2986037 * 2 ^ 59
def prefixEnd_2986037 : Nat := 4983230072969 + 3 ^ 40 * 2986037 * 2
def baseEnd_2986037 : Nat := 340727162913253077823327

theorem tailTrace_2986037 : CollatzResearch.WordTrace tailWord_2986037 prefixEnd_2986037 340727162913253077823327 := by
  unfold tailWord_2986037
  simp only [CollatzResearch.WordTrace]
  refine ⟨108909716683105398363564365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72606477788736932242376243 108909716683105398363564365)
  ·
    refine ⟨40841143756164524386336637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108909716683105398363564365 40841143756164524386336637)
    ·
      refine ⟨15315428908561696644876239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40841143756164524386336637 15315428908561696644876239)
      ·
        refine ⟨22973143362842544967314359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15315428908561696644876239 22973143362842544967314359)
        ·
          refine ⟨34459715044263817450971539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22973143362842544967314359 34459715044263817450971539)
          ·
            refine ⟨51689572566395726176457309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34459715044263817450971539 51689572566395726176457309)
            ·
              refine ⟨19383589712398397316171491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51689572566395726176457309 19383589712398397316171491)
              ·
                refine ⟨29075384568597595974257237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19383589712398397316171491 29075384568597595974257237)
                ·
                  refine ⟨340727162913253077823327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29075384568597595974257237 340727162913253077823327)
                  ·
                    rfl

theorem cell22_2986037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_2986037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986037 prefixEnd_2986037 := by exact prefixLift 2986037
  have htrace : WordTrace (prefixWord ++ tailWord_2986037) baseStart_2986037 baseEnd_2986037 := by
    simpa [prefixWord, tailWord_2986037, baseEnd_2986037] using wordTrace_append hprefix tailTrace_2986037
  have hstable : (prefixWord ++ tailWord_2986037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986037).length < 2 ^ (prefixWord ++ tailWord_2986037).sum := by decide
  have hdescent : baseEnd_2986037 < baseStart_2986037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986097 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_2986097 : Nat := 118140960795 + 2986097 * 2 ^ 59
def prefixEnd_2986097 : Nat := 4983230072969 + 3 ^ 40 * 2986097 * 2
def baseEnd_2986097 : Nat := 1022202027965939076969797

theorem tailTrace_2986097 : CollatzResearch.WordTrace tailWord_2986097 prefixEnd_2986097 1022202027965939076969797 := by
  unfold tailWord_2986097
  simp only [CollatzResearch.WordTrace]
  refine ⟨108911905062888028610748545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72607936708592019073832363 108911905062888028610748545)
  ·
    refine ⟨81683928797166021458061409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108911905062888028610748545 81683928797166021458061409)
    ·
      refine ⟨61262946597874516093546057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81683928797166021458061409 61262946597874516093546057)
      ·
        refine ⟨45947209948405887070159543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61262946597874516093546057 45947209948405887070159543)
        ·
          refine ⟨68920814922608830605239315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45947209948405887070159543 68920814922608830605239315)
          ·
            refine ⟨103381222383913245907858973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68920814922608830605239315 103381222383913245907858973)
            ·
              refine ⟨38767958393967467215447115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103381222383913245907858973 38767958393967467215447115)
              ·
                refine ⟨58151937590951200823170673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38767958393967467215447115 58151937590951200823170673)
                ·
                  refine ⟨43613953193213400617378005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58151937590951200823170673 43613953193213400617378005)
                  ·
                    refine ⟨1022202027965939076969797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43613953193213400617378005 1022202027965939076969797)
                    ·
                      rfl

theorem cell22_2986097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_2986097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986097 prefixEnd_2986097 := by exact prefixLift 2986097
  have htrace : WordTrace (prefixWord ++ tailWord_2986097) baseStart_2986097 baseEnd_2986097 := by
    simpa [prefixWord, tailWord_2986097, baseEnd_2986097] using wordTrace_append hprefix tailTrace_2986097
  have hstable : (prefixWord ++ tailWord_2986097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986097).length < 2 ^ (prefixWord ++ tailWord_2986097).sum := by decide
  have hdescent : baseEnd_2986097 < baseStart_2986097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986112 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_2986112 : Nat := 118140960795 + 2986112 * 2 ^ 59
def prefixEnd_2986112 : Nat := 4983230072969 + 3 ^ 40 * 2986112 * 2
def baseEnd_2986112 : Nat := 1022207162772484037844751

theorem tailTrace_2986112 : CollatzResearch.WordTrace tailWord_2986112 prefixEnd_2986112 1022207162772484037844751 := by
  unfold tailWord_2986112
  simp only [CollatzResearch.WordTrace]
  refine ⟨54456226078916843086272295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72608301438555790781696393 54456226078916843086272295)
  ·
    refine ⟨81684339118375264629408443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54456226078916843086272295 81684339118375264629408443)
    ·
      refine ⟨122526508677562896944112665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81684339118375264629408443 122526508677562896944112665)
      ·
        refine ⟨91894881508172172708084499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122526508677562896944112665 91894881508172172708084499)
        ·
          refine ⟨137842322262258259062126749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91894881508172172708084499 137842322262258259062126749)
          ·
            refine ⟨51690870848346847148297531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137842322262258259062126749 51690870848346847148297531)
            ·
              refine ⟨77536306272520270722446297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51690870848346847148297531 77536306272520270722446297)
              ·
                refine ⟨58152229704390203041834723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77536306272520270722446297 58152229704390203041834723)
                ·
                  refine ⟨87228344556585304562752085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58152229704390203041834723 87228344556585304562752085)
                  ·
                    refine ⟨1022207162772484037844751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87228344556585304562752085 1022207162772484037844751)
                    ·
                      rfl

theorem cell22_2986112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_2986112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986112 prefixEnd_2986112 := by exact prefixLift 2986112
  have htrace : WordTrace (prefixWord ++ tailWord_2986112) baseStart_2986112 baseEnd_2986112 := by
    simpa [prefixWord, tailWord_2986112, baseEnd_2986112] using wordTrace_append hprefix tailTrace_2986112
  have hstable : (prefixWord ++ tailWord_2986112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986112).length < 2 ^ (prefixWord ++ tailWord_2986112).sum := by decide
  have hdescent : baseEnd_2986112 < baseStart_2986112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986219 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 1, 6]
def baseStart_2986219 : Nat := 118140960795 + 2986219 * 2 ^ 59
def prefixEnd_2986219 : Nat := 4983230072969 + 3 ^ 40 * 2986219 * 2
def baseEnd_2986219 : Nat := 1022243791059171425419423

theorem tailTrace_2986219 : CollatzResearch.WordTrace tailWord_2986219 prefixEnd_2986219 1022243791059171425419423 := by
  unfold tailWord_2986219
  simp only [CollatzResearch.WordTrace]
  refine ⟨108916354768446043446689711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72610903178964028964459807 108916354768446043446689711)
  ·
    refine ⟨163374532152669065170034567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108916354768446043446689711 163374532152669065170034567)
    ·
      refine ⟨245061798229003597755051851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163374532152669065170034567 245061798229003597755051851)
      ·
        refine ⟨367592697343505396632577777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245061798229003597755051851 367592697343505396632577777)
        ·
          refine ⟨275694523007629047474433333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367592697343505396632577777 275694523007629047474433333)
          ·
            refine ⟨25846361531965223200728125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275694523007629047474433333 25846361531965223200728125)
            ·
              refine ⟨9692385574486958700273047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25846361531965223200728125 9692385574486958700273047)
              ·
                refine ⟨14538578361730438050409571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692385574486958700273047 14538578361730438050409571)
                ·
                  refine ⟨21807867542595657075614357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14538578361730438050409571 21807867542595657075614357)
                  ·
                    refine ⟨1022243791059171425419423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21807867542595657075614357 1022243791059171425419423)
                    ·
                      rfl

theorem cell22_2986219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_2986219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986219 prefixEnd_2986219 := by exact prefixLift 2986219
  have htrace : WordTrace (prefixWord ++ tailWord_2986219) baseStart_2986219 baseEnd_2986219 := by
    simpa [prefixWord, tailWord_2986219, baseEnd_2986219] using wordTrace_append hprefix tailTrace_2986219
  have hstable : (prefixWord ++ tailWord_2986219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986219).length < 2 ^ (prefixWord ++ tailWord_2986219).sum := by decide
  have hdescent : baseEnd_2986219 < baseStart_2986219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986223 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 4]
def baseStart_2986223 : Nat := 118140960795 + 2986223 * 2 ^ 59
def prefixEnd_2986223 : Nat := 4983230072969 + 3 ^ 40 * 2986223 * 2
def baseEnd_2986223 : Nat := 340748386780305582773137

theorem tailTrace_2986223 : CollatzResearch.WordTrace tailWord_2986223 prefixEnd_2986223 340748386780305582773137 := by
  unfold tailWord_2986223
  simp only [CollatzResearch.WordTrace]
  refine ⟨108916500660431552129835323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72611000440287701419890215 108916500660431552129835323)
  ·
    refine ⟨163374750990647328194752985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108916500660431552129835323 163374750990647328194752985)
    ·
      refine ⟨122531063242985496146064739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163374750990647328194752985 122531063242985496146064739)
      ·
        refine ⟨183796594864478244219097109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122531063242985496146064739 183796594864478244219097109)
        ·
          refine ⟨8615465384272417697770177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183796594864478244219097109 8615465384272417697770177)
          ·
            refine ⟨6461599038204313273327633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8615465384272417697770177 6461599038204313273327633)
            ·
              refine ⟨4846199278653234954995725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6461599038204313273327633 4846199278653234954995725)
              ·
                refine ⟨1817324729494963108123397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4846199278653234954995725 1817324729494963108123397)
                ·
                  refine ⟨340748386780305582773137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1817324729494963108123397 340748386780305582773137)
                  ·
                    rfl

theorem cell22_2986223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 4].length) (baseStart_2986223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986223 prefixEnd_2986223 := by exact prefixLift 2986223
  have htrace : WordTrace (prefixWord ++ tailWord_2986223) baseStart_2986223 baseEnd_2986223 := by
    simpa [prefixWord, tailWord_2986223, baseEnd_2986223] using wordTrace_append hprefix tailTrace_2986223
  have hstable : (prefixWord ++ tailWord_2986223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986223).length < 2 ^ (prefixWord ++ tailWord_2986223).sum := by decide
  have hdescent : baseEnd_2986223 < baseStart_2986223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986234 : List Nat := [3, 1, 1, 1, 1, 6, 9]
def baseStart_2986234 : Nat := 118140960795 + 2986234 * 2 ^ 59
def prefixEnd_2986234 : Nat := 4983230072969 + 3 ^ 40 * 2986234 * 2
def baseEnd_2986234 : Nat := 37861071328359866159051

theorem tailTrace_2986234 : CollatzResearch.WordTrace tailWord_2986234 prefixEnd_2986234 37861071328359866159051 := by
  unfold tailWord_2986234
  simp only [CollatzResearch.WordTrace]
  refine ⟨27229225465847925252121439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72611267908927800672323837 27229225465847925252121439)
  ·
    refine ⟨40843838198771887878182159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27229225465847925252121439 40843838198771887878182159)
    ·
      refine ⟨61265757298157831817273239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40843838198771887878182159 61265757298157831817273239)
      ·
        refine ⟨91898635947236747725909859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61265757298157831817273239 91898635947236747725909859)
        ·
          refine ⟨137847953920855121588864789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91898635947236747725909859 137847953920855121588864789)
          ·
            refine ⟨6461622840040083824478037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137847953920855121588864789 6461622840040083824478037)
            ·
              refine ⟨37861071328359866159051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6461622840040083824478037 37861071328359866159051)
              ·
                rfl

theorem cell22_2986234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 9].length) (baseStart_2986234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986234 prefixEnd_2986234 := by exact prefixLift 2986234
  have htrace : WordTrace (prefixWord ++ tailWord_2986234) baseStart_2986234 baseEnd_2986234 := by
    simpa [prefixWord, tailWord_2986234, baseEnd_2986234] using wordTrace_append hprefix tailTrace_2986234
  have hstable : (prefixWord ++ tailWord_2986234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986234).length < 2 ^ (prefixWord ++ tailWord_2986234).sum := by decide
  have hdescent : baseEnd_2986234 < baseStart_2986234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986238 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2986238 : Nat := 118140960795 + 2986238 * 2 ^ 59
def prefixEnd_2986238 : Nat := 4983230072969 + 3 ^ 40 * 2986238 * 2
def baseEnd_2986238 : Nat := 1022250295147461709194365

theorem tailTrace_2986238 : CollatzResearch.WordTrace tailWord_2986238 prefixEnd_2986238 1022250295147461709194365 := by
  unfold tailWord_2986238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13614630969422151211453921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72611365170251473127754245 13614630969422151211453921)
  ·
    refine ⟨10210973227066613408590441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13614630969422151211453921 10210973227066613408590441)
    ·
      refine ⟨7658229920299960056442831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10210973227066613408590441 7658229920299960056442831)
      ·
        refine ⟨11487344880449940084664247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658229920299960056442831 11487344880449940084664247)
        ·
          refine ⟨17231017320674910126996371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11487344880449940084664247 17231017320674910126996371)
          ·
            refine ⟨25846525981012365190494557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17231017320674910126996371 25846525981012365190494557)
            ·
              refine ⟨9692447242879636946435459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25846525981012365190494557 9692447242879636946435459)
              ·
                refine ⟨14538670864319455419653189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692447242879636946435459 14538670864319455419653189)
                ·
                  refine ⟨2726000787059897891184973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14538670864319455419653189 2726000787059897891184973)
                  ·
                    refine ⟨1022250295147461709194365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726000787059897891184973 1022250295147461709194365)
                    ·
                      rfl

theorem cell22_2986238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2986238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986238 prefixEnd_2986238 := by exact prefixLift 2986238
  have htrace : WordTrace (prefixWord ++ tailWord_2986238) baseStart_2986238 baseEnd_2986238 := by
    simpa [prefixWord, tailWord_2986238, baseEnd_2986238] using wordTrace_append hprefix tailTrace_2986238
  have hstable : (prefixWord ++ tailWord_2986238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986238).length < 2 ^ (prefixWord ++ tailWord_2986238).sum := by decide
  have hdescent : baseEnd_2986238 < baseStart_2986238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986285 : List Nat := [1, 5, 3, 1, 3, 1, 8]
def baseStart_2986285 : Nat := 118140960795 + 2986285 * 2 ^ 59
def prefixEnd_2986285 : Nat := 4983230072969 + 3 ^ 40 * 2986285 * 2
def baseEnd_2986285 : Nat := 37861717933628490861823

theorem tailTrace_2986285 : CollatzResearch.WordTrace tailWord_2986285 prefixEnd_2986285 37861717933628490861823 := by
  unfold tailWord_2986285
  simp only [CollatzResearch.WordTrace]
  refine ⟨108918761986206936718592309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72612507990804624479061539 108918761986206936718592309)
  ·
    refine ⟨10211133936206900317368029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108918761986206936718592309 10211133936206900317368029)
    ·
      refine ⟨3829175226077587619013011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10211133936206900317368029 3829175226077587619013011)
      ·
        refine ⟨5743762839116381428519517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829175226077587619013011 5743762839116381428519517)
        ·
          refine ⟨2153911064668643035694819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5743762839116381428519517 2153911064668643035694819)
          ·
            refine ⟨3230866597002964553542229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153911064668643035694819 3230866597002964553542229)
            ·
              refine ⟨37861717933628490861823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3230866597002964553542229 37861717933628490861823)
              ·
                rfl

theorem cell22_2986285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 8].length) (baseStart_2986285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986285 prefixEnd_2986285 := by exact prefixLift 2986285
  have htrace : WordTrace (prefixWord ++ tailWord_2986285) baseStart_2986285 baseEnd_2986285 := by
    simpa [prefixWord, tailWord_2986285, baseEnd_2986285] using wordTrace_append hprefix tailTrace_2986285
  have hstable : (prefixWord ++ tailWord_2986285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986285).length < 2 ^ (prefixWord ++ tailWord_2986285).sum := by decide
  have hdescent : baseEnd_2986285 < baseStart_2986285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986309 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2986309 : Nat := 118140960795 + 2986309 * 2 ^ 59
def prefixEnd_2986309 : Nat := 4983230072969 + 3 ^ 40 * 2986309 * 2
def baseEnd_2986309 : Nat := 1022274599898441190669147

theorem tailTrace_2986309 : CollatzResearch.WordTrace tailWord_2986309 prefixEnd_2986309 1022274599898441190669147 := by
  unfold tailWord_2986309
  simp only [CollatzResearch.WordTrace]
  refine ⟨108919637338119988817465981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72613091558746659211643987 108919637338119988817465981)
  ·
    refine ⟨40844864001794995806549743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108919637338119988817465981 40844864001794995806549743)
    ·
      refine ⟨61267296002692493709824615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40844864001794995806549743 61267296002692493709824615)
      ·
        refine ⟨91900944004038740564736923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61267296002692493709824615 91900944004038740564736923)
        ·
          refine ⟨137851416006058110847105385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91900944004038740564736923 137851416006058110847105385)
          ·
            refine ⟨103388562004543583135329039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137851416006058110847105385 103388562004543583135329039)
            ·
              refine ⟨155082843006815374702993559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103388562004543583135329039 155082843006815374702993559)
              ·
                refine ⟨232624264510223062054490339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155082843006815374702993559 232624264510223062054490339)
                ·
                  refine ⟨348936396765334593081735509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232624264510223062054490339 348936396765334593081735509)
                  ·
                    refine ⟨1022274599898441190669147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 348936396765334593081735509 1022274599898441190669147)
                    ·
                      rfl

theorem cell22_2986309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2986309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986309 prefixEnd_2986309 := by exact prefixLift 2986309
  have htrace : WordTrace (prefixWord ++ tailWord_2986309) baseStart_2986309 baseEnd_2986309 := by
    simpa [prefixWord, tailWord_2986309, baseEnd_2986309] using wordTrace_append hprefix tailTrace_2986309
  have hstable : (prefixWord ++ tailWord_2986309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986309).length < 2 ^ (prefixWord ++ tailWord_2986309).sum := by decide
  have hdescent : baseEnd_2986309 < baseStart_2986309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986407 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2986407 : Nat := 118140960795 + 2986407 * 2 ^ 59
def prefixEnd_2986407 : Nat := 4983230072969 + 3 ^ 40 * 2986407 * 2
def baseEnd_2986407 : Nat := 1022308147301201601718847

theorem tailTrace_2986407 : CollatzResearch.WordTrace tailWord_2986407 prefixEnd_2986407 1022308147301201601718847 := by
  unfold tailWord_2986407
  simp only [CollatzResearch.WordTrace]
  refine ⟨108923211691764951554533475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72615474461176634369688983 108923211691764951554533475)
  ·
    refine ⟨163384817537647427331800213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108923211691764951554533475 163384817537647427331800213)
    ·
      refine ⟨7658663322077223156178135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163384817537647427331800213 7658663322077223156178135)
      ·
        refine ⟨11487994983115834734267203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658663322077223156178135 11487994983115834734267203)
        ·
          refine ⟨17231992474673752101400805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11487994983115834734267203 17231992474673752101400805)
          ·
            refine ⟨3230998589001328519012651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17231992474673752101400805 3230998589001328519012651)
            ·
              refine ⟨4846497883501992778518977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230998589001328519012651 4846497883501992778518977)
              ·
                refine ⟨3634873412626494583889233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4846497883501992778518977 3634873412626494583889233)
                ·
                  refine ⟨2726155059469870937916925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634873412626494583889233 2726155059469870937916925)
                  ·
                    refine ⟨1022308147301201601718847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726155059469870937916925 1022308147301201601718847)
                    ·
                      rfl

theorem cell22_2986407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2986407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986407 prefixEnd_2986407 := by exact prefixLift 2986407
  have htrace : WordTrace (prefixWord ++ tailWord_2986407) baseStart_2986407 baseEnd_2986407 := by
    simpa [prefixWord, tailWord_2986407, baseEnd_2986407] using wordTrace_append hprefix tailTrace_2986407
  have hstable : (prefixWord ++ tailWord_2986407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986407).length < 2 ^ (prefixWord ++ tailWord_2986407).sum := by decide
  have hdescent : baseEnd_2986407 < baseStart_2986407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986469 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_2986469 : Nat := 118140960795 + 2986469 * 2 ^ 59
def prefixEnd_2986469 : Nat := 4983230072969 + 3 ^ 40 * 2986469 * 2
def baseEnd_2986469 : Nat := 1022329371168254106668657

theorem tailTrace_2986469 : CollatzResearch.WordTrace tailWord_2986469 prefixEnd_2986469 1022329371168254106668657 := by
  unfold tailWord_2986469
  simp only [CollatzResearch.WordTrace]
  refine ⟨108925473017540336143290461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72616982011693557428860307 108925473017540336143290461)
  ·
    refine ⟨40847052381577626053733923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108925473017540336143290461 40847052381577626053733923)
    ·
      refine ⟨61270578572366439080600885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40847052381577626053733923 61270578572366439080600885)
      ·
        refine ⟨5744116741159353663806333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61270578572366439080600885 5744116741159353663806333)
        ·
          refine ⟨2154043777934757623927375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5744116741159353663806333 2154043777934757623927375)
          ·
            refine ⟨3231065666902136435891063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154043777934757623927375 3231065666902136435891063)
            ·
              refine ⟨4846598500353204653836595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231065666902136435891063 4846598500353204653836595)
              ·
                refine ⟨7269897750529806980754893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846598500353204653836595 7269897750529806980754893)
                ·
                  refine ⟨2726211656448677617783085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7269897750529806980754893 2726211656448677617783085)
                  ·
                    refine ⟨1022329371168254106668657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726211656448677617783085 1022329371168254106668657)
                    ·
                      rfl

theorem cell22_2986469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_2986469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986469 prefixEnd_2986469 := by exact prefixLift 2986469
  have htrace : WordTrace (prefixWord ++ tailWord_2986469) baseStart_2986469 baseEnd_2986469 := by
    simpa [prefixWord, tailWord_2986469, baseEnd_2986469] using wordTrace_append hprefix tailTrace_2986469
  have hstable : (prefixWord ++ tailWord_2986469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986469).length < 2 ^ (prefixWord ++ tailWord_2986469).sum := by decide
  have hdescent : baseEnd_2986469 < baseStart_2986469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986508 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_2986508 : Nat := 118140960795 + 2986508 * 2 ^ 59
def prefixEnd_2986508 : Nat := 4983230072969 + 3 ^ 40 * 2986508 * 2
def baseEnd_2986508 : Nat := 1022342721665271004943537

theorem tailTrace_2986508 : CollatzResearch.WordTrace tailWord_2986508 prefixEnd_2986508 1022342721665271004943537 := by
  unfold tailWord_2986508
  simp only [CollatzResearch.WordTrace]
  refine ⟨54463447732199522901980089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72617930309599363869306785 54463447732199522901980089)
  ·
    refine ⟨40847585799149642176485067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54463447732199522901980089 40847585799149642176485067)
    ·
      refine ⟨61271378698724463264727601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40847585799149642176485067 61271378698724463264727601)
      ·
        refine ⟨45953534024043347448545701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61271378698724463264727601 45953534024043347448545701)
        ·
          refine ⟨8616287629508127646602319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45953534024043347448545701 8616287629508127646602319)
          ·
            refine ⟨12924431444262191469903479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616287629508127646602319 12924431444262191469903479)
            ·
              refine ⟨19386647166393287204855219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12924431444262191469903479 19386647166393287204855219)
              ·
                refine ⟨29079970749589930807282829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19386647166393287204855219 29079970749589930807282829)
                ·
                  refine ⟨10904989031096224052731061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29079970749589930807282829 10904989031096224052731061)
                  ·
                    refine ⟨1022342721665271004943537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10904989031096224052731061 1022342721665271004943537)
                    ·
                      rfl

theorem cell22_2986508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_2986508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986508 prefixEnd_2986508 := by exact prefixLift 2986508
  have htrace : WordTrace (prefixWord ++ tailWord_2986508) baseStart_2986508 baseEnd_2986508 := by
    simpa [prefixWord, tailWord_2986508, baseEnd_2986508] using wordTrace_append hprefix tailTrace_2986508
  have hstable : (prefixWord ++ tailWord_2986508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986508).length < 2 ^ (prefixWord ++ tailWord_2986508).sum := by decide
  have hdescent : baseEnd_2986508 < baseStart_2986508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986542 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2986542 : Nat := 118140960795 + 2986542 * 2 ^ 59
def prefixEnd_2986542 : Nat := 4983230072969 + 3 ^ 40 * 2986542 * 2
def baseEnd_2986542 : Nat := 1022354360560106249593433

theorem tailTrace_2986542 : CollatzResearch.WordTrace tailWord_2986542 prefixEnd_2986542 1022354360560106249593433 := by
  unfold tailWord_2986542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616016943284483701337235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72618757030850579740465253 13616016943284483701337235)
  ·
    refine ⟨20424025414926725552005853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13616016943284483701337235 20424025414926725552005853)
    ·
      refine ⟨7659009530597522082002195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20424025414926725552005853 7659009530597522082002195)
      ·
        refine ⟨11488514295896283123003293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7659009530597522082002195 11488514295896283123003293)
        ·
          refine ⟨4308192860961106171126235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11488514295896283123003293 4308192860961106171126235)
          ·
            refine ⟨6462289291441659256689353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308192860961106171126235 6462289291441659256689353)
            ·
              refine ⟨4846716968581244442517015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462289291441659256689353 4846716968581244442517015)
              ·
                refine ⟨7270075452871866663775523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846716968581244442517015 7270075452871866663775523)
                ·
                  refine ⟨10905113179307799995663285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270075452871866663775523 10905113179307799995663285)
                  ·
                    refine ⟨1022354360560106249593433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10905113179307799995663285 1022354360560106249593433)
                    ·
                      rfl

theorem cell22_2986542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2986542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986542 prefixEnd_2986542 := by exact prefixLift 2986542
  have htrace : WordTrace (prefixWord ++ tailWord_2986542) baseStart_2986542 baseEnd_2986542 := by
    simpa [prefixWord, tailWord_2986542, baseEnd_2986542] using wordTrace_append hprefix tailTrace_2986542
  have hstable : (prefixWord ++ tailWord_2986542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986542).length < 2 ^ (prefixWord ++ tailWord_2986542).sum := by decide
  have hdescent : baseEnd_2986542 < baseStart_2986542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986557 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2986557 : Nat := 118140960795 + 2986557 * 2 ^ 59
def prefixEnd_2986557 : Nat := 4983230072969 + 3 ^ 40 * 2986557 * 2
def baseEnd_2986557 : Nat := 1022359495366651210468387

theorem tailTrace_2986557 : CollatzResearch.WordTrace tailWord_2986557 prefixEnd_2986557 1022359495366651210468387 := by
  unfold tailWord_2986557
  simp only [CollatzResearch.WordTrace]
  refine ⟨108928682641221527172493925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72619121760814351448329283 108928682641221527172493925)
  ·
    refine ⟨20424127995229036344842611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108928682641221527172493925 20424127995229036344842611)
    ·
      refine ⟨30636191992843554517263917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20424127995229036344842611 30636191992843554517263917)
      ·
        refine ⟨11488571997316332943973969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30636191992843554517263917 11488571997316332943973969)
        ·
          refine ⟨8616428997987249707980477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11488571997316332943973969 8616428997987249707980477)
          ·
            refine ⟨3231160874245218640492679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8616428997987249707980477 3231160874245218640492679)
            ·
              refine ⟨4846741311367827960739019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231160874245218640492679 4846741311367827960739019)
              ·
                refine ⟨7270111967051741941108529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846741311367827960739019 7270111967051741941108529)
                ·
                  refine ⟨5452583975288806455831397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270111967051741941108529 5452583975288806455831397)
                  ·
                    refine ⟨1022359495366651210468387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452583975288806455831397 1022359495366651210468387)
                    ·
                      rfl

theorem cell22_2986557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2986557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986557 prefixEnd_2986557 := by exact prefixLift 2986557
  have htrace : WordTrace (prefixWord ++ tailWord_2986557) baseStart_2986557 baseEnd_2986557 := by
    simpa [prefixWord, tailWord_2986557, baseEnd_2986557] using wordTrace_append hprefix tailTrace_2986557
  have hstable : (prefixWord ++ tailWord_2986557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986557).length < 2 ^ (prefixWord ++ tailWord_2986557).sum := by decide
  have hdescent : baseEnd_2986557 < baseStart_2986557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986583 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 7]
def baseStart_2986583 : Nat := 118140960795 + 2986583 * 2 ^ 59
def prefixEnd_2986583 : Nat := 4983230072969 + 3 ^ 40 * 2986583 * 2
def baseEnd_2986583 : Nat := 340789465232665269772769

theorem tailTrace_2986583 : CollatzResearch.WordTrace tailWord_2986583 prefixEnd_2986583 340789465232665269772769 := by
  unfold tailWord_2986583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108929630939127333612940403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72619753959418222408626935 108929630939127333612940403)
  ·
    refine ⟨163394446408691000419410605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108929630939127333612940403 163394446408691000419410605)
    ·
      refine ⟨61272917403259125157278977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163394446408691000419410605 61272917403259125157278977)
      ·
        refine ⟨45954688052444343867959233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61272917403259125157278977 45954688052444343867959233)
        ·
          refine ⟨34466016039333257900969425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45954688052444343867959233 34466016039333257900969425)
          ·
            refine ⟨25849512029499943425727069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34466016039333257900969425 25849512029499943425727069)
            ·
              refine ⟨9693567011062478784647651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25849512029499943425727069 9693567011062478784647651)
              ·
                refine ⟨14540350516593718176971477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9693567011062478784647651 14540350516593718176971477)
                ·
                  refine ⟨340789465232665269772769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14540350516593718176971477 340789465232665269772769)
                  ·
                    rfl

theorem cell22_2986583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 7].length) (baseStart_2986583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986583 prefixEnd_2986583 := by exact prefixLift 2986583
  have htrace : WordTrace (prefixWord ++ tailWord_2986583) baseStart_2986583 baseEnd_2986583 := by
    simpa [prefixWord, tailWord_2986583, baseEnd_2986583] using wordTrace_append hprefix tailTrace_2986583
  have hstable : (prefixWord ++ tailWord_2986583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986583).length < 2 ^ (prefixWord ++ tailWord_2986583).sum := by decide
  have hdescent : baseEnd_2986583 < baseStart_2986583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986621 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2986621 : Nat := 118140960795 + 2986621 * 2 ^ 59
def prefixEnd_2986621 : Nat := 4983230072969 + 3 ^ 40 * 2986621 * 2
def baseEnd_2986621 : Nat := 1022381403874576376868191

theorem tailTrace_2986621 : CollatzResearch.WordTrace tailWord_2986621 prefixEnd_2986621 1022381403874576376868191 := by
  unfold tailWord_2986621
  simp only [CollatzResearch.WordTrace]
  refine ⟨108931016912989666102823717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72620677941993110735215811 108931016912989666102823717)
  ·
    refine ⟨20424565671185562394279447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108931016912989666102823717 20424565671185562394279447)
    ·
      refine ⟨30636848506778343591419171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20424565671185562394279447 30636848506778343591419171)
      ·
        refine ⟨45955272760167515387128757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30636848506778343591419171 45955272760167515387128757)
        ·
          refine ⟨4308306821265704567543321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45955272760167515387128757 4308306821265704567543321)
          ·
            refine ⟨3231230115949278425657491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4308306821265704567543321 3231230115949278425657491)
            ·
              refine ⟨4846845173923917638486237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231230115949278425657491 4846845173923917638486237)
              ·
                refine ⟨1817566940221469114432339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4846845173923917638486237 1817566940221469114432339)
                ·
                  refine ⟨2726350410332203671648509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817566940221469114432339 2726350410332203671648509)
                  ·
                    refine ⟨1022381403874576376868191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726350410332203671648509 1022381403874576376868191)
                    ·
                      rfl

theorem cell22_2986621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2986621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986621 prefixEnd_2986621 := by exact prefixLift 2986621
  have htrace : WordTrace (prefixWord ++ tailWord_2986621) baseStart_2986621 baseEnd_2986621 := by
    simpa [prefixWord, tailWord_2986621, baseEnd_2986621] using wordTrace_append hprefix tailTrace_2986621
  have hstable : (prefixWord ++ tailWord_2986621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986621).length < 2 ^ (prefixWord ++ tailWord_2986621).sum := by decide
  have hdescent : baseEnd_2986621 < baseStart_2986621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986643 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_2986643 : Nat := 118140960795 + 2986643 * 2 ^ 59
def prefixEnd_2986643 : Nat := 4983230072969 + 3 ^ 40 * 2986643 * 2
def baseEnd_2986643 : Nat := 1022388934924175652818123

theorem tailTrace_2986643 : CollatzResearch.WordTrace tailWord_2986643 prefixEnd_2986643 1022388934924175652818123 := by
  unfold tailWord_2986643
  simp only [CollatzResearch.WordTrace]
  refine ⟨108931819318909963860124583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72621212879273309240083055 108931819318909963860124583)
  ·
    refine ⟨163397728978364945790186875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108931819318909963860124583 163397728978364945790186875)
    ·
      refine ⟨245096593467547418685280313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163397728978364945790186875 245096593467547418685280313)
      ·
        refine ⟨183822445100660564013960235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245096593467547418685280313 183822445100660564013960235)
        ·
          refine ⟨275733667650990846020940353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183822445100660564013960235 275733667650990846020940353)
          ·
            refine ⟨206800250738243134515705265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275733667650990846020940353 206800250738243134515705265)
            ·
              refine ⟨155100188053682350886778949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206800250738243134515705265 155100188053682350886778949)
              ·
                refine ⟨29081285260065440791271053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155100188053682350886778949 29081285260065440791271053)
                ·
                  refine ⟨10905481972524540296726645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29081285260065440791271053 10905481972524540296726645)
                  ·
                    refine ⟨1022388934924175652818123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10905481972524540296726645 1022388934924175652818123)
                    ·
                      rfl

theorem cell22_2986643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_2986643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986643 prefixEnd_2986643 := by exact prefixLift 2986643
  have htrace : WordTrace (prefixWord ++ tailWord_2986643) baseStart_2986643 baseEnd_2986643 := by
    simpa [prefixWord, tailWord_2986643, baseEnd_2986643] using wordTrace_append hprefix tailTrace_2986643
  have hstable : (prefixWord ++ tailWord_2986643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986643).length < 2 ^ (prefixWord ++ tailWord_2986643).sum := by decide
  have hdescent : baseEnd_2986643 < baseStart_2986643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986660 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_2986660 : Nat := 118140960795 + 2986660 * 2 ^ 59
def prefixEnd_2986660 : Nat := 4983230072969 + 3 ^ 40 * 2986660 * 2
def baseEnd_2986660 : Nat := 1022394754371593275143071

theorem tailTrace_2986660 : CollatzResearch.WordTrace tailWord_2986660 prefixEnd_2986660 1022394754371593275143071 := by
  unfold tailWord_2986660
  simp only [CollatzResearch.WordTrace]
  refine ⟨54466219679924187881746717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72621626239898917175662289 54466219679924187881746717)
  ·
    refine ⟨20424832379971570455655019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54466219679924187881746717 20424832379971570455655019)
    ·
      refine ⟨30637248569957355683482529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20424832379971570455655019 30637248569957355683482529)
      ·
        refine ⟨22977936427468016762611897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30637248569957355683482529 22977936427468016762611897)
        ·
          refine ⟨17233452320601012571958923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22977936427468016762611897 17233452320601012571958923)
          ·
            refine ⟨25850178480901518857938385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17233452320601012571958923 25850178480901518857938385)
            ·
              refine ⟨19387633860676139143453789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25850178480901518857938385 19387633860676139143453789)
              ·
                refine ⟨7270362697753552178795171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19387633860676139143453789 7270362697753552178795171)
                ·
                  refine ⟨10905544046630328268192757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270362697753552178795171 10905544046630328268192757)
                  ·
                    refine ⟨1022394754371593275143071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10905544046630328268192757 1022394754371593275143071)
                    ·
                      rfl

theorem cell22_2986660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_2986660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986660 prefixEnd_2986660 := by exact prefixLift 2986660
  have htrace : WordTrace (prefixWord ++ tailWord_2986660) baseStart_2986660 baseEnd_2986660 := by
    simpa [prefixWord, tailWord_2986660, baseEnd_2986660] using wordTrace_append hprefix tailTrace_2986660
  have hstable : (prefixWord ++ tailWord_2986660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986660).length < 2 ^ (prefixWord ++ tailWord_2986660).sum := by decide
  have hdescent : baseEnd_2986660 < baseStart_2986660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986675 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 2, 4]
def baseStart_2986675 : Nat := 118140960795 + 2986675 * 2 ^ 59
def prefixEnd_2986675 : Nat := 4983230072969 + 3 ^ 40 * 2986675 * 2
def baseEnd_2986675 : Nat := 1022399889178138236018025

theorem tailTrace_2986675 : CollatzResearch.WordTrace tailWord_2986675 prefixEnd_2986675 1022399889178138236018025 := by
  unfold tailWord_2986675
  simp only [CollatzResearch.WordTrace]
  refine ⟨108932986454794033325289479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72621990969862688883526319 108932986454794033325289479)
  ·
    refine ⟨163399479682191049987934219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108932986454794033325289479 163399479682191049987934219)
    ·
      refine ⟨245099219523286574981901329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163399479682191049987934219 245099219523286574981901329)
      ·
        refine ⟨183824414642464931236425997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245099219523286574981901329 183824414642464931236425997)
        ·
          refine ⟨68934155490924349213659749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183824414642464931236425997 68934155490924349213659749)
          ·
            refine ⟨12925154154548315477561203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68934155490924349213659749 12925154154548315477561203)
            ·
              refine ⟨19387731231822473216341805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925154154548315477561203 19387731231822473216341805)
              ·
                refine ⟨7270399211933427456128177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19387731231822473216341805 7270399211933427456128177)
                ·
                  refine ⟨5452799408950070592096133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270399211933427456128177 5452799408950070592096133)
                  ·
                    refine ⟨1022399889178138236018025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452799408950070592096133 1022399889178138236018025)
                    ·
                      rfl

theorem cell22_2986675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_2986675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986675 prefixEnd_2986675 := by exact prefixLift 2986675
  have htrace : WordTrace (prefixWord ++ tailWord_2986675) baseStart_2986675 baseEnd_2986675 := by
    simpa [prefixWord, tailWord_2986675, baseEnd_2986675] using wordTrace_append hprefix tailTrace_2986675
  have hstable : (prefixWord ++ tailWord_2986675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986675).length < 2 ^ (prefixWord ++ tailWord_2986675).sum := by decide
  have hdescent : baseEnd_2986675 < baseStart_2986675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986677 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2986677 : Nat := 118140960795 + 2986677 * 2 ^ 59
def prefixEnd_2986677 : Nat := 4983230072969 + 3 ^ 40 * 2986677 * 2
def baseEnd_2986677 : Nat := 1022400573819010897468019

theorem tailTrace_2986677 : CollatzResearch.WordTrace tailWord_2986677 prefixEnd_2986677 1022400573819010897468019 := by
  unfold tailWord_2986677
  simp only [CollatzResearch.WordTrace]
  refine ⟨108933059400786787666862285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72622039600524525111241523 108933059400786787666862285)
  ·
    refine ⟨40849897275295045375073357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108933059400786787666862285 40849897275295045375073357)
    ·
      refine ⟨15318711478235642015652509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40849897275295045375073357 15318711478235642015652509)
      ·
        refine ⟨5744516804338365755869691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15318711478235642015652509 5744516804338365755869691)
        ·
          refine ⟨8616775206507548633804537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744516804338365755869691 8616775206507548633804537)
          ·
            refine ⟨6462581404880661475353403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616775206507548633804537 6462581404880661475353403)
            ·
              refine ⟨9693872107320992213030105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6462581404880661475353403 9693872107320992213030105)
              ·
                refine ⟨7270404080490744159772579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9693872107320992213030105 7270404080490744159772579)
                ·
                  refine ⟨10905606120736116239658869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270404080490744159772579 10905606120736116239658869)
                  ·
                    refine ⟨1022400573819010897468019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10905606120736116239658869 1022400573819010897468019)
                    ·
                      rfl

theorem cell22_2986677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2986677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986677 prefixEnd_2986677 := by exact prefixLift 2986677
  have htrace : WordTrace (prefixWord ++ tailWord_2986677) baseStart_2986677 baseEnd_2986677 := by
    simpa [prefixWord, tailWord_2986677, baseEnd_2986677] using wordTrace_append hprefix tailTrace_2986677
  have hstable : (prefixWord ++ tailWord_2986677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986677).length < 2 ^ (prefixWord ++ tailWord_2986677).sum := by decide
  have hdescent : baseEnd_2986677 < baseStart_2986677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986692 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2986692 : Nat := 118140960795 + 2986692 * 2 ^ 59
def prefixEnd_2986692 : Nat := 4983230072969 + 3 ^ 40 * 2986692 * 2
def baseEnd_2986692 : Nat := 1022405708625555858342973

theorem tailTrace_2986692 : CollatzResearch.WordTrace tailWord_2986692 prefixEnd_2986692 1022405708625555858342973 := by
  unfold tailWord_2986692
  simp only [CollatzResearch.WordTrace]
  refine ⟨54466803247866222614329165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72622404330488296819105553 54466803247866222614329165)
  ·
    refine ⟨20425051217949833480373437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54466803247866222614329165 20425051217949833480373437)
    ·
      refine ⟨7659394206731187555140039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20425051217949833480373437 7659394206731187555140039)
      ·
        refine ⟨11489091310096781332710059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7659394206731187555140039 11489091310096781332710059)
        ·
          refine ⟨17233636965145171999065089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11489091310096781332710059 17233636965145171999065089)
          ·
            refine ⟨12925227723858878999298817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17233636965145171999065089 12925227723858878999298817)
            ·
              refine ⟨9693920792894159249474113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12925227723858878999298817 9693920792894159249474113)
              ·
                refine ⟨7270440594670619437105585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9693920792894159249474113 7270440594670619437105585)
                ·
                  refine ⟨5452830446002964577829189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270440594670619437105585 5452830446002964577829189)
                  ·
                    refine ⟨1022405708625555858342973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452830446002964577829189 1022405708625555858342973)
                    ·
                      rfl

theorem cell22_2986692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2986692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986692 prefixEnd_2986692 := by exact prefixLift 2986692
  have htrace : WordTrace (prefixWord ++ tailWord_2986692) baseStart_2986692 baseEnd_2986692 := by
    simpa [prefixWord, tailWord_2986692, baseEnd_2986692] using wordTrace_append hprefix tailTrace_2986692
  have hstable : (prefixWord ++ tailWord_2986692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986692).length < 2 ^ (prefixWord ++ tailWord_2986692).sum := by decide
  have hdescent : baseEnd_2986692 < baseStart_2986692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986820 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 5]
def baseStart_2986820 : Nat := 118140960795 + 2986820 * 2 ^ 59
def prefixEnd_2986820 : Nat := 4983230072969 + 3 ^ 40 * 2986820 * 2
def baseEnd_2986820 : Nat := 340816508547135397047527

theorem tailTrace_2986820 : CollatzResearch.WordTrace tailWord_2986820 prefixEnd_2986820 340816508547135397047527 := by
  unfold tailWord_2986820
  simp only [CollatzResearch.WordTrace]
  refine ⟨54469137519634361544658957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72625516692845815392878609 54469137519634361544658957)
  ·
    refine ⟨20425926569862885579247109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54469137519634361544658957 20425926569862885579247109)
    ·
      refine ⟨3829861231849291046108833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20425926569862885579247109 3829861231849291046108833)
      ·
        refine ⟨2872395923886968284581625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3829861231849291046108833 2872395923886968284581625)
        ·
          refine ⟨2154296942915226213436219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2872395923886968284581625 2154296942915226213436219)
          ·
            refine ⟨3231445414372839320154329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154296942915226213436219 3231445414372839320154329)
            ·
              refine ⟨2423584060779629490115747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231445414372839320154329 2423584060779629490115747)
              ·
                refine ⟨3635376091169444235173621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423584060779629490115747 3635376091169444235173621)
                ·
                  refine ⟨340816508547135397047527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3635376091169444235173621 340816508547135397047527)
                  ·
                    rfl

theorem cell22_2986820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_2986820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986820 prefixEnd_2986820 := by exact prefixLift 2986820
  have htrace : WordTrace (prefixWord ++ tailWord_2986820) baseStart_2986820 baseEnd_2986820 := by
    simpa [prefixWord, tailWord_2986820, baseEnd_2986820] using wordTrace_append hprefix tailTrace_2986820
  have hstable : (prefixWord ++ tailWord_2986820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986820).length < 2 ^ (prefixWord ++ tailWord_2986820).sum := by decide
  have hdescent : baseEnd_2986820 < baseStart_2986820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986825 : List Nat := [1, 2, 1, 1, 2, 5, 1, 9]
def baseStart_2986825 : Nat := 118140960795 + 2986825 * 2 ^ 59
def prefixEnd_2986825 : Nat := 4983230072969 + 3 ^ 40 * 2986825 * 2
def baseEnd_2986825 : Nat := 113605693027065316085285

theorem tailTrace_2986825 : CollatzResearch.WordTrace tailWord_2986825 prefixEnd_2986825 113605693027065316085285 := by
  unfold tailWord_2986825
  simp only [CollatzResearch.WordTrace]
  refine ⟨108938457404250608943249929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72625638269500405962166619 108938457404250608943249929)
  ·
    refine ⟨81703843053187956707437447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108938457404250608943249929 81703843053187956707437447)
    ·
      refine ⟨122555764579781935061156171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81703843053187956707437447 122555764579781935061156171)
      ·
        refine ⟨183833646869672902591734257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122555764579781935061156171 183833646869672902591734257)
        ·
          refine ⟨137875235152254676943800693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183833646869672902591734257 137875235152254676943800693)
          ·
            refine ⟨12925803295523875963481315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137875235152254676943800693 12925803295523875963481315)
            ·
              refine ⟨19388704943285813945221973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925803295523875963481315 19388704943285813945221973)
              ·
                refine ⟨113605693027065316085285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19388704943285813945221973 113605693027065316085285)
                ·
                  rfl

theorem cell22_2986825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 9].length) (baseStart_2986825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986825 prefixEnd_2986825 := by exact prefixLift 2986825
  have htrace : WordTrace (prefixWord ++ tailWord_2986825) baseStart_2986825 baseEnd_2986825 := by
    simpa [prefixWord, tailWord_2986825, baseEnd_2986825] using wordTrace_append hprefix tailTrace_2986825
  have hstable : (prefixWord ++ tailWord_2986825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986825).length < 2 ^ (prefixWord ++ tailWord_2986825).sum := by decide
  have hdescent : baseEnd_2986825 < baseStart_2986825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986840 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_2986840 : Nat := 118140960795 + 2986840 * 2 ^ 59
def prefixEnd_2986840 : Nat := 4983230072969 + 3 ^ 40 * 2986840 * 2
def baseEnd_2986840 : Nat := 1022456372050132805642519

theorem tailTrace_2986840 : CollatzResearch.WordTrace tailWord_2986840 prefixEnd_2986840 1022456372050132805642519 := by
  unfold tailWord_2986840
  simp only [CollatzResearch.WordTrace]
  refine ⟨54469502249598133252522987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72626002999464177670030649 54469502249598133252522987)
  ·
    refine ⟨81704253374397199878784481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54469502249598133252522987 81704253374397199878784481)
    ·
      refine ⟨61278190030797899909088361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81704253374397199878784481 61278190030797899909088361)
      ·
        refine ⟨45958642523098424931816271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61278190030797899909088361 45958642523098424931816271)
        ·
          refine ⟨68937963784647637397724407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45958642523098424931816271 68937963784647637397724407)
          ·
            refine ⟨103406945676971456096586611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68937963784647637397724407 103406945676971456096586611)
            ·
              refine ⟨155110418515457184144879917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103406945676971456096586611 155110418515457184144879917)
              ·
                refine ⟨58166406943296444054329969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155110418515457184144879917 58166406943296444054329969)
                ·
                  refine ⟨43624805207472333040747477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58166406943296444054329969 43624805207472333040747477)
                  ·
                    refine ⟨1022456372050132805642519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43624805207472333040747477 1022456372050132805642519)
                    ·
                      rfl

theorem cell22_2986840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_2986840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986840 prefixEnd_2986840 := by exact prefixLift 2986840
  have htrace : WordTrace (prefixWord ++ tailWord_2986840) baseStart_2986840 baseEnd_2986840 := by
    simpa [prefixWord, tailWord_2986840, baseEnd_2986840] using wordTrace_append hprefix tailTrace_2986840
  have hstable : (prefixWord ++ tailWord_2986840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986840).length < 2 ^ (prefixWord ++ tailWord_2986840).sum := by decide
  have hdescent : baseEnd_2986840 < baseStart_2986840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986844 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2986844 : Nat := 118140960795 + 2986844 * 2 ^ 59
def prefixEnd_2986844 : Nat := 4983230072969 + 3 ^ 40 * 2986844 * 2
def baseEnd_2986844 : Nat := 1022457741331878128542507

theorem tailTrace_2986844 : CollatzResearch.WordTrace tailWord_2986844 prefixEnd_2986844 1022457741331878128542507 := by
  unfold tailWord_2986844
  simp only [CollatzResearch.WordTrace]
  refine ⟨54469575195590887594095793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72626100260787850125461057 54469575195590887594095793)
  ·
    refine ⟨40852181396693165695571845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54469575195590887594095793 40852181396693165695571845)
    ·
      refine ⟨7659784011879968567919721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40852181396693165695571845 7659784011879968567919721)
      ·
        refine ⟨5744838008909976425939791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7659784011879968567919721 5744838008909976425939791)
        ·
          refine ⟨8617257013364964638909687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744838008909976425939791 8617257013364964638909687)
          ·
            refine ⟨12925885520047446958364531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617257013364964638909687 12925885520047446958364531)
            ·
              refine ⟨19388828280071170437546797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925885520047446958364531 19388828280071170437546797)
              ·
                refine ⟨7270810605026688914080049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19388828280071170437546797 7270810605026688914080049)
                ·
                  refine ⟨5453107953770016685560037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270810605026688914080049 5453107953770016685560037)
                  ·
                    refine ⟨1022457741331878128542507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453107953770016685560037 1022457741331878128542507)
                    ·
                      rfl

theorem cell22_2986844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2986844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986844 prefixEnd_2986844 := by exact prefixLift 2986844
  have htrace : WordTrace (prefixWord ++ tailWord_2986844) baseStart_2986844 baseEnd_2986844 := by
    simpa [prefixWord, tailWord_2986844, baseEnd_2986844] using wordTrace_append hprefix tailTrace_2986844
  have hstable : (prefixWord ++ tailWord_2986844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986844).length < 2 ^ (prefixWord ++ tailWord_2986844).sum := by decide
  have hdescent : baseEnd_2986844 < baseStart_2986844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986979 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 2, 4]
def baseStart_2986979 : Nat := 118140960795 + 2986979 * 2 ^ 59
def prefixEnd_2986979 : Nat := 4983230072969 + 3 ^ 40 * 2986979 * 2
def baseEnd_2986979 : Nat := 1022503954590782776417093

theorem tailTrace_2986979 : CollatzResearch.WordTrace tailWord_2986979 prefixEnd_2986979 1022503954590782776417093 := by
  unfold tailWord_2986979
  simp only [CollatzResearch.WordTrace]
  refine ⟨108944074245692693244355991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72629382830461795496237327 108944074245692693244355991)
  ·
    refine ⟨163416111368539039866533987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108944074245692693244355991 163416111368539039866533987)
    ·
      refine ⟨245124167052808559799800981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163416111368539039866533987 245124167052808559799800981)
      ·
        refine ⟨11490195330600401240615671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245124167052808559799800981 11490195330600401240615671)
        ·
          refine ⟨17235292995900601860923507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11490195330600401240615671 17235292995900601860923507)
          ·
            refine ⟨25852939493850902791385261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17235292995900601860923507 25852939493850902791385261)
            ·
              refine ⟨9694852310194088546769473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25852939493850902791385261 9694852310194088546769473)
              ·
                refine ⟨7271139232645566410077105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9694852310194088546769473 7271139232645566410077105)
                ·
                  refine ⟨5453354424484174807557829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7271139232645566410077105 5453354424484174807557829)
                  ·
                    refine ⟨1022503954590782776417093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453354424484174807557829 1022503954590782776417093)
                    ·
                      rfl

theorem cell22_2986979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_2986979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986979 prefixEnd_2986979 := by exact prefixLift 2986979
  have htrace : WordTrace (prefixWord ++ tailWord_2986979) baseStart_2986979 baseEnd_2986979 := by
    simpa [prefixWord, tailWord_2986979, baseEnd_2986979] using wordTrace_append hprefix tailTrace_2986979
  have hstable : (prefixWord ++ tailWord_2986979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986979).length < 2 ^ (prefixWord ++ tailWord_2986979).sum := by decide
  have hdescent : baseEnd_2986979 < baseStart_2986979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986983 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 4]
def baseStart_2986983 : Nat := 118140960795 + 2986983 * 2 ^ 59
def prefixEnd_2986983 : Nat := 4983230072969 + 3 ^ 40 * 2986983 * 2
def baseEnd_2986983 : Nat := 340835107957509366439027

theorem tailTrace_2986983 : CollatzResearch.WordTrace tailWord_2986983 prefixEnd_2986983 340835107957509366439027 := by
  unfold tailWord_2986983
  simp only [CollatzResearch.WordTrace]
  refine ⟨108944220137678201927501603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72629480091785467951667735 108944220137678201927501603)
  ·
    refine ⟨163416330206517302891252405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108944220137678201927501603 163416330206517302891252405)
    ·
      refine ⟨15320280956860997146054913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163416330206517302891252405 15320280956860997146054913)
      ·
        refine ⟨11490210717645747859541185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15320280956860997146054913 11490210717645747859541185)
        ·
          refine ⟨8617658038234310894655889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11490210717645747859541185 8617658038234310894655889)
          ·
            refine ⟨6463243528675733170991917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8617658038234310894655889 6463243528675733170991917)
            ·
              refine ⟨2423716323253399939121969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6463243528675733170991917 2423716323253399939121969)
              ·
                refine ⟨1817787242440049954341477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423716323253399939121969 1817787242440049954341477)
                ·
                  refine ⟨340835107957509366439027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1817787242440049954341477 340835107957509366439027)
                  ·
                    rfl

theorem cell22_2986983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 4].length) (baseStart_2986983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986983 prefixEnd_2986983 := by exact prefixLift 2986983
  have htrace : WordTrace (prefixWord ++ tailWord_2986983) baseStart_2986983 baseEnd_2986983 := by
    simpa [prefixWord, tailWord_2986983, baseEnd_2986983] using wordTrace_append hprefix tailTrace_2986983
  have hstable : (prefixWord ++ tailWord_2986983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986983).length < 2 ^ (prefixWord ++ tailWord_2986983).sum := by decide
  have hdescent : baseEnd_2986983 < baseStart_2986983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986998 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_2986998 : Nat := 118140960795 + 2986998 * 2 ^ 59
def prefixEnd_2986998 : Nat := 4983230072969 + 3 ^ 40 * 2986998 * 2
def baseEnd_2986998 : Nat := 1022510458679073060192035

theorem tailTrace_2986998 : CollatzResearch.WordTrace tailWord_2986998 prefixEnd_2986998 1022510458679073060192035 := by
  unfold tailWord_2986998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809047952038991218081103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72629844821749239659531765 6809047952038991218081103)
  ·
    refine ⟨10213571928058486827121655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6809047952038991218081103 10213571928058486827121655)
    ·
      refine ⟨15320357892087730240682483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213571928058486827121655 15320357892087730240682483)
      ·
        refine ⟨22980536838131595361023725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15320357892087730240682483 22980536838131595361023725)
        ·
          refine ⟨8617701314299348260383897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22980536838131595361023725 8617701314299348260383897)
          ·
            refine ⟨6463275985724511195287923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8617701314299348260383897 6463275985724511195287923)
            ·
              refine ⟨9694913978586766792931885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463275985724511195287923 9694913978586766792931885)
              ·
                refine ⟨3635592741970037547349457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9694913978586766792931885 3635592741970037547349457)
                ·
                  refine ⟨2726694556477528160512093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635592741970037547349457 2726694556477528160512093)
                  ·
                    refine ⟨1022510458679073060192035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726694556477528160512093 1022510458679073060192035)
                    ·
                      rfl

theorem cell22_2986998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_2986998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2986998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2986998 prefixEnd_2986998 := by exact prefixLift 2986998
  have htrace : WordTrace (prefixWord ++ tailWord_2986998) baseStart_2986998 baseEnd_2986998 := by
    simpa [prefixWord, tailWord_2986998, baseEnd_2986998] using wordTrace_append hprefix tailTrace_2986998
  have hstable : (prefixWord ++ tailWord_2986998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986998).length < 2 ^ (prefixWord ++ tailWord_2986998).sum := by decide
  have hdescent : baseEnd_2986998 < baseStart_2986998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987039 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 5]
def baseStart_2987039 : Nat := 118140960795 + 2987039 * 2 ^ 59
def prefixEnd_2987039 : Nat := 4983230072969 + 3 ^ 40 * 2987039 * 2
def baseEnd_2987039 : Nat := 340841497938987539972303

theorem tailTrace_2987039 : CollatzResearch.WordTrace tailWord_2987039 prefixEnd_2987039 340841497938987539972303 := by
  unfold tailWord_2987039
  simp only [CollatzResearch.WordTrace]
  refine ⟨108946262625475323491540171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72630841750316882327693447 108946262625475323491540171)
  ·
    refine ⟨163419393938212985237310257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108946262625475323491540171 163419393938212985237310257)
    ·
      refine ⟨122564545453659738927982693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163419393938212985237310257 122564545453659738927982693)
      ·
        refine ⟨22980852272561201048996755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122564545453659738927982693 22980852272561201048996755)
        ·
          refine ⟨34471278408841801573495133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22980852272561201048996755 34471278408841801573495133)
          ·
            refine ⟨12926729403315675590060675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34471278408841801573495133 12926729403315675590060675)
            ·
              refine ⟨19390094104973513385091013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12926729403315675590060675 19390094104973513385091013)
              ·
                refine ⟨3635642644682533759704565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19390094104973513385091013 3635642644682533759704565)
                ·
                  refine ⟨340841497938987539972303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3635642644682533759704565 340841497938987539972303)
                  ·
                    rfl

theorem cell22_2987039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 5].length) (baseStart_2987039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987039 prefixEnd_2987039 := by exact prefixLift 2987039
  have htrace : WordTrace (prefixWord ++ tailWord_2987039) baseStart_2987039 baseEnd_2987039 := by
    simpa [prefixWord, tailWord_2987039, baseEnd_2987039] using wordTrace_append hprefix tailTrace_2987039
  have hstable : (prefixWord ++ tailWord_2987039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987039).length < 2 ^ (prefixWord ++ tailWord_2987039).sum := by decide
  have hdescent : baseEnd_2987039 < baseStart_2987039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987043 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 1, 3]
def baseStart_2987043 : Nat := 118140960795 + 2987043 * 2 ^ 59
def prefixEnd_2987043 : Nat := 4983230072969 + 3 ^ 40 * 2987043 * 2
def baseEnd_2987043 : Nat := 1022525863098707942816897

theorem tailTrace_2987043 : CollatzResearch.WordTrace tailWord_2987043 prefixEnd_2987043 1022525863098707942816897 := by
  unfold tailWord_2987043
  simp only [CollatzResearch.WordTrace]
  refine ⟨108946408517460832174685783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72630939011640554783123855 108946408517460832174685783)
  ·
    refine ⟨163419612776191248262028675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108946408517460832174685783 163419612776191248262028675)
    ·
      refine ⟨245129419164286872393043013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163419612776191248262028675 245129419164286872393043013)
      ·
        refine ⟨45961766093303788573695565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245129419164286872393043013 45961766093303788573695565)
        ·
          refine ⟨17235662284988920715135837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45961766093303788573695565 17235662284988920715135837)
          ·
            refine ⟨6463373356870845268175939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17235662284988920715135837 6463373356870845268175939)
            ·
              refine ⟨9695060035306267902263909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463373356870845268175939 9695060035306267902263909)
              ·
                refine ⟨1817823756619925231674483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9695060035306267902263909 1817823756619925231674483)
                ·
                  refine ⟨2726735634929887847511725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817823756619925231674483 2726735634929887847511725)
                  ·
                    refine ⟨1022525863098707942816897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726735634929887847511725 1022525863098707942816897)
                    ·
                      rfl

theorem cell22_2987043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 3].length) (baseStart_2987043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987043 prefixEnd_2987043 := by exact prefixLift 2987043
  have htrace : WordTrace (prefixWord ++ tailWord_2987043) baseStart_2987043 baseEnd_2987043 := by
    simpa [prefixWord, tailWord_2987043, baseEnd_2987043] using wordTrace_append hprefix tailTrace_2987043
  have hstable : (prefixWord ++ tailWord_2987043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987043).length < 2 ^ (prefixWord ++ tailWord_2987043).sum := by decide
  have hdescent : baseEnd_2987043 < baseStart_2987043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987086 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2987086 : Nat := 118140960795 + 2987086 * 2 ^ 59
def prefixEnd_2987086 : Nat := 4983230072969 + 3 ^ 40 * 2987086 * 2
def baseEnd_2987086 : Nat := 1022540582877470163991765

theorem tailTrace_2987086 : CollatzResearch.WordTrace tailWord_2987086 prefixEnd_2987086 1022540582877470163991765 := by
  unfold tailWord_2987086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13618497107038131314812639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72631984570870033679000741 13618497107038131314812639)
  ·
    refine ⟨20427745660557196972218959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13618497107038131314812639 20427745660557196972218959)
    ·
      refine ⟨30641618490835795458328439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20427745660557196972218959 30641618490835795458328439)
      ·
        refine ⟨45962427736253693187492659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30641618490835795458328439 45962427736253693187492659)
        ·
          refine ⟨68943641604380539781238989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45962427736253693187492659 68943641604380539781238989)
          ·
            refine ⟨25853865601642702417964621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68943641604380539781238989 25853865601642702417964621)
            ·
              refine ⟨9695199600616013406736733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25853865601642702417964621 9695199600616013406736733)
              ·
                refine ⟨3635699850231005027526275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9695199600616013406736733 3635699850231005027526275)
                ·
                  refine ⟨5453549775346507541289413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635699850231005027526275 5453549775346507541289413)
                  ·
                    refine ⟨1022540582877470163991765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453549775346507541289413 1022540582877470163991765)
                    ·
                      rfl

theorem cell22_2987086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2987086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987086 prefixEnd_2987086 := by exact prefixLift 2987086
  have htrace : WordTrace (prefixWord ++ tailWord_2987086) baseStart_2987086 baseEnd_2987086 := by
    simpa [prefixWord, tailWord_2987086, baseEnd_2987086] using wordTrace_append hprefix tailTrace_2987086
  have hstable : (prefixWord ++ tailWord_2987086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987086).length < 2 ^ (prefixWord ++ tailWord_2987086).sum := by decide
  have hdescent : baseEnd_2987086 < baseStart_2987086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987167 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 2, 3]
def baseStart_2987167 : Nat := 118140960795 + 2987167 * 2 ^ 59
def prefixEnd_2987167 : Nat := 4983230072969 + 3 ^ 40 * 2987167 * 2
def baseEnd_2987167 : Nat := 1022568310832812952716517

theorem tailTrace_2987167 : CollatzResearch.WordTrace tailWord_2987167 prefixEnd_2987167 1022568310832812952716517 := by
  unfold tailWord_2987167
  simp only [CollatzResearch.WordTrace]
  refine ⟨108950931169011601352199755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72633954112674400901466503 108950931169011601352199755)
  ·
    refine ⟨163426396753517402028299633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108950931169011601352199755 163426396753517402028299633)
    ·
      refine ⟨122569797565138051521224725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163426396753517402028299633 122569797565138051521224725)
      ·
        refine ⟨5745459260865846165057409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122569797565138051521224725 5745459260865846165057409)
        ·
          refine ⟨4309094445649384623793057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5745459260865846165057409 4309094445649384623793057)
          ·
            refine ⟨3231820834237038467844793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4309094445649384623793057 3231820834237038467844793)
            ·
              refine ⟨2423865625677778850883595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231820834237038467844793 2423865625677778850883595)
              ·
                refine ⟨3635798438516668276325393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423865625677778850883595 3635798438516668276325393)
                ·
                  refine ⟨2726848828887501207244045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635798438516668276325393 2726848828887501207244045)
                  ·
                    refine ⟨1022568310832812952716517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726848828887501207244045 1022568310832812952716517)
                    ·
                      rfl

theorem cell22_2987167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_2987167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987167 prefixEnd_2987167 := by exact prefixLift 2987167
  have htrace : WordTrace (prefixWord ++ tailWord_2987167) baseStart_2987167 baseEnd_2987167 := by
    simpa [prefixWord, tailWord_2987167, baseEnd_2987167] using wordTrace_append hprefix tailTrace_2987167
  have hstable : (prefixWord ++ tailWord_2987167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987167).length < 2 ^ (prefixWord ++ tailWord_2987167).sum := by decide
  have hdescent : baseEnd_2987167 < baseStart_2987167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987251 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 1, 5]
def baseStart_2987251 : Nat := 118140960795 + 2987251 * 2 ^ 59
def prefixEnd_2987251 : Nat := 4983230072969 + 3 ^ 40 * 2987251 * 2
def baseEnd_2987251 : Nat := 1022597065749464733616259

theorem tailTrace_2987251 : CollatzResearch.WordTrace tailWord_2987251 prefixEnd_2987251 1022597065749464733616259 := by
  unfold tailWord_2987251
  simp only [CollatzResearch.WordTrace]
  refine ⟨108953994900707283698257607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72635996600471522465505071 108953994900707283698257607)
  ·
    refine ⟨163430992351060925547386411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108953994900707283698257607 163430992351060925547386411)
    ·
      refine ⟨245146488526591388321079617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163430992351060925547386411 245146488526591388321079617)
      ·
        refine ⟨183859866394943541240809713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245146488526591388321079617 183859866394943541240809713)
        ·
          refine ⟨137894899796207655930607285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183859866394943541240809713 137894899796207655930607285)
          ·
            refine ⟨12927646855894467743494433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137894899796207655930607285 12927646855894467743494433)
            ·
              refine ⟨9695735141920850807620825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12927646855894467743494433 9695735141920850807620825)
              ·
                refine ⟨7271801356440638105715619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695735141920850807620825 7271801356440638105715619)
                ·
                  refine ⟨10907702034660957158573429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7271801356440638105715619 10907702034660957158573429)
                  ·
                    refine ⟨1022597065749464733616259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10907702034660957158573429 1022597065749464733616259)
                    ·
                      rfl

theorem cell22_2987251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_2987251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987251 prefixEnd_2987251 := by exact prefixLift 2987251
  have htrace : WordTrace (prefixWord ++ tailWord_2987251) baseStart_2987251 baseEnd_2987251 := by
    simpa [prefixWord, tailWord_2987251, baseEnd_2987251] using wordTrace_append hprefix tailTrace_2987251
  have hstable : (prefixWord ++ tailWord_2987251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987251).length < 2 ^ (prefixWord ++ tailWord_2987251).sum := by decide
  have hdescent : baseEnd_2987251 < baseStart_2987251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987298 : List Nat := [3, 3, 1, 1, 4, 1, 1, 8]
def baseStart_2987298 : Nat := 118140960795 + 2987298 * 2 ^ 59
def prefixEnd_2987298 : Nat := 4983230072969 + 3 ^ 40 * 2987298 * 2
def baseEnd_2987298 : Nat := 113623683867774697521235

theorem tailTrace_2987298 : CollatzResearch.WordTrace tailWord_2987298 prefixEnd_2987298 113623683867774697521235 := by
  unfold tailWord_2987298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27238927282884252681304637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72637139421024673816812365 27238927282884252681304637)
  ·
    refine ⟨10214597731081594755489239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27238927282884252681304637 10214597731081594755489239)
    ·
      refine ⟨15321896596622392133233859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10214597731081594755489239 15321896596622392133233859)
      ·
        refine ⟨22982844894933588199850789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15321896596622392133233859 22982844894933588199850789)
        ·
          refine ⟨4309283417800047787472023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22982844894933588199850789 4309283417800047787472023)
          ·
            refine ⟨6463925126700071681208035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309283417800047787472023 6463925126700071681208035)
            ·
              refine ⟨9695887690050107521812053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463925126700071681208035 9695887690050107521812053)
              ·
                refine ⟨113623683867774697521235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9695887690050107521812053 113623683867774697521235)
                ·
                  rfl

theorem cell22_2987298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_2987298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987298 prefixEnd_2987298 := by exact prefixLift 2987298
  have htrace : WordTrace (prefixWord ++ tailWord_2987298) baseStart_2987298 baseEnd_2987298 := by
    simpa [prefixWord, tailWord_2987298, baseEnd_2987298] using wordTrace_append hprefix tailTrace_2987298
  have hstable : (prefixWord ++ tailWord_2987298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987298).length < 2 ^ (prefixWord ++ tailWord_2987298).sum := by decide
  have hdescent : baseEnd_2987298 < baseStart_2987298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987381 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2987381 : Nat := 118140960795 + 2987381 * 2 ^ 59
def prefixEnd_2987381 : Nat := 4983230072969 + 3 ^ 40 * 2987381 * 2
def baseEnd_2987381 : Nat := 1022641567406187727865861

theorem tailTrace_2987381 : CollatzResearch.WordTrace tailWord_2987381 prefixEnd_2987381 1022641567406187727865861 := by
  unfold tailWord_2987381
  simp only [CollatzResearch.WordTrace]
  refine ⟨108958736390236315900489997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72639157593490877266993331 108958736390236315900489997)
  ·
    refine ⟨40859526146338618462683749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108958736390236315900489997 40859526146338618462683749)
    ·
      refine ⟨7661161152438490961753203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40859526146338618462683749 7661161152438490961753203)
      ·
        refine ⟨11491741728657736442629805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7661161152438490961753203 11491741728657736442629805)
        ·
          refine ⟨4309403148246651165986177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11491741728657736442629805 4309403148246651165986177)
          ·
            refine ⟨3232052361184988374489633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4309403148246651165986177 3232052361184988374489633)
            ·
              refine ⟨2424039270888741280867225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232052361184988374489633 2424039270888741280867225)
              ·
                refine ⟨1818029453166555960650419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424039270888741280867225 1818029453166555960650419)
                ·
                  refine ⟨2727044179749833940975629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818029453166555960650419 2727044179749833940975629)
                  ·
                    refine ⟨1022641567406187727865861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727044179749833940975629 1022641567406187727865861)
                    ·
                      rfl

theorem cell22_2987381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2987381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987381 prefixEnd_2987381 := by exact prefixLift 2987381
  have htrace : WordTrace (prefixWord ++ tailWord_2987381) baseStart_2987381 baseEnd_2987381 := by
    simpa [prefixWord, tailWord_2987381, baseEnd_2987381] using wordTrace_append hprefix tailTrace_2987381
  have hstable : (prefixWord ++ tailWord_2987381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987381).length < 2 ^ (prefixWord ++ tailWord_2987381).sum := by decide
  have hdescent : baseEnd_2987381 < baseStart_2987381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987403 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 1, 5]
def baseStart_2987403 : Nat := 118140960795 + 2987403 * 2 ^ 59
def prefixEnd_2987403 : Nat := 4983230072969 + 3 ^ 40 * 2987403 * 2
def baseEnd_2987403 : Nat := 1022649098455787003815793

theorem tailTrace_2987403 : CollatzResearch.WordTrace tailWord_2987403 prefixEnd_2987403 1022649098455787003815793 := by
  unfold tailWord_2987403
  simp only [CollatzResearch.WordTrace]
  refine ⟨108959538796156613657790863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72639692530771075771860575 108959538796156613657790863)
  ·
    refine ⟨163439308194234920486686295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108959538796156613657790863 163439308194234920486686295)
    ·
      refine ⟨245158962291352380730029443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163439308194234920486686295 245158962291352380730029443)
      ·
        refine ⟨367738443437028571095044165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245158962291352380730029443 367738443437028571095044165)
        ·
          refine ⟨68950958144442857080320781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367738443437028571095044165 68950958144442857080320781)
          ·
            refine ⟨25856609304166071405120293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68950958144442857080320781 25856609304166071405120293)
            ·
              refine ⟨4848114244531138388460055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25856609304166071405120293 4848114244531138388460055)
              ·
                refine ⟨7272171366796707582690083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848114244531138388460055 7272171366796707582690083)
                ·
                  refine ⟨10908257050195061374035125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272171366796707582690083 10908257050195061374035125)
                  ·
                    refine ⟨1022649098455787003815793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10908257050195061374035125 1022649098455787003815793)
                    ·
                      rfl

theorem cell22_2987403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].length) (baseStart_2987403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987403 prefixEnd_2987403 := by exact prefixLift 2987403
  have htrace : WordTrace (prefixWord ++ tailWord_2987403) baseStart_2987403 baseEnd_2987403 := by
    simpa [prefixWord, tailWord_2987403, baseEnd_2987403] using wordTrace_append hprefix tailTrace_2987403
  have hstable : (prefixWord ++ tailWord_2987403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987403).length < 2 ^ (prefixWord ++ tailWord_2987403).sum := by decide
  have hdescent : baseEnd_2987403 < baseStart_2987403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987418 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_2987418 : Nat := 118140960795 + 2987418 * 2 ^ 59
def prefixEnd_2987418 : Nat := 4983230072969 + 3 ^ 40 * 2987418 * 2
def baseEnd_2987418 : Nat := 1022654233262331964690747

theorem tailTrace_2987418 : CollatzResearch.WordTrace tailWord_2987418 prefixEnd_2987418 1022654233262331964690747 := by
  unfold tailWord_2987418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27240021472775567804896727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72640057260734847479724605 27240021472775567804896727)
  ·
    refine ⟨40860032209163351707345091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27240021472775567804896727 40860032209163351707345091)
    ·
      refine ⟨61290048313745027561017637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40860032209163351707345091 61290048313745027561017637)
      ·
        refine ⟨11491884058827192667690807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61290048313745027561017637 11491884058827192667690807)
        ·
          refine ⟨17237826088240789001536211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11491884058827192667690807 17237826088240789001536211)
          ·
            refine ⟨25856739132361183502304317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17237826088240789001536211 25856739132361183502304317)
            ·
              refine ⟨9696277174635443813364119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25856739132361183502304317 9696277174635443813364119)
              ·
                refine ⟨14544415761953165720046179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696277174635443813364119 14544415761953165720046179)
                ·
                  refine ⟨21816623642929748580069269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14544415761953165720046179 21816623642929748580069269)
                  ·
                    refine ⟨1022654233262331964690747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21816623642929748580069269 1022654233262331964690747)
                    ·
                      rfl

theorem cell22_2987418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_2987418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987418 prefixEnd_2987418 := by exact prefixLift 2987418
  have htrace : WordTrace (prefixWord ++ tailWord_2987418) baseStart_2987418 baseEnd_2987418 := by
    simpa [prefixWord, tailWord_2987418, baseEnd_2987418] using wordTrace_append hprefix tailTrace_2987418
  have hstable : (prefixWord ++ tailWord_2987418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987418).length < 2 ^ (prefixWord ++ tailWord_2987418).sum := by decide
  have hdescent : baseEnd_2987418 < baseStart_2987418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987437 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2987437 : Nat := 118140960795 + 2987437 * 2 ^ 59
def prefixEnd_2987437 : Nat := 4983230072969 + 3 ^ 40 * 2987437 * 2
def baseEnd_2987437 : Nat := 1022660737350622248465689

theorem tailTrace_2987437 : CollatzResearch.WordTrace tailWord_2987437 prefixEnd_2987437 1022660737350622248465689 := by
  unfold tailWord_2987437
  simp only [CollatzResearch.WordTrace]
  refine ⟨108960778878033437464528565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72640519252022291643019043 108960778878033437464528565)
  ·
    refine ⟨10215073019815634762299553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108960778878033437464528565 10215073019815634762299553)
    ·
      refine ⟨7661304764861726071724665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10215073019815634762299553 7661304764861726071724665)
      ·
        refine ⟨5745978573646294553793499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7661304764861726071724665 5745978573646294553793499)
        ·
          refine ⟨8618967860469441830690249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745978573646294553793499 8618967860469441830690249)
          ·
            refine ⟨6464225895352081373017687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8618967860469441830690249 6464225895352081373017687)
            ·
              refine ⟨9696338843028122059526531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464225895352081373017687 9696338843028122059526531)
              ·
                refine ⟨14544508264542183089289797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696338843028122059526531 14544508264542183089289797)
                ·
                  refine ⟨2727095299601659329241837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14544508264542183089289797 2727095299601659329241837)
                  ·
                    refine ⟨1022660737350622248465689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727095299601659329241837 1022660737350622248465689)
                    ·
                      rfl

theorem cell22_2987437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2987437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987437 prefixEnd_2987437 := by exact prefixLift 2987437
  have htrace : WordTrace (prefixWord ++ tailWord_2987437) baseStart_2987437 baseEnd_2987437 := by
    simpa [prefixWord, tailWord_2987437, baseEnd_2987437] using wordTrace_append hprefix tailTrace_2987437
  have hstable : (prefixWord ++ tailWord_2987437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987437).length < 2 ^ (prefixWord ++ tailWord_2987437).sum := by decide
  have hdescent : baseEnd_2987437 < baseStart_2987437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987458 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2987458 : Nat := 118140960795 + 2987458 * 2 ^ 59
def prefixEnd_2987458 : Nat := 4983230072969 + 3 ^ 40 * 2987458 * 2
def baseEnd_2987458 : Nat := 1022667926079785193690625

theorem tailTrace_2987458 : CollatzResearch.WordTrace tailWord_2987458 prefixEnd_2987458 1022667926079785193690625 := by
  unfold tailWord_2987458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27240386202739339512760757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72641029873971572034028685 27240386202739339512760757)
  ·
    refine ⟨2553786206506813079321321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27240386202739339512760757 2553786206506813079321321)
    ·
      refine ⟨1915339654880109809490991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2553786206506813079321321 1915339654880109809490991)
      ·
        refine ⟨2873009482320164714236487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915339654880109809490991 2873009482320164714236487)
        ·
          refine ⟨4309514223480247071354731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873009482320164714236487 4309514223480247071354731)
          ·
            refine ⟨6464271335220370607032097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309514223480247071354731 6464271335220370607032097)
            ·
              refine ⟨4848203501415277955274073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464271335220370607032097 4848203501415277955274073)
              ·
                refine ⟨3636152626061458466455555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848203501415277955274073 3636152626061458466455555)
                ·
                  refine ⟨5454228939092187699683333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636152626061458466455555 5454228939092187699683333)
                  ·
                    refine ⟨1022667926079785193690625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5454228939092187699683333 1022667926079785193690625)
                    ·
                      rfl

theorem cell22_2987458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2987458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987458 prefixEnd_2987458 := by exact prefixLift 2987458
  have htrace : WordTrace (prefixWord ++ tailWord_2987458) baseStart_2987458 baseEnd_2987458 := by
    simpa [prefixWord, tailWord_2987458, baseEnd_2987458] using wordTrace_append hprefix tailTrace_2987458
  have hstable : (prefixWord ++ tailWord_2987458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987458).length < 2 ^ (prefixWord ++ tailWord_2987458).sum := by decide
  have hdescent : baseEnd_2987458 < baseStart_2987458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987512 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 5]
def baseStart_2987512 : Nat := 118140960795 + 2987512 * 2 ^ 59
def prefixEnd_2987512 : Nat := 4983230072969 + 3 ^ 40 * 2987512 * 2
def baseEnd_2987512 : Nat := 340895470461115684280153

theorem tailTrace_2987512 : CollatzResearch.WordTrace tailWord_2987512 prefixEnd_2987512 340895470461115684280153 := by
  unfold tailWord_2987512
  simp only [CollatzResearch.WordTrace]
  refine ⟨54481757176380862636754395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72642342901841150182339193 54481757176380862636754395)
  ·
    refine ⟨81722635764571293955131593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54481757176380862636754395 81722635764571293955131593)
    ·
      refine ⟨61291976823428470466348695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81722635764571293955131593 61291976823428470466348695)
      ·
        refine ⟨91937965235142705699523043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61291976823428470466348695 91937965235142705699523043)
        ·
          refine ⟨137906947852714058549284565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91937965235142705699523043 137906947852714058549284565)
          ·
            refine ⟨3232194090297985747248857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 137906947852714058549284565 3232194090297985747248857)
            ·
              refine ⟨2424145567723489310436643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232194090297985747248857 2424145567723489310436643)
              ·
                refine ⟨3636218351585233965654965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424145567723489310436643 3636218351585233965654965)
                ·
                  refine ⟨340895470461115684280153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3636218351585233965654965 340895470461115684280153)
                  ·
                    rfl

theorem cell22_2987512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_2987512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987512 prefixEnd_2987512 := by exact prefixLift 2987512
  have htrace : WordTrace (prefixWord ++ tailWord_2987512) baseStart_2987512 baseEnd_2987512 := by
    simpa [prefixWord, tailWord_2987512, baseEnd_2987512] using wordTrace_append hprefix tailTrace_2987512
  have hstable : (prefixWord ++ tailWord_2987512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987512).length < 2 ^ (prefixWord ++ tailWord_2987512).sum := by decide
  have hdescent : baseEnd_2987512 < baseStart_2987512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987550 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2987550 : Nat := 118140960795 + 2987550 * 2 ^ 59
def prefixEnd_2987550 : Nat := 4983230072969 + 3 ^ 40 * 2987550 * 2
def baseEnd_2987550 : Nat := 1022699419559927620390343

theorem tailTrace_2987550 : CollatzResearch.WordTrace tailWord_2987550 prefixEnd_2987550 1022699419559927620390343 := by
  unfold tailWord_2987550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13620612540828007220424013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72643266884416038508928069 13620612540828007220424013)
  ·
    refine ⟨5107729702810502707659005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13620612540828007220424013 5107729702810502707659005)
    ·
      refine ⟨1915398638553938515372127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5107729702810502707659005 1915398638553938515372127)
      ·
        refine ⟨2873097957830907773058191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915398638553938515372127 2873097957830907773058191)
        ·
          refine ⟨4309646936746361659587287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873097957830907773058191 4309646936746361659587287)
          ·
            refine ⟨6464470405119542489380931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309646936746361659587287 6464470405119542489380931)
            ·
              refine ⟨9696705607679313734071397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464470405119542489380931 9696705607679313734071397)
              ·
                refine ⟨1818132301439871325138387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9696705607679313734071397 1818132301439871325138387)
                ·
                  refine ⟨2727198452159806987707581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818132301439871325138387 2727198452159806987707581)
                  ·
                    refine ⟨1022699419559927620390343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727198452159806987707581 1022699419559927620390343)
                    ·
                      rfl

theorem cell22_2987550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2987550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987550 prefixEnd_2987550 := by exact prefixLift 2987550
  have htrace : WordTrace (prefixWord ++ tailWord_2987550) baseStart_2987550 baseEnd_2987550 := by
    simpa [prefixWord, tailWord_2987550, baseEnd_2987550] using wordTrace_append hprefix tailTrace_2987550
  have hstable : (prefixWord ++ tailWord_2987550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987550).length < 2 ^ (prefixWord ++ tailWord_2987550).sum := by decide
  have hdescent : baseEnd_2987550 < baseStart_2987550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987600 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_2987600 : Nat := 118140960795 + 2987600 * 2 ^ 59
def prefixEnd_2987600 : Nat := 4983230072969 + 3 ^ 40 * 2987600 * 2
def baseEnd_2987600 : Nat := 1022716535581744156640189

theorem tailTrace_2987600 : CollatzResearch.WordTrace tailWord_2987600 prefixEnd_2987600 1022716535581744156640189 := by
  unfold tailWord_2987600
  simp only [CollatzResearch.WordTrace]
  refine ⟨54483361988221458151356127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72644482650961944201808169 54483361988221458151356127)
  ·
    refine ⟨81725042982332187227034191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54483361988221458151356127 81725042982332187227034191)
    ·
      refine ⟨122587564473498280840551287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81725042982332187227034191 122587564473498280840551287)
      ·
        refine ⟨183881346710247421260826931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122587564473498280840551287 183881346710247421260826931)
        ·
          refine ⟨275822020065371131891240397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183881346710247421260826931 275822020065371131891240397)
          ·
            refine ⟨103433257524514174459215149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275822020065371131891240397 103433257524514174459215149)
            ·
              refine ⟨38787471571692815422205681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103433257524514174459215149 38787471571692815422205681)
              ·
                refine ⟨29090603678769611566654261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38787471571692815422205681 29090603678769611566654261)
                ·
                  refine ⟨2727244094884651084373837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29090603678769611566654261 2727244094884651084373837)
                  ·
                    refine ⟨1022716535581744156640189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727244094884651084373837 1022716535581744156640189)
                    ·
                      rfl

theorem cell22_2987600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_2987600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987600 prefixEnd_2987600 := by exact prefixLift 2987600
  have htrace : WordTrace (prefixWord ++ tailWord_2987600) baseStart_2987600 baseEnd_2987600 := by
    simpa [prefixWord, tailWord_2987600, baseEnd_2987600] using wordTrace_append hprefix tailTrace_2987600
  have hstable : (prefixWord ++ tailWord_2987600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987600).length < 2 ^ (prefixWord ++ tailWord_2987600).sum := by decide
  have hdescent : baseEnd_2987600 < baseStart_2987600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987617 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_2987617 : Nat := 118140960795 + 2987617 * 2 ^ 59
def prefixEnd_2987617 : Nat := 4983230072969 + 3 ^ 40 * 2987617 * 2
def baseEnd_2987617 : Nat := 1022722355029161778965137

theorem tailTrace_2987617 : CollatzResearch.WordTrace tailWord_2987617 prefixEnd_2987617 1022722355029161778965137 := by
  unfold tailWord_2987617
  simp only [CollatzResearch.WordTrace]
  refine ⟨108967344017381328206081105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72644896011587552137387403 108967344017381328206081105)
  ·
    refine ⟨81725508013035996154560829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108967344017381328206081105 81725508013035996154560829)
    ·
      refine ⟨30647065504888498557960311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81725508013035996154560829 30647065504888498557960311)
      ·
        refine ⟨45970598257332747836940467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30647065504888498557960311 45970598257332747836940467)
        ·
          refine ⟨68955897385999121755410701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45970598257332747836940467 68955897385999121755410701)
          ·
            refine ⟨25858461519749670658279013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68955897385999121755410701 25858461519749670658279013)
            ·
              refine ⟨4848461534953063248427315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25858461519749670658279013 4848461534953063248427315)
              ·
                refine ⟨7272692302429594872640973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848461534953063248427315 7272692302429594872640973)
                ·
                  refine ⟨2727259613411098077240365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7272692302429594872640973 2727259613411098077240365)
                  ·
                    refine ⟨1022722355029161778965137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727259613411098077240365 1022722355029161778965137)
                    ·
                      rfl

theorem cell22_2987617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_2987617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987617 prefixEnd_2987617 := by exact prefixLift 2987617
  have htrace : WordTrace (prefixWord ++ tailWord_2987617) baseStart_2987617 baseEnd_2987617 := by
    simpa [prefixWord, tailWord_2987617, baseEnd_2987617] using wordTrace_append hprefix tailTrace_2987617
  have hstable : (prefixWord ++ tailWord_2987617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987617).length < 2 ^ (prefixWord ++ tailWord_2987617).sum := by decide
  have hdescent : baseEnd_2987617 < baseStart_2987617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987668 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2987668 : Nat := 118140960795 + 2987668 * 2 ^ 59
def prefixEnd_2987668 : Nat := 4983230072969 + 3 ^ 40 * 2987668 * 2
def baseEnd_2987668 : Nat := 1022739813371414645939981

theorem tailTrace_2987668 : CollatzResearch.WordTrace tailWord_2987668 prefixEnd_2987668 1022739813371414645939981 := by
  unfold tailWord_2987668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54484602070098281958093829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72646136093464375944125105 54484602070098281958093829)
  ·
    refine ⟨10215862888143427867142593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54484602070098281958093829 10215862888143427867142593)
    ·
      refine ⟨7661897166107570900356945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10215862888143427867142593 7661897166107570900356945)
      ·
        refine ⟨5746422874580678175267709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7661897166107570900356945 5746422874580678175267709)
        ·
          refine ⟨2154908577967754315725391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5746422874580678175267709 2154908577967754315725391)
          ·
            refine ⟨3232362866951631473588087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154908577967754315725391 3232362866951631473588087)
            ·
              refine ⟨4848544300427447210382131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232362866951631473588087 4848544300427447210382131)
              ·
                refine ⟨7272816450641170815573197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848544300427447210382131 7272816450641170815573197)
                ·
                  refine ⟨2727306168990439055839949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7272816450641170815573197 2727306168990439055839949)
                  ·
                    refine ⟨1022739813371414645939981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727306168990439055839949 1022739813371414645939981)
                    ·
                      rfl

theorem cell22_2987668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2987668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987668 prefixEnd_2987668 := by exact prefixLift 2987668
  have htrace : WordTrace (prefixWord ++ tailWord_2987668) baseStart_2987668 baseEnd_2987668 := by
    simpa [prefixWord, tailWord_2987668, baseEnd_2987668] using wordTrace_append hprefix tailTrace_2987668
  have hstable : (prefixWord ++ tailWord_2987668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987668).length < 2 ^ (prefixWord ++ tailWord_2987668).sum := by decide
  have hdescent : baseEnd_2987668 < baseStart_2987668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987705 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_2987705 : Nat := 118140960795 + 2987705 * 2 ^ 59
def prefixEnd_2987705 : Nat := 4983230072969 + 3 ^ 40 * 2987705 * 2
def baseEnd_2987705 : Nat := 1022752479227558882764867

theorem tailTrace_2987705 : CollatzResearch.WordTrace tailWord_2987705 prefixEnd_2987705 1022752479227558882764867 := by
  unfold tailWord_2987705
  simp only [CollatzResearch.WordTrace]
  refine ⟨108970553641062519235284569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72647035760708346156856379 108970553641062519235284569)
  ·
    refine ⟨81727915230796889426463427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108970553641062519235284569 81727915230796889426463427)
    ·
      refine ⟨122591872846195334139695141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81727915230796889426463427 122591872846195334139695141)
      ·
        refine ⟨22985976158661625151192839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122591872846195334139695141 22985976158661625151192839)
        ·
          refine ⟨34478964237992437726789259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22985976158661625151192839 34478964237992437726789259)
          ·
            refine ⟨51718446356988656590183889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34478964237992437726789259 51718446356988656590183889)
            ·
              refine ⟨38788834767741492442637917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51718446356988656590183889 38788834767741492442637917)
              ·
                refine ⟨14545813037903059665989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38788834767741492442637917 14545813037903059665989219)
                ·
                  refine ⟨21818719556854589498983829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14545813037903059665989219 21818719556854589498983829)
                  ·
                    refine ⟨1022752479227558882764867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21818719556854589498983829 1022752479227558882764867)
                    ·
                      rfl

theorem cell22_2987705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_2987705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987705 prefixEnd_2987705 := by exact prefixLift 2987705
  have htrace : WordTrace (prefixWord ++ tailWord_2987705) baseStart_2987705 baseEnd_2987705 := by
    simpa [prefixWord, tailWord_2987705, baseEnd_2987705] using wordTrace_append hprefix tailTrace_2987705
  have hstable : (prefixWord ++ tailWord_2987705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987705).length < 2 ^ (prefixWord ++ tailWord_2987705).sum := by decide
  have hdescent : baseEnd_2987705 < baseStart_2987705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987737 : List Nat := [1, 2, 1, 2, 3, 5, 1, 7]
def baseStart_2987737 : Nat := 118140960795 + 2987737 * 2 ^ 59
def prefixEnd_2987737 : Nat := 4983230072969 + 3 ^ 40 * 2987737 * 2
def baseEnd_2987737 : Nat := 113640381497946829551641

theorem tailTrace_2987737 : CollatzResearch.WordTrace tailWord_2987737 prefixEnd_2987737 113640381497946829551641 := by
  unfold tailWord_2987737
  simp only [CollatzResearch.WordTrace]
  refine ⟨108971720776946588700449465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72647813851297725800299643 108971720776946588700449465)
  ·
    refine ⟨81728790582709941525337099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108971720776946588700449465 81728790582709941525337099)
    ·
      refine ⟨122593185874064912288005649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81728790582709941525337099 122593185874064912288005649)
      ·
        refine ⟨91944889405548684216004237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122593185874064912288005649 91944889405548684216004237)
        ·
          refine ⟨34479333527080756581001589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91944889405548684216004237 34479333527080756581001589)
          ·
            refine ⟨3232437518163820929468899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34479333527080756581001589 3232437518163820929468899)
            ·
              refine ⟨4848656277245731394203349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232437518163820929468899 4848656277245731394203349)
              ·
                refine ⟨113640381497946829551641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4848656277245731394203349 113640381497946829551641)
                ·
                  rfl

theorem cell22_2987737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 7].length) (baseStart_2987737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987737 prefixEnd_2987737 := by exact prefixLift 2987737
  have htrace : WordTrace (prefixWord ++ tailWord_2987737) baseStart_2987737 baseEnd_2987737 := by
    simpa [prefixWord, tailWord_2987737, baseEnd_2987737] using wordTrace_append hprefix tailTrace_2987737
  have hstable : (prefixWord ++ tailWord_2987737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987737).length < 2 ^ (prefixWord ++ tailWord_2987737).sum := by decide
  have hdescent : baseEnd_2987737 < baseStart_2987737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987741 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2987741 : Nat := 118140960795 + 2987741 * 2 ^ 59
def prefixEnd_2987741 : Nat := 4983230072969 + 3 ^ 40 * 2987741 * 2
def baseEnd_2987741 : Nat := 1022764802763266788864757

theorem tailTrace_2987741 : CollatzResearch.WordTrace tailWord_2987741 prefixEnd_2987741 1022764802763266788864757 := by
  unfold tailWord_2987741
  simp only [CollatzResearch.WordTrace]
  refine ⟨108971866668932097383595077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72647911112621398255730051 108971866668932097383595077)
  ·
    refine ⟨20432225000424768259424077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108971866668932097383595077 20432225000424768259424077)
    ·
      refine ⟨7662084375159288097284029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20432225000424768259424077 7662084375159288097284029)
      ·
        refine ⟨2873281640684733036481511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7662084375159288097284029 2873281640684733036481511)
        ·
          refine ⟨4309922461027099554722267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873281640684733036481511 4309922461027099554722267)
          ·
            refine ⟨6464883691540649332083401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309922461027099554722267 6464883691540649332083401)
            ·
              refine ⟨4848662768655486999062551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464883691540649332083401 4848662768655486999062551)
              ·
                refine ⟨7272994152983230498593827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848662768655486999062551 7272994152983230498593827)
                ·
                  refine ⟨10909491229474845747890741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272994152983230498593827 10909491229474845747890741)
                  ·
                    refine ⟨1022764802763266788864757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10909491229474845747890741 1022764802763266788864757)
                    ·
                      rfl

theorem cell22_2987741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2987741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987741 prefixEnd_2987741 := by exact prefixLift 2987741
  have htrace : WordTrace (prefixWord ++ tailWord_2987741) baseStart_2987741 baseEnd_2987741 := by
    simpa [prefixWord, tailWord_2987741, baseEnd_2987741] using wordTrace_append hprefix tailTrace_2987741
  have hstable : (prefixWord ++ tailWord_2987741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987741).length < 2 ^ (prefixWord ++ tailWord_2987741).sum := by decide
  have hdescent : baseEnd_2987741 < baseStart_2987741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987786 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_2987786 : Nat := 118140960795 + 2987786 * 2 ^ 59
def prefixEnd_2987786 : Nat := 4983230072969 + 3 ^ 40 * 2987786 * 2
def baseEnd_2987786 : Nat := 1022780207182901671489619

theorem tailTrace_2987786 : CollatzResearch.WordTrace tailWord_2987786 prefixEnd_2987786 1022780207182901671489619 := by
  unfold tailWord_2987786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27243376988442267517245803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72649005302512713379322141 27243376988442267517245803)
  ·
    refine ⟨40865065482663401275868705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27243376988442267517245803 40865065482663401275868705)
    ·
      refine ⟨30648799111997550956901529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40865065482663401275868705 30648799111997550956901529)
      ·
        refine ⟨22986599333998163217676147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30648799111997550956901529 22986599333998163217676147)
        ·
          refine ⟨34479899000997244826514221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22986599333998163217676147 34479899000997244826514221)
          ·
            refine ⟨12929962125373966809942833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34479899000997244826514221 12929962125373966809942833)
            ·
              refine ⟨9697471594030475107457125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12929962125373966809942833 9697471594030475107457125)
              ·
                refine ⟨1818275923880714082648211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9697471594030475107457125 1818275923880714082648211)
                ·
                  refine ⟨2727413885821071123972317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818275923880714082648211 2727413885821071123972317)
                  ·
                    refine ⟨1022780207182901671489619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727413885821071123972317 1022780207182901671489619)
                    ·
                      rfl

theorem cell22_2987786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_2987786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987786 prefixEnd_2987786 := by exact prefixLift 2987786
  have htrace : WordTrace (prefixWord ++ tailWord_2987786) baseStart_2987786 baseEnd_2987786 := by
    simpa [prefixWord, tailWord_2987786, baseEnd_2987786] using wordTrace_append hprefix tailTrace_2987786
  have hstable : (prefixWord ++ tailWord_2987786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987786).length < 2 ^ (prefixWord ++ tailWord_2987786).sum := by decide
  have hdescent : baseEnd_2987786 < baseStart_2987786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987795 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_2987795 : Nat := 118140960795 + 2987795 * 2 ^ 59
def prefixEnd_2987795 : Nat := 4983230072969 + 3 ^ 40 * 2987795 * 2
def baseEnd_2987795 : Nat := 1022783288066828648014591

theorem tailTrace_2987795 : CollatzResearch.WordTrace tailWord_2987795 prefixEnd_2987795 1022783288066828648014591 := by
  unfold tailWord_2987795
  simp only [CollatzResearch.WordTrace]
  refine ⟨108973836210736464606060839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72649224140490976404040559 108973836210736464606060839)
  ·
    refine ⟨163460754316104696909091259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108973836210736464606060839 163460754316104696909091259)
    ·
      refine ⟨245191131474157045363636889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163460754316104696909091259 245191131474157045363636889)
      ·
        refine ⟨183893348605617784022727667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245191131474157045363636889 183893348605617784022727667)
        ·
          refine ⟨275840022908426676034091501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183893348605617784022727667 275840022908426676034091501)
          ·
            refine ⟨103440008590660003512784313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275840022908426676034091501 103440008590660003512784313)
            ·
              refine ⟨77580006442995002634588235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103440008590660003512784313 77580006442995002634588235)
              ·
                refine ⟨116370009664492503951882353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77580006442995002634588235 116370009664492503951882353)
                ·
                  refine ⟨87277507248369377963911765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116370009664492503951882353 87277507248369377963911765)
                  ·
                    refine ⟨1022783288066828648014591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87277507248369377963911765 1022783288066828648014591)
                    ·
                      rfl

theorem cell22_2987795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_2987795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987795 prefixEnd_2987795 := by exact prefixLift 2987795
  have htrace : WordTrace (prefixWord ++ tailWord_2987795) baseStart_2987795 baseEnd_2987795 := by
    simpa [prefixWord, tailWord_2987795, baseEnd_2987795] using wordTrace_append hprefix tailTrace_2987795
  have hstable : (prefixWord ++ tailWord_2987795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987795).length < 2 ^ (prefixWord ++ tailWord_2987795).sum := by decide
  have hdescent : baseEnd_2987795 < baseStart_2987795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987797 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2987797 : Nat := 118140960795 + 2987797 * 2 ^ 59
def prefixEnd_2987797 : Nat := 4983230072969 + 3 ^ 40 * 2987797 * 2
def baseEnd_2987797 : Nat := 1022783972707701309464585

theorem tailTrace_2987797 : CollatzResearch.WordTrace tailWord_2987797 prefixEnd_2987797 1022783972707701309464585 := by
  unfold tailWord_2987797
  simp only [CollatzResearch.WordTrace]
  refine ⟨108973909156729218947633645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72649272771152812631755763 108973909156729218947633645)
  ·
    refine ⟨40865215933773457105362617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108973909156729218947633645 40865215933773457105362617)
    ·
      refine ⟨30648911950330092829021963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40865215933773457105362617 30648911950330092829021963)
      ·
        refine ⟨45973367925495139243532945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30648911950330092829021963 45973367925495139243532945)
        ·
          refine ⟨34480025944121354432649709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45973367925495139243532945 34480025944121354432649709)
          ·
            refine ⟨12930009729045507912243641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34480025944121354432649709 12930009729045507912243641)
            ·
              refine ⟨9697507296784130934182731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12930009729045507912243641 9697507296784130934182731)
              ·
                refine ⟨14546260945176196401274097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9697507296784130934182731 14546260945176196401274097)
                ·
                  refine ⟨10909695708882147300955573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14546260945176196401274097 10909695708882147300955573)
                  ·
                    refine ⟨1022783972707701309464585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10909695708882147300955573 1022783972707701309464585)
                    ·
                      rfl

theorem cell22_2987797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2987797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987797 prefixEnd_2987797 := by exact prefixLift 2987797
  have htrace : WordTrace (prefixWord ++ tailWord_2987797) baseStart_2987797 baseEnd_2987797 := by
    simpa [prefixWord, tailWord_2987797, baseEnd_2987797] using wordTrace_append hprefix tailTrace_2987797
  have hstable : (prefixWord ++ tailWord_2987797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987797).length < 2 ^ (prefixWord ++ tailWord_2987797).sum := by decide
  have hdescent : baseEnd_2987797 < baseStart_2987797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987863 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 1, 4]
def baseStart_2987863 : Nat := 118140960795 + 2987863 * 2 ^ 59
def prefixEnd_2987863 : Nat := 4983230072969 + 3 ^ 40 * 2987863 * 2
def baseEnd_2987863 : Nat := 1022806565856499137314383

theorem tailTrace_2987863 : CollatzResearch.WordTrace tailWord_2987863 prefixEnd_2987863 1022806565856499137314383 := by
  unfold tailWord_2987863
  simp only [CollatzResearch.WordTrace]
  refine ⟨108976316374490112219536243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72650877582993408146357495 108976316374490112219536243)
  ·
    refine ⟨163464474561735168329304365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108976316374490112219536243 163464474561735168329304365)
    ·
      refine ⟨61299177960650688123489137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163464474561735168329304365 61299177960650688123489137)
      ·
        refine ⟨45974383470488016092616853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61299177960650688123489137 45974383470488016092616853)
        ·
          refine ⟨2155049225179125754341415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45974383470488016092616853 2155049225179125754341415)
          ·
            refine ⟨3232573837768688631512123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155049225179125754341415 3232573837768688631512123)
            ·
              refine ⟨4848860756653032947268185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232573837768688631512123 4848860756653032947268185)
              ·
                refine ⟨3636645567489774710451139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848860756653032947268185 3636645567489774710451139)
                ·
                  refine ⟨5454968351234662065676709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636645567489774710451139 5454968351234662065676709)
                  ·
                    refine ⟨1022806565856499137314383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5454968351234662065676709 1022806565856499137314383)
                    ·
                      rfl

theorem cell22_2987863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_2987863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987863 prefixEnd_2987863 := by exact prefixLift 2987863
  have htrace : WordTrace (prefixWord ++ tailWord_2987863) baseStart_2987863 baseEnd_2987863 := by
    simpa [prefixWord, tailWord_2987863, baseEnd_2987863] using wordTrace_append hprefix tailTrace_2987863
  have hstable : (prefixWord ++ tailWord_2987863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987863).length < 2 ^ (prefixWord ++ tailWord_2987863).sum := by decide
  have hdescent : baseEnd_2987863 < baseStart_2987863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987872 : List Nat := [2, 1, 1, 3, 3, 2, 2, 8]
def baseStart_2987872 : Nat := 118140960795 + 2987872 * 2 ^ 59
def prefixEnd_2987872 : Nat := 4983230072969 + 3 ^ 40 * 2987872 * 2
def baseEnd_2987872 : Nat := 113645516304491790426595

theorem tailTrace_2987872 : CollatzResearch.WordTrace tailWord_2987872 prefixEnd_2987872 113645516304491790426595 := by
  unfold tailWord_2987872
  simp only [CollatzResearch.WordTrace]
  refine ⟨54488322315728753378306935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72651096420971671171075913 54488322315728753378306935)
  ·
    refine ⟨81732483473593130067460403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54488322315728753378306935 81732483473593130067460403)
    ·
      refine ⟨122598725210389695101190605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81732483473593130067460403 122598725210389695101190605)
      ·
        refine ⟨45974521953896135662946477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122598725210389695101190605 45974521953896135662946477)
        ·
          refine ⟨17240445732711050873604929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45974521953896135662946477 17240445732711050873604929)
          ·
            refine ⟨12930334299533288155203697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17240445732711050873604929 12930334299533288155203697)
            ·
              refine ⟨9697750724649966116402773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12930334299533288155203697 9697750724649966116402773)
              ·
                refine ⟨113645516304491790426595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9697750724649966116402773 113645516304491790426595)
                ·
                  rfl

theorem cell22_2987872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_2987872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987872 prefixEnd_2987872 := by exact prefixLift 2987872
  have htrace : WordTrace (prefixWord ++ tailWord_2987872) baseStart_2987872 baseEnd_2987872 := by
    simpa [prefixWord, tailWord_2987872, baseEnd_2987872] using wordTrace_append hprefix tailTrace_2987872
  have hstable : (prefixWord ++ tailWord_2987872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987872).length < 2 ^ (prefixWord ++ tailWord_2987872).sum := by decide
  have hdescent : baseEnd_2987872 < baseStart_2987872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987904 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_2987904 : Nat := 118140960795 + 2987904 * 2 ^ 59
def prefixEnd_2987904 : Nat := 4983230072969 + 3 ^ 40 * 2987904 * 2
def baseEnd_2987904 : Nat := 1022820600994388697039257

theorem tailTrace_2987904 : CollatzResearch.WordTrace tailWord_2987904 prefixEnd_2987904 1022820600994388697039257 := by
  unfold tailWord_2987904
  simp only [CollatzResearch.WordTrace]
  refine ⟨54488905883670788110889383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72651874511561050814519177 54488905883670788110889383)
  ·
    refine ⟨81733358825506182166334075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54488905883670788110889383 81733358825506182166334075)
    ·
      refine ⟨122600038238259273249501113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81733358825506182166334075 122600038238259273249501113)
      ·
        refine ⟨91950028678694454937125835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122600038238259273249501113 91950028678694454937125835)
        ·
          refine ⟨137925043018041682405688753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91950028678694454937125835 137925043018041682405688753)
          ·
            refine ⟨103443782263531261804266565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137925043018041682405688753 103443782263531261804266565)
            ·
              refine ⟨19395709174412111588299981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103443782263531261804266565 19395709174412111588299981)
              ·
                refine ⟨7273390940404541845612493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19395709174412111588299981 7273390940404541845612493)
                ·
                  refine ⟨2727521602651703192104685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7273390940404541845612493 2727521602651703192104685)
                  ·
                    refine ⟨1022820600994388697039257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727521602651703192104685 1022820600994388697039257)
                    ·
                      rfl

theorem cell22_2987904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_2987904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2987904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2987904 prefixEnd_2987904 := by exact prefixLift 2987904
  have htrace : WordTrace (prefixWord ++ tailWord_2987904) baseStart_2987904 baseEnd_2987904 := by
    simpa [prefixWord, tailWord_2987904, baseEnd_2987904] using wordTrace_append hprefix tailTrace_2987904
  have hstable : (prefixWord ++ tailWord_2987904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987904).length < 2 ^ (prefixWord ++ tailWord_2987904).sum := by decide
  have hdescent : baseEnd_2987904 < baseStart_2987904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988150 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_2988150 : Nat := 118140960795 + 2988150 * 2 ^ 59
def prefixEnd_2988150 : Nat := 4983230072969 + 3 ^ 40 * 2988150 * 2
def baseEnd_2988150 : Nat := 1022904811821726055388503

theorem tailTrace_2988150 : CollatzResearch.WordTrace tailWord_2988150 prefixEnd_2988150 1022904811821726055388503 := by
  unfold tailWord_2988150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811674007778147514702119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72657856082966906823489269 6811674007778147514702119)
  ·
    refine ⟨10217511011667221272053179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6811674007778147514702119 10217511011667221272053179)
    ·
      refine ⟨15326266517500831908079769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10217511011667221272053179 15326266517500831908079769)
      ·
        refine ⟨11494699888125623931059827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15326266517500831908079769 11494699888125623931059827)
        ·
          refine ⟨17242049832188435896589741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11494699888125623931059827 17242049832188435896589741)
          ·
            refine ⟨6465768687070663461221153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17242049832188435896589741 6465768687070663461221153)
            ·
              refine ⟨4849326515302997595915865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6465768687070663461221153 4849326515302997595915865)
              ·
                refine ⟨3636994886477248196936899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849326515302997595915865 3636994886477248196936899)
                ·
                  refine ⟨5455492329715872295405349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636994886477248196936899 5455492329715872295405349)
                  ·
                    refine ⟨1022904811821726055388503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455492329715872295405349 1022904811821726055388503)
                    ·
                      rfl

theorem cell22_2988150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_2988150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988150 prefixEnd_2988150 := by exact prefixLift 2988150
  have htrace : WordTrace (prefixWord ++ tailWord_2988150) baseStart_2988150 baseEnd_2988150 := by
    simpa [prefixWord, tailWord_2988150, baseEnd_2988150] using wordTrace_append hprefix tailTrace_2988150
  have hstable : (prefixWord ++ tailWord_2988150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988150).length < 2 ^ (prefixWord ++ tailWord_2988150).sum := by decide
  have hdescent : baseEnd_2988150 < baseStart_2988150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988165 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 4]
def baseStart_2988165 : Nat := 118140960795 + 2988165 * 2 ^ 59
def prefixEnd_2988165 : Nat := 4983230072969 + 3 ^ 40 * 2988165 * 2
def baseEnd_2988165 : Nat := 340969982209423672087819

theorem tailTrace_2988165 : CollatzResearch.WordTrace tailWord_2988165 prefixEnd_2988165 340969982209423672087819 := by
  unfold tailWord_2988165
  simp only [CollatzResearch.WordTrace]
  refine ⟨108987331219396017797029949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72658220812930678531353299 108987331219396017797029949)
  ·
    refine ⟨40870249207273506673886231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108987331219396017797029949 40870249207273506673886231)
    ·
      refine ⟨61305373810910260010829347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40870249207273506673886231 61305373810910260010829347)
      ·
        refine ⟨91958060716365390016244021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61305373810910260010829347 91958060716365390016244021)
        ·
          refine ⟨8621068192159255314022877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91958060716365390016244021 8621068192159255314022877)
          ·
            refine ⟨3232900572059720742758579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8621068192159255314022877 3232900572059720742758579)
            ·
              refine ⟨4849350858089581114137869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232900572059720742758579 4849350858089581114137869)
              ·
                refine ⟨1818506571783592917801701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4849350858089581114137869 1818506571783592917801701)
                ·
                  refine ⟨340969982209423672087819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1818506571783592917801701 340969982209423672087819)
                  ·
                    rfl

theorem cell22_2988165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_2988165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988165 prefixEnd_2988165 := by exact prefixLift 2988165
  have htrace : WordTrace (prefixWord ++ tailWord_2988165) baseStart_2988165 baseEnd_2988165 := by
    simpa [prefixWord, tailWord_2988165, baseEnd_2988165] using wordTrace_append hprefix tailTrace_2988165
  have hstable : (prefixWord ++ tailWord_2988165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988165).length < 2 ^ (prefixWord ++ tailWord_2988165).sum := by decide
  have hdescent : baseEnd_2988165 < baseStart_2988165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988178 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2988178 : Nat := 118140960795 + 2988178 * 2 ^ 59
def prefixEnd_2988178 : Nat := 4983230072969 + 3 ^ 40 * 2988178 * 2
def baseEnd_2988178 : Nat := 1022914396793943315688417

theorem tailTrace_2988178 : CollatzResearch.WordTrace tailWord_2988178 prefixEnd_2988178 1022914396793943315688417 := by
  unfold tailWord_2988178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27246951342087230254313297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72658536912232614011502125 27246951342087230254313297)
  ·
    refine ⟨20435213506565422690734973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27246951342087230254313297 20435213506565422690734973)
    ·
      refine ⟨7663205064962033509025615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20435213506565422690734973 7663205064962033509025615)
      ·
        refine ⟨11494807597443050263538423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7663205064962033509025615 11494807597443050263538423)
        ·
          refine ⟨17242211396164575395307635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11494807597443050263538423 17242211396164575395307635)
          ·
            refine ⟨25863317094246863092961453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17242211396164575395307635 25863317094246863092961453)
            ·
              refine ⟨9698743910342573659860545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25863317094246863092961453 9698743910342573659860545)
              ·
                refine ⟨7274057932756930244895409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9698743910342573659860545 7274057932756930244895409)
                ·
                  refine ⟨5455543449567697683671557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7274057932756930244895409 5455543449567697683671557)
                  ·
                    refine ⟨1022914396793943315688417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455543449567697683671557 1022914396793943315688417)
                    ·
                      rfl

theorem cell22_2988178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2988178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988178 prefixEnd_2988178 := by exact prefixLift 2988178
  have htrace : WordTrace (prefixWord ++ tailWord_2988178) baseStart_2988178 baseEnd_2988178 := by
    simpa [prefixWord, tailWord_2988178, baseEnd_2988178] using wordTrace_append hprefix tailTrace_2988178
  have hstable : (prefixWord ++ tailWord_2988178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988178).length < 2 ^ (prefixWord ++ tailWord_2988178).sum := by decide
  have hdescent : baseEnd_2988178 < baseStart_2988178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988238 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_2988238 : Nat := 118140960795 + 2988238 * 2 ^ 59
def prefixEnd_2988238 : Nat := 4983230072969 + 3 ^ 40 * 2988238 * 2
def baseEnd_2988238 : Nat := 340978312006707719729411

theorem tailTrace_2988238 : CollatzResearch.WordTrace tailWord_2988238 prefixEnd_2988238 340978312006707719729411 := by
  unfold tailWord_2988238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623749218516443908054671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72659995832087700842958245 13623749218516443908054671)
  ·
    refine ⟨20435623827774665862082007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13623749218516443908054671 20435623827774665862082007)
    ·
      refine ⟨30653435741661998793123011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20435623827774665862082007 30653435741661998793123011)
      ·
        refine ⟨45980153612492998189684517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30653435741661998793123011 45980153612492998189684517)
        ·
          refine ⟨8621278802342437160565847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45980153612492998189684517 8621278802342437160565847)
          ·
            refine ⟨12931918203513655740848771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621278802342437160565847 12931918203513655740848771)
            ·
              refine ⟨19397877305270483611273157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931918203513655740848771 19397877305270483611273157)
              ·
                refine ⟨3637101994738215677113717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19397877305270483611273157 3637101994738215677113717)
                ·
                  refine ⟨340978312006707719729411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3637101994738215677113717 340978312006707719729411)
                  ·
                    rfl

theorem cell22_2988238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_2988238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988238 prefixEnd_2988238 := by exact prefixLift 2988238
  have htrace : WordTrace (prefixWord ++ tailWord_2988238) baseStart_2988238 baseEnd_2988238 := by
    simpa [prefixWord, tailWord_2988238, baseEnd_2988238] using wordTrace_append hprefix tailTrace_2988238
  have hstable : (prefixWord ++ tailWord_2988238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988238).length < 2 ^ (prefixWord ++ tailWord_2988238).sum := by decide
  have hdescent : baseEnd_2988238 < baseStart_2988238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988242 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2988242 : Nat := 118140960795 + 2988242 * 2 ^ 59
def prefixEnd_2988242 : Nat := 4983230072969 + 3 ^ 40 * 2988242 * 2
def baseEnd_2988242 : Nat := 1022936305301868482088221

theorem tailTrace_2988242 : CollatzResearch.WordTrace tailWord_2988242 prefixEnd_2988242 1022936305301868482088221 := by
  unfold tailWord_2988242
  simp only [CollatzResearch.WordTrace]
  refine ⟨27247534910029264986895745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72660093093411373298388653 27247534910029264986895745)
  ·
    refine ⟨20435651182521948740171809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27247534910029264986895745 20435651182521948740171809)
    ·
      refine ⟨15326738386891461555128857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20435651182521948740171809 15326738386891461555128857)
      ·
        refine ⟨11495053790168596166346643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15326738386891461555128857 11495053790168596166346643)
        ·
          refine ⟨17242580685252894249519965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11495053790168596166346643 17242580685252894249519965)
          ·
            refine ⟨6465967756969835343569987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17242580685252894249519965 6465967756969835343569987)
            ·
              refine ⟨9698951635454753015354981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465967756969835343569987 9698951635454753015354981)
              ·
                refine ⟨1818553431647766190379059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9698951635454753015354981 1818553431647766190379059)
                ·
                  refine ⟨2727830147471649285568589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818553431647766190379059 2727830147471649285568589)
                  ·
                    refine ⟨1022936305301868482088221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727830147471649285568589 1022936305301868482088221)
                    ·
                      rfl

theorem cell22_2988242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2988242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988242 prefixEnd_2988242 := by exact prefixLift 2988242
  have htrace : WordTrace (prefixWord ++ tailWord_2988242) baseStart_2988242 baseEnd_2988242 := by
    simpa [prefixWord, tailWord_2988242, baseEnd_2988242] using wordTrace_append hprefix tailTrace_2988242
  have hstable : (prefixWord ++ tailWord_2988242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988242).length < 2 ^ (prefixWord ++ tailWord_2988242).sum := by decide
  have hdescent : baseEnd_2988242 < baseStart_2988242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988251 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 3, 4]
def baseStart_2988251 : Nat := 118140960795 + 2988251 * 2 ^ 59
def prefixEnd_2988251 : Nat := 4983230072969 + 3 ^ 40 * 2988251 * 2
def baseEnd_2988251 : Nat := 1022939386185795458613193

theorem tailTrace_2988251 : CollatzResearch.WordTrace tailWord_2988251 prefixEnd_2988251 1022939386185795458613193 := by
  unfold tailWord_2988251
  simp only [CollatzResearch.WordTrace]
  refine ⟨108990467897084454484660607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72660311931389636323107071 108990467897084454484660607)
  ·
    refine ⟨163485701845626681726990911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108990467897084454484660607 163485701845626681726990911)
    ·
      refine ⟨245228552768440022590486367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163485701845626681726990911 245228552768440022590486367)
      ·
        refine ⟨367842829152660033885729551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245228552768440022590486367 367842829152660033885729551)
        ·
          refine ⟨551764243728990050828594327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367842829152660033885729551 551764243728990050828594327)
          ·
            refine ⟨827646365593485076242891491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551764243728990050828594327 827646365593485076242891491)
            ·
              refine ⟨1241469548390227614364337237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827646365593485076242891491 1241469548390227614364337237)
              ·
                refine ⟨14548471270197979855832077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1241469548390227614364337237 14548471270197979855832077)
                ·
                  refine ⟨5455676726324242445937029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14548471270197979855832077 5455676726324242445937029)
                  ·
                    refine ⟨1022939386185795458613193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455676726324242445937029 1022939386185795458613193)
                    ·
                      rfl

theorem cell22_2988251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_2988251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988251 prefixEnd_2988251 := by exact prefixLift 2988251
  have htrace : WordTrace (prefixWord ++ tailWord_2988251) baseStart_2988251 baseEnd_2988251 := by
    simpa [prefixWord, tailWord_2988251, baseEnd_2988251] using wordTrace_append hprefix tailTrace_2988251
  have hstable : (prefixWord ++ tailWord_2988251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988251).length < 2 ^ (prefixWord ++ tailWord_2988251).sum := by decide
  have hdescent : baseEnd_2988251 < baseStart_2988251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988253 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2988253 : Nat := 118140960795 + 2988253 * 2 ^ 59
def prefixEnd_2988253 : Nat := 4983230072969 + 3 ^ 40 * 2988253 * 2
def baseEnd_2988253 : Nat := 1022940070826668120063187

theorem tailTrace_2988253 : CollatzResearch.WordTrace tailWord_2988253 prefixEnd_2988253 1022940070826668120063187 := by
  unfold tailWord_2988253
  simp only [CollatzResearch.WordTrace]
  refine ⟨108990540843077208826233413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72660360562051472550822275 108990540843077208826233413)
  ·
    refine ⟨20435726408076976654918765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108990540843077208826233413 20435726408076976654918765)
    ·
      refine ⟨7663397403028866245594537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20435726408076976654918765 7663397403028866245594537)
      ·
        refine ⟨5747548052271649684195903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663397403028866245594537 5747548052271649684195903)
        ·
          refine ⟨8621322078407474526293855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747548052271649684195903 8621322078407474526293855)
          ·
            refine ⟨12931983117611211789440783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621322078407474526293855 12931983117611211789440783)
            ·
              refine ⟨19397974676416817684161175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931983117611211789440783 19397974676416817684161175)
              ·
                refine ⟨29096962014625226526241763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19397974676416817684161175 29096962014625226526241763)
                ·
                  refine ⟨43645443021937839789362645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29096962014625226526241763 43645443021937839789362645)
                  ·
                    refine ⟨1022940070826668120063187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43645443021937839789362645 1022940070826668120063187)
                    ·
                      rfl

theorem cell22_2988253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2988253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988253 prefixEnd_2988253 := by exact prefixLift 2988253
  have htrace : WordTrace (prefixWord ++ tailWord_2988253) baseStart_2988253 baseEnd_2988253 := by
    simpa [prefixWord, tailWord_2988253, baseEnd_2988253] using wordTrace_append hprefix tailTrace_2988253
  have hstable : (prefixWord ++ tailWord_2988253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988253).length < 2 ^ (prefixWord ++ tailWord_2988253).sum := by decide
  have hdescent : baseEnd_2988253 < baseStart_2988253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988268 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_2988268 : Nat := 118140960795 + 2988268 * 2 ^ 59
def prefixEnd_2988268 : Nat := 4983230072969 + 3 ^ 40 * 2988268 * 2
def baseEnd_2988268 : Nat := 1022945205633213080938141

theorem tailTrace_2988268 : CollatzResearch.WordTrace tailWord_2988268 prefixEnd_2988268 1022945205633213080938141 := by
  unfold tailWord_2988268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54495543969011433194014729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72660725292015244258686305 54495543969011433194014729)
  ·
    refine ⟨40871657976758574895511047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54495543969011433194014729 40871657976758574895511047)
    ·
      refine ⟨61307486965137862343266571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40871657976758574895511047 61307486965137862343266571)
      ·
        refine ⟨91961230447706793514899857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61307486965137862343266571 91961230447706793514899857)
        ·
          refine ⟨68970922835780095136174893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91961230447706793514899857 68970922835780095136174893)
          ·
            refine ⟨25864096063417535676065585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68970922835780095136174893 25864096063417535676065585)
            ·
              refine ⟨19398072047563151757049189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25864096063417535676065585 19398072047563151757049189)
              ·
                refine ⟨3637138508918090954446723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19398072047563151757049189 3637138508918090954446723)
                ·
                  refine ⟨5455707763377136431670085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637138508918090954446723 5455707763377136431670085)
                  ·
                    refine ⟨1022945205633213080938141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455707763377136431670085 1022945205633213080938141)
                    ·
                      rfl

theorem cell22_2988268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_2988268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988268 prefixEnd_2988268 := by exact prefixLift 2988268
  have htrace : WordTrace (prefixWord ++ tailWord_2988268) baseStart_2988268 baseEnd_2988268 := by
    simpa [prefixWord, tailWord_2988268, baseEnd_2988268] using wordTrace_append hprefix tailTrace_2988268
  have hstable : (prefixWord ++ tailWord_2988268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988268).length < 2 ^ (prefixWord ++ tailWord_2988268).sum := by decide
  have hdescent : baseEnd_2988268 < baseStart_2988268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988281 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_2988281 : Nat := 118140960795 + 2988281 * 2 ^ 59
def prefixEnd_2988281 : Nat := 4983230072969 + 3 ^ 40 * 2988281 * 2
def baseEnd_2988281 : Nat := 1022949655798885380363101

theorem tailTrace_2988281 : CollatzResearch.WordTrace tailWord_2988281 prefixEnd_2988281 1022949655798885380363101 := by
  unfold tailWord_2988281
  simp only [CollatzResearch.WordTrace]
  refine ⟨108991562086975769608252697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72661041391317179738835131 108991562086975769608252697)
  ·
    refine ⟨81743671565231827206189523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108991562086975769608252697 81743671565231827206189523)
    ·
      refine ⟨122615507347847740809284285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81743671565231827206189523 122615507347847740809284285)
      ·
        refine ⟨45980815255442902803481607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122615507347847740809284285 45980815255442902803481607)
        ·
          refine ⟨68971222883164354205222411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45980815255442902803481607 68971222883164354205222411)
          ·
            refine ⟨103456834324746531307833617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68971222883164354205222411 103456834324746531307833617)
            ·
              refine ⟨77592625743559898480875213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103456834324746531307833617 77592625743559898480875213)
              ·
                refine ⟨29097234653834961930328205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77592625743559898480875213 29097234653834961930328205)
                ·
                  refine ⟨10911462995188110723873077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29097234653834961930328205 10911462995188110723873077)
                  ·
                    refine ⟨1022949655798885380363101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10911462995188110723873077 1022949655798885380363101)
                    ·
                      rfl

theorem cell22_2988281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_2988281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988281 prefixEnd_2988281 := by exact prefixLift 2988281
  have htrace : WordTrace (prefixWord ++ tailWord_2988281) baseStart_2988281 baseEnd_2988281 := by
    simpa [prefixWord, tailWord_2988281, baseEnd_2988281] using wordTrace_append hprefix tailTrace_2988281
  have hstable : (prefixWord ++ tailWord_2988281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988281).length < 2 ^ (prefixWord ++ tailWord_2988281).sum := by decide
  have hdescent : baseEnd_2988281 < baseStart_2988281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988343 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 5, 3]
def baseStart_2988343 : Nat := 118140960795 + 2988343 * 2 ^ 59
def prefixEnd_2988343 : Nat := 4983230072969 + 3 ^ 40 * 2988343 * 2
def baseEnd_2988343 : Nat := 1022970879665937885312911

theorem tailTrace_2988343 : CollatzResearch.WordTrace tailWord_2988343 prefixEnd_2988343 1022970879665937885312911 := by
  unfold tailWord_2988343
  simp only [CollatzResearch.WordTrace]
  refine ⟨108993823412751154197009683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72662548941834102798006455 108993823412751154197009683)
  ·
    refine ⟨163490735119126731295514525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108993823412751154197009683 163490735119126731295514525)
    ·
      refine ⟨61309025669672524235817947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163490735119126731295514525 61309025669672524235817947)
      ·
        refine ⟨91963538504508786353726921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61309025669672524235817947 91963538504508786353726921)
        ·
          refine ⟨68972653878381589765295191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91963538504508786353726921 68972653878381589765295191)
          ·
            refine ⟨103458980817572384647942787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68972653878381589765295191 103458980817572384647942787)
            ·
              refine ⟨155188471226358576971914181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103458980817572384647942787 155188471226358576971914181)
              ·
                refine ⟨29097838354942233182233909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155188471226358576971914181 29097838354942233182233909)
                ·
                  refine ⟨2727922345775834360834429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29097838354942233182233909 2727922345775834360834429)
                  ·
                    refine ⟨1022970879665937885312911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727922345775834360834429 1022970879665937885312911)
                    ·
                      rfl

theorem cell22_2988343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_2988343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988343 prefixEnd_2988343 := by exact prefixLift 2988343
  have htrace : WordTrace (prefixWord ++ tailWord_2988343) baseStart_2988343 baseEnd_2988343 := by
    simpa [prefixWord, tailWord_2988343, baseEnd_2988343] using wordTrace_append hprefix tailTrace_2988343
  have hstable : (prefixWord ++ tailWord_2988343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988343).length < 2 ^ (prefixWord ++ tailWord_2988343).sum := by decide
  have hdescent : baseEnd_2988343 < baseStart_2988343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988360 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_2988360 : Nat := 118140960795 + 2988360 * 2 ^ 59
def prefixEnd_2988360 : Nat := 4983230072969 + 3 ^ 40 * 2988360 * 2
def baseEnd_2988360 : Nat := 1022976699113355507637859

theorem tailTrace_2988360 : CollatzResearch.WordTrace tailWord_2988360 prefixEnd_2988360 1022976699113355507637859 := by
  unfold tailWord_2988360
  simp only [CollatzResearch.WordTrace]
  refine ⟨54497221726844783050189267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72662962302459710733585689 54497221726844783050189267)
  ·
    refine ⟨81745832590267174575283901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54497221726844783050189267 81745832590267174575283901)
    ·
      refine ⟨30654687221350190465731463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81745832590267174575283901 30654687221350190465731463)
      ·
        refine ⟨45982030832025285698597195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30654687221350190465731463 45982030832025285698597195)
        ·
          refine ⟨68973046248037928547895793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45982030832025285698597195 68973046248037928547895793)
          ·
            refine ⟨51729784686028446410921845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68973046248037928547895793 51729784686028446410921845)
            ·
              refine ⟨4849667314315166851023923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51729784686028446410921845 4849667314315166851023923)
              ·
                refine ⟨7274500971472750276535885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849667314315166851023923 7274500971472750276535885)
                ·
                  refine ⟨2727937864302281353700957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7274500971472750276535885 2727937864302281353700957)
                  ·
                    refine ⟨1022976699113355507637859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727937864302281353700957 1022976699113355507637859)
                    ·
                      rfl

theorem cell22_2988360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_2988360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988360 prefixEnd_2988360 := by exact prefixLift 2988360
  have htrace : WordTrace (prefixWord ++ tailWord_2988360) baseStart_2988360 baseEnd_2988360 := by
    simpa [prefixWord, tailWord_2988360, baseEnd_2988360] using wordTrace_append hprefix tailTrace_2988360
  have hstable : (prefixWord ++ tailWord_2988360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988360).length < 2 ^ (prefixWord ++ tailWord_2988360).sum := by decide
  have hdescent : baseEnd_2988360 < baseStart_2988360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988450 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2988450 : Nat := 118140960795 + 2988450 * 2 ^ 59
def prefixEnd_2988450 : Nat := 4983230072969 + 3 ^ 40 * 2988450 * 2
def baseEnd_2988450 : Nat := 1023007507952625272887583

theorem tailTrace_2988450 : CollatzResearch.WordTrace tailWord_2988450 prefixEnd_2988450 1023007507952625272887583 := by
  unfold tailWord_2988450
  simp only [CollatzResearch.WordTrace]
  refine ⟨27249431505840877867788701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72665150682242340980769869 27249431505840877867788701)
  ·
    refine ⟨10218536814690329200420763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27249431505840877867788701 10218536814690329200420763)
    ·
      refine ⟨15327805222035493800631145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10218536814690329200420763 15327805222035493800631145)
      ·
        refine ⟨11495853916526620350473359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15327805222035493800631145 11495853916526620350473359)
        ·
          refine ⟨17243780874789930525710039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11495853916526620350473359 17243780874789930525710039)
          ·
            refine ⟨25865671312184895788565059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17243780874789930525710039 25865671312184895788565059)
            ·
              refine ⟨38798506968277343682847589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25865671312184895788565059 38798506968277343682847589)
              ·
                refine ⟨7274720056552001940533923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38798506968277343682847589 7274720056552001940533923)
                ·
                  refine ⟨10912080084828002910800885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7274720056552001940533923 10912080084828002910800885)
                  ·
                    refine ⟨1023007507952625272887583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10912080084828002910800885 1023007507952625272887583)
                    ·
                      rfl

theorem cell22_2988450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2988450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988450 prefixEnd_2988450 := by exact prefixLift 2988450
  have htrace : WordTrace (prefixWord ++ tailWord_2988450) baseStart_2988450 baseEnd_2988450 := by
    simpa [prefixWord, tailWord_2988450, baseEnd_2988450] using wordTrace_append hprefix tailTrace_2988450
  have hstable : (prefixWord ++ tailWord_2988450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988450).length < 2 ^ (prefixWord ++ tailWord_2988450).sum := by decide
  have hdescent : baseEnd_2988450 < baseStart_2988450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988458 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_2988458 : Nat := 118140960795 + 2988458 * 2 ^ 59
def prefixEnd_2988458 : Nat := 4983230072969 + 3 ^ 40 * 2988458 * 2
def baseEnd_2988458 : Nat := 341003415505371972895853

theorem tailTrace_2988458 : CollatzResearch.WordTrace tailWord_2988458 prefixEnd_2988458 341003415505371972895853 := by
  unfold tailWord_2988458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27249504451833632209361507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72665345204889685891630685 27249504451833632209361507)
  ·
    refine ⟨40874256677750448314042261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27249504451833632209361507 40874256677750448314042261)
    ·
      refine ⟨1915980781769552264720731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40874256677750448314042261 1915980781769552264720731)
      ·
        refine ⟨2873971172654328397081097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915980781769552264720731 2873971172654328397081097)
        ·
          refine ⟨2155478379490746297810823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873971172654328397081097 2155478379490746297810823)
          ·
            refine ⟨3233217569236119446716235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155478379490746297810823 3233217569236119446716235)
            ·
              refine ⟨4849826353854179170074353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233217569236119446716235 4849826353854179170074353)
              ·
                refine ⟨3637369765390634377555765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849826353854179170074353 3637369765390634377555765)
                ·
                  refine ⟨341003415505371972895853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3637369765390634377555765 341003415505371972895853)
                  ·
                    rfl

theorem cell22_2988458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_2988458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988458 prefixEnd_2988458 := by exact prefixLift 2988458
  have htrace : WordTrace (prefixWord ++ tailWord_2988458) baseStart_2988458 baseEnd_2988458 := by
    simpa [prefixWord, tailWord_2988458, baseEnd_2988458] using wordTrace_append hprefix tailTrace_2988458
  have hstable : (prefixWord ++ tailWord_2988458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988458).length < 2 ^ (prefixWord ++ tailWord_2988458).sum := by decide
  have hdescent : baseEnd_2988458 < baseStart_2988458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988484 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2988484 : Nat := 118140960795 + 2988484 * 2 ^ 59
def prefixEnd_2988484 : Nat := 4983230072969 + 3 ^ 40 * 2988484 * 2
def baseEnd_2988484 : Nat := 1023019146847460517537479

theorem tailTrace_2988484 : CollatzResearch.WordTrace tailWord_2988484 prefixEnd_2988484 1023019146847460517537479 := by
  unfold tailWord_2988484
  simp only [CollatzResearch.WordTrace]
  refine ⟨54499483052620167638946253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72665977403493556851928337 54499483052620167638946253)
  ·
    refine ⟨20437306144732562864604845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54499483052620167638946253 20437306144732562864604845)
    ·
      refine ⟨7663989804274711074226817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20437306144732562864604845 7663989804274711074226817)
      ·
        refine ⟨5747992353206033305670113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663989804274711074226817 5747992353206033305670113)
        ·
          refine ⟨4310994264904524979252585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5747992353206033305670113 4310994264904524979252585)
          ·
            refine ⟨3233245698678393734439439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310994264904524979252585 3233245698678393734439439)
            ·
              refine ⟨4849868548017590601659159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233245698678393734439439 4849868548017590601659159)
              ·
                refine ⟨7274802822026385902488739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849868548017590601659159 7274802822026385902488739)
                ·
                  refine ⟨10912204233039578853733109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7274802822026385902488739 10912204233039578853733109)
                  ·
                    refine ⟨1023019146847460517537479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10912204233039578853733109 1023019146847460517537479)
                    ·
                      rfl

theorem cell22_2988484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2988484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988484 prefixEnd_2988484 := by exact prefixLift 2988484
  have htrace : WordTrace (prefixWord ++ tailWord_2988484) baseStart_2988484 baseEnd_2988484 := by
    simpa [prefixWord, tailWord_2988484, baseEnd_2988484] using wordTrace_append hprefix tailTrace_2988484
  have hstable : (prefixWord ++ tailWord_2988484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988484).length < 2 ^ (prefixWord ++ tailWord_2988484).sum := by decide
  have hdescent : baseEnd_2988484 < baseStart_2988484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988514 : List Nat := [3, 3, 3, 2, 1, 2, 8]
def baseStart_2988514 : Nat := 118140960795 + 2988514 * 2 ^ 59
def prefixEnd_2988514 : Nat := 4983230072969 + 3 ^ 40 * 2988514 * 2
def baseEnd_2988514 : Nat := 37889978387427794047681

theorem tailTrace_2988514 : CollatzResearch.WordTrace tailWord_2988514 prefixEnd_2988514 37889978387427794047681 := by
  unfold tailWord_2988514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27250015073782912600371149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72666706863421100267656397 27250015073782912600371149)
  ·
    refine ⟨10218755652668592225139181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27250015073782912600371149 10218755652668592225139181)
    ·
      refine ⟨3832033369750722084427193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10218755652668592225139181 3832033369750722084427193)
      ·
        refine ⟨2874025027313041563320395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3832033369750722084427193 2874025027313041563320395)
        ·
          refine ⟨4311037540969562344980593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874025027313041563320395 4311037540969562344980593)
          ·
            refine ⟨3233278155727171758735445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311037540969562344980593 3233278155727171758735445)
            ·
              refine ⟨37889978387427794047681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3233278155727171758735445 37889978387427794047681)
              ·
                rfl

theorem cell22_2988514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 8].length) (baseStart_2988514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988514 prefixEnd_2988514 := by exact prefixLift 2988514
  have htrace : WordTrace (prefixWord ++ tailWord_2988514) baseStart_2988514 baseEnd_2988514 := by
    simpa [prefixWord, tailWord_2988514, baseEnd_2988514] using wordTrace_append hprefix tailTrace_2988514
  have hstable : (prefixWord ++ tailWord_2988514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988514).length < 2 ^ (prefixWord ++ tailWord_2988514).sum := by decide
  have hdescent : baseEnd_2988514 < baseStart_2988514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988580 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_2988580 : Nat := 118140960795 + 2988580 * 2 ^ 59
def prefixEnd_2988580 : Nat := 4983230072969 + 3 ^ 40 * 2988580 * 2
def baseEnd_2988580 : Nat := 1023052009609348267137185

theorem tailTrace_2988580 : CollatzResearch.WordTrace tailWord_2988580 prefixEnd_2988580 1023052009609348267137185 := by
  unfold tailWord_2988580
  simp only [CollatzResearch.WordTrace]
  refine ⟨54501233756446271836693597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72668311675261695782258129 54501233756446271836693597)
  ·
    refine ⟨20437962658667351938760099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54501233756446271836693597 20437962658667351938760099)
    ·
      refine ⟨30656943988001027908140149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20437962658667351938760099 30656943988001027908140149)
      ·
        refine ⟨2874088498875096366388139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30656943988001027908140149 2874088498875096366388139)
        ·
          refine ⟨4311132748312644549582209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874088498875096366388139 4311132748312644549582209)
          ·
            refine ⟨3233349561234483412186657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311132748312644549582209 3233349561234483412186657)
            ·
              refine ⟨2425012170925862559139993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233349561234483412186657 2425012170925862559139993)
              ·
                refine ⟨1818759128194396919354995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2425012170925862559139993 1818759128194396919354995)
                ·
                  refine ⟨2728138692291595379032493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818759128194396919354995 2728138692291595379032493)
                  ·
                    refine ⟨1023052009609348267137185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728138692291595379032493 1023052009609348267137185)
                    ·
                      rfl

theorem cell22_2988580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_2988580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988580 prefixEnd_2988580 := by exact prefixLift 2988580
  have htrace : WordTrace (prefixWord ++ tailWord_2988580) baseStart_2988580 baseEnd_2988580 := by
    simpa [prefixWord, tailWord_2988580, baseEnd_2988580] using wordTrace_append hprefix tailTrace_2988580
  have hstable : (prefixWord ++ tailWord_2988580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988580).length < 2 ^ (prefixWord ++ tailWord_2988580).sum := by decide
  have hdescent : baseEnd_2988580 < baseStart_2988580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988600 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_2988600 : Nat := 118140960795 + 2988600 * 2 ^ 59
def prefixEnd_2988600 : Nat := 4983230072969 + 3 ^ 40 * 2988600 * 2
def baseEnd_2988600 : Nat := 1023058856018074881637123

theorem tailTrace_2988600 : CollatzResearch.WordTrace tailWord_2988600 prefixEnd_2988600 1023058856018074881637123 := by
  unfold tailWord_2988600
  simp only [CollatzResearch.WordTrace]
  refine ⟨54501598486410043544557627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72668797981880058059410169 54501598486410043544557627)
  ·
    refine ⟨81752397729615065316836441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54501598486410043544557627 81752397729615065316836441)
    ·
      refine ⟨61314298297211298987627331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81752397729615065316836441 61314298297211298987627331)
      ·
        refine ⟨91971447445816948481440997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61314298297211298987627331 91971447445816948481440997)
        ·
          refine ⟨17244646396090677840270187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91971447445816948481440997 17244646396090677840270187)
          ·
            refine ⟨25866969594136016760405281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17244646396090677840270187 25866969594136016760405281)
            ·
              refine ⟨19400227195602012570303961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25866969594136016760405281 19400227195602012570303961)
              ·
                refine ⟨14550170396701509427727971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19400227195602012570303961 14550170396701509427727971)
                ·
                  refine ⟨21825255595052264141591957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14550170396701509427727971 21825255595052264141591957)
                  ·
                    refine ⟨1023058856018074881637123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21825255595052264141591957 1023058856018074881637123)
                    ·
                      rfl

theorem cell22_2988600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_2988600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988600 prefixEnd_2988600 := by exact prefixLift 2988600
  have htrace : WordTrace (prefixWord ++ tailWord_2988600) baseStart_2988600 baseEnd_2988600 := by
    simpa [prefixWord, tailWord_2988600, baseEnd_2988600] using wordTrace_append hprefix tailTrace_2988600
  have hstable : (prefixWord ++ tailWord_2988600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988600).length < 2 ^ (prefixWord ++ tailWord_2988600).sum := by decide
  have hdescent : baseEnd_2988600 < baseStart_2988600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988602 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_2988602 : Nat := 118140960795 + 2988602 * 2 ^ 59
def prefixEnd_2988602 : Nat := 4983230072969 + 3 ^ 40 * 2988602 * 2
def baseEnd_2988602 : Nat := 1023059540658947543087117

theorem tailTrace_2988602 : CollatzResearch.WordTrace tailWord_2988602 prefixEnd_2988602 1023059540658947543087117 := by
  unfold tailWord_2988602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27250817479703210357672015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72668846612541894287125373 27250817479703210357672015)
  ·
    refine ⟨40876226219554815536508023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27250817479703210357672015 40876226219554815536508023)
    ·
      refine ⟨61314339329332223304762035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40876226219554815536508023 61314339329332223304762035)
      ·
        refine ⟨91971508993998334957143053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61314339329332223304762035 91971508993998334957143053)
        ·
          refine ⟨34489315872749375608928645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91971508993998334957143053 34489315872749375608928645)
          ·
            refine ⟨6466746726140507926674121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34489315872749375608928645 6466746726140507926674121)
            ·
              refine ⟨4850060044605380945005591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6466746726140507926674121 4850060044605380945005591)
              ·
                refine ⟨7275090066908071417508387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4850060044605380945005591 7275090066908071417508387)
                ·
                  refine ⟨10912635100362107126262581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7275090066908071417508387 10912635100362107126262581)
                  ·
                    refine ⟨1023059540658947543087117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10912635100362107126262581 1023059540658947543087117)
                    ·
                      rfl

theorem cell22_2988602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_2988602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988602 prefixEnd_2988602 := by exact prefixLift 2988602
  have htrace : WordTrace (prefixWord ++ tailWord_2988602) baseStart_2988602 baseEnd_2988602 := by
    simpa [prefixWord, tailWord_2988602, baseEnd_2988602] using wordTrace_append hprefix tailTrace_2988602
  have hstable : (prefixWord ++ tailWord_2988602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988602).length < 2 ^ (prefixWord ++ tailWord_2988602).sum := by decide
  have hdescent : baseEnd_2988602 < baseStart_2988602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988621 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2988621 : Nat := 118140960795 + 2988621 * 2 ^ 59
def prefixEnd_2988621 : Nat := 4983230072969 + 3 ^ 40 * 2988621 * 2
def baseEnd_2988621 : Nat := 341022014915745942287353

theorem tailTrace_2988621 : CollatzResearch.WordTrace tailWord_2988621 prefixEnd_2988621 341022014915745942287353 := by
  unfold tailWord_2988621
  simp only [CollatzResearch.WordTrace]
  refine ⟨109003962905744007675629717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72669308603829338450419811 109003962905744007675629717)
  ·
    refine ⟨5109560761206750359795143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109003962905744007675629717 5109560761206750359795143)
    ·
      refine ⟨7664341141810125539692715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5109560761206750359795143 7664341141810125539692715)
      ·
        refine ⟨11496511712715188309539073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664341141810125539692715 11496511712715188309539073)
        ·
          refine ⟨8622383784536391232154305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11496511712715188309539073 8622383784536391232154305)
          ·
            refine ⟨6466787838402293424115729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8622383784536391232154305 6466787838402293424115729)
            ·
              refine ⟨4850090878801720068086797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6466787838402293424115729 4850090878801720068086797)
              ·
                refine ⟨1818784079550645025532549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4850090878801720068086797 1818784079550645025532549)
                ·
                  refine ⟨341022014915745942287353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1818784079550645025532549 341022014915745942287353)
                  ·
                    rfl

theorem cell22_2988621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2988621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988621 prefixEnd_2988621 := by exact prefixLift 2988621
  have htrace : WordTrace (prefixWord ++ tailWord_2988621) baseStart_2988621 baseEnd_2988621 := by
    simpa [prefixWord, tailWord_2988621, baseEnd_2988621] using wordTrace_append hprefix tailTrace_2988621
  have hstable : (prefixWord ++ tailWord_2988621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988621).length < 2 ^ (prefixWord ++ tailWord_2988621).sum := by decide
  have hdescent : baseEnd_2988621 < baseStart_2988621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988638 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2988638 : Nat := 118140960795 + 2988638 * 2 ^ 59
def prefixEnd_2988638 : Nat := 4983230072969 + 3 ^ 40 * 2988638 * 2
def baseEnd_2988638 : Nat := 341023954731551816395669

theorem tailTrace_2988638 : CollatzResearch.WordTrace tailWord_2988638 prefixEnd_2988638 341023954731551816395669 := by
  unfold tailWord_2988638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13625572868335302447374821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72669721964454946385999045 13625572868335302447374821)
  ·
    refine ⟨2554794912812869208882779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13625572868335302447374821 2554794912812869208882779)
    ·
      refine ⟨3832192369219303813324169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2554794912812869208882779 3832192369219303813324169)
      ·
        refine ⟨2874144276914477859993127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3832192369219303813324169 2874144276914477859993127)
        ·
          refine ⟨4311216415371716789989691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874144276914477859993127 4311216415371716789989691)
          ·
            refine ⟨6466824623057575184984537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311216415371716789989691 6466824623057575184984537)
            ·
              refine ⟨4850118467293181388738403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6466824623057575184984537 4850118467293181388738403)
              ·
                refine ⟨7275177700939772083107605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4850118467293181388738403 7275177700939772083107605)
                ·
                  refine ⟨341023954731551816395669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7275177700939772083107605 341023954731551816395669)
                  ·
                    rfl

theorem cell22_2988638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2988638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988638 prefixEnd_2988638 := by exact prefixLift 2988638
  have htrace : WordTrace (prefixWord ++ tailWord_2988638) baseStart_2988638 baseEnd_2988638 := by
    simpa [prefixWord, tailWord_2988638, baseEnd_2988638] using wordTrace_append hprefix tailTrace_2988638
  have hstable : (prefixWord ++ tailWord_2988638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988638).length < 2 ^ (prefixWord ++ tailWord_2988638).sum := by decide
  have hdescent : baseEnd_2988638 < baseStart_2988638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988675 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_2988675 : Nat := 118140960795 + 2988675 * 2 ^ 59
def prefixEnd_2988675 : Nat := 4983230072969 + 3 ^ 40 * 2988675 * 2
def baseEnd_2988675 : Nat := 1023084530050799686011893

theorem tailTrace_2988675 : CollatzResearch.WordTrace tailWord_2988675 prefixEnd_2988675 1023084530050799686011893 := by
  unfold tailWord_2988675
  simp only [CollatzResearch.WordTrace]
  refine ⟨109005932447548374898095479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72670621631698916598730319 109005932447548374898095479)
  ·
    refine ⟨163508898671322562347143219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109005932447548374898095479 163508898671322562347143219)
    ·
      refine ⟨245263348006983843520714829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163508898671322562347143219 245263348006983843520714829)
      ·
        refine ⟨91973755502618941320268061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245263348006983843520714829 91973755502618941320268061)
        ·
          refine ⟨34490158313482102995100523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91973755502618941320268061 34490158313482102995100523)
          ·
            refine ⟨51735237470223154492650785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34490158313482102995100523 51735237470223154492650785)
            ·
              refine ⟨38801428102667365869488089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51735237470223154492650785 38801428102667365869488089)
              ·
                refine ⟨29101071077000524402116067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38801428102667365869488089 29101071077000524402116067)
                ·
                  refine ⟨43651606615500786603174101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29101071077000524402116067 43651606615500786603174101)
                  ·
                    refine ⟨1023084530050799686011893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43651606615500786603174101 1023084530050799686011893)
                    ·
                      rfl

theorem cell22_2988675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_2988675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988675 prefixEnd_2988675 := by exact prefixLift 2988675
  have htrace : WordTrace (prefixWord ++ tailWord_2988675) baseStart_2988675 baseEnd_2988675 := by
    simpa [prefixWord, tailWord_2988675, baseEnd_2988675] using wordTrace_append hprefix tailTrace_2988675
  have hstable : (prefixWord ++ tailWord_2988675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988675).length < 2 ^ (prefixWord ++ tailWord_2988675).sum := by decide
  have hdescent : baseEnd_2988675 < baseStart_2988675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988698 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_2988698 : Nat := 118140960795 + 2988698 * 2 ^ 59
def prefixEnd_2988698 : Nat := 4983230072969 + 3 ^ 40 * 2988698 * 2
def baseEnd_2988698 : Nat := 1023092403420835292686823

theorem tailTrace_2988698 : CollatzResearch.WordTrace tailWord_2988698 prefixEnd_2988698 1023092403420835292686823 := by
  unfold tailWord_2988698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27251692831616262456545687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72671180884310033217455165 27251692831616262456545687)
  ·
    refine ⟨40877539247424393684818531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27251692831616262456545687 40877539247424393684818531)
    ·
      refine ⟨61316308871136590527227797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40877539247424393684818531 61316308871136590527227797)
      ·
        refine ⟨2874201978334527680963803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61316308871136590527227797 2874201978334527680963803)
        ·
          refine ⟨4311302967501791521445705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874201978334527680963803 4311302967501791521445705)
          ·
            refine ⟨3233477225626343641084279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311302967501791521445705 3233477225626343641084279)
            ·
              refine ⟨4850215838439515461626419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233477225626343641084279 4850215838439515461626419)
              ·
                refine ⟨7275323757659273192439629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4850215838439515461626419 7275323757659273192439629)
                ·
                  refine ⟨2728246409122227447164861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7275323757659273192439629 2728246409122227447164861)
                  ·
                    refine ⟨1023092403420835292686823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728246409122227447164861 1023092403420835292686823)
                    ·
                      rfl

theorem cell22_2988698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_2988698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988698 prefixEnd_2988698 := by exact prefixLift 2988698
  have htrace : WordTrace (prefixWord ++ tailWord_2988698) baseStart_2988698 baseEnd_2988698 := by
    simpa [prefixWord, tailWord_2988698, baseEnd_2988698] using wordTrace_append hprefix tailTrace_2988698
  have hstable : (prefixWord ++ tailWord_2988698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988698).length < 2 ^ (prefixWord ++ tailWord_2988698).sum := by decide
  have hdescent : baseEnd_2988698 < baseStart_2988698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988711 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 5]
def baseStart_2988711 : Nat := 118140960795 + 2988711 * 2 ^ 59
def prefixEnd_2988711 : Nat := 4983230072969 + 3 ^ 40 * 2988711 * 2
def baseEnd_2988711 : Nat := 341032284528835864037261

theorem tailTrace_2988711 : CollatzResearch.WordTrace tailWord_2988711 prefixEnd_2988711 341032284528835864037261 := by
  unfold tailWord_2988711
  simp only [CollatzResearch.WordTrace]
  refine ⟨109007245475417953046405987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72671496983611968697603991 109007245475417953046405987)
  ·
    refine ⟨163510868213126929569608981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109007245475417953046405987 163510868213126929569608981)
    ·
      refine ⟨7664571947490324823575421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163510868213126929569608981 7664571947490324823575421)
      ·
        refine ⟨2874214480308871808840783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7664571947490324823575421 2874214480308871808840783)
        ·
          refine ⟨4311321720463307713261175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874214480308871808840783 4311321720463307713261175)
          ·
            refine ⟨6466982580694961569891763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311321720463307713261175 6466982580694961569891763)
            ·
              refine ⟨9700473871042442354837645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466982580694961569891763 9700473871042442354837645)
              ·
                refine ⟨3637677701640915883064117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9700473871042442354837645 3637677701640915883064117)
                ·
                  refine ⟨341032284528835864037261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3637677701640915883064117 341032284528835864037261)
                  ·
                    rfl

theorem cell22_2988711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 5].length) (baseStart_2988711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988711 prefixEnd_2988711 := by exact prefixLift 2988711
  have htrace : WordTrace (prefixWord ++ tailWord_2988711) baseStart_2988711 baseEnd_2988711 := by
    simpa [prefixWord, tailWord_2988711, baseEnd_2988711] using wordTrace_append hprefix tailTrace_2988711
  have hstable : (prefixWord ++ tailWord_2988711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988711).length < 2 ^ (prefixWord ++ tailWord_2988711).sum := by decide
  have hdescent : baseEnd_2988711 < baseStart_2988711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988749 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2988749 : Nat := 118140960795 + 2988749 * 2 ^ 59
def prefixEnd_2988749 : Nat := 4983230072969 + 3 ^ 40 * 2988749 * 2
def baseEnd_2988749 : Nat := 1023109861763088159661667

theorem tailTrace_2988749 : CollatzResearch.WordTrace tailWord_2988749 prefixEnd_2988749 1023109861763088159661667 := by
  unfold tailWord_2988749
  simp only [CollatzResearch.WordTrace]
  refine ⟨109008631449280285536289301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72672420966186857024192867 109008631449280285536289301)
  ·
    refine ⟨5109779599185013384513561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109008631449280285536289301 5109779599185013384513561)
    ·
      refine ⟨3832334699388760038385171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5109779599185013384513561 3832334699388760038385171)
      ·
        refine ⟨5748502049083140057577757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832334699388760038385171 5748502049083140057577757)
        ·
          refine ⟨2155688268406177521591659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5748502049083140057577757 2155688268406177521591659)
          ·
            refine ⟨3233532402609266282387489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155688268406177521591659 3233532402609266282387489)
            ·
              refine ⟨2425149301956949711790617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233532402609266282387489 2425149301956949711790617)
              ·
                refine ⟨1818861976467712283842963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2425149301956949711790617 1818861976467712283842963)
                ·
                  refine ⟨2728292964701568425764445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818861976467712283842963 2728292964701568425764445)
                  ·
                    refine ⟨1023109861763088159661667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728292964701568425764445 1023109861763088159661667)
                    ·
                      rfl

theorem cell22_2988749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2988749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988749 prefixEnd_2988749 := by exact prefixLift 2988749
  have htrace : WordTrace (prefixWord ++ tailWord_2988749) baseStart_2988749 baseEnd_2988749 := by
    simpa [prefixWord, tailWord_2988749, baseEnd_2988749] using wordTrace_append hprefix tailTrace_2988749
  have hstable : (prefixWord ++ tailWord_2988749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988749).length < 2 ^ (prefixWord ++ tailWord_2988749).sum := by decide
  have hdescent : baseEnd_2988749 < baseStart_2988749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988767 : List Nat := [1, 1, 2, 3, 2, 3, 3, 7]
def baseStart_2988767 : Nat := 118140960795 + 2988767 * 2 ^ 59
def prefixEnd_2988767 : Nat := 4983230072969 + 3 ^ 40 * 2988767 * 2
def baseEnd_2988767 : Nat := 113679558170104679190179

theorem tailTrace_2988767 : CollatzResearch.WordTrace tailWord_2988767 prefixEnd_2988767 113679558170104679190179 := by
  unfold tailWord_2988767
  simp only [CollatzResearch.WordTrace]
  refine ⟨109009287963215074610444555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72672858642143383073629703 109009287963215074610444555)
  ·
    refine ⟨163513931944822611915666833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109009287963215074610444555 163513931944822611915666833)
    ·
      refine ⟨122635448958616958936750125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163513931944822611915666833 122635448958616958936750125)
      ·
        refine ⟨45988293359481359601281297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122635448958616958936750125 45988293359481359601281297)
        ·
          refine ⟨34491220019611019700960973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45988293359481359601281297 34491220019611019700960973)
          ·
            refine ⟨12934207507354132387860365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34491220019611019700960973 12934207507354132387860365)
            ·
              refine ⟨4850327815257799645447637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12934207507354132387860365 4850327815257799645447637)
              ·
                refine ⟨113679558170104679190179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4850327815257799645447637 113679558170104679190179)
                ·
                  rfl

theorem cell22_2988767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 7].length) (baseStart_2988767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988767 prefixEnd_2988767 := by exact prefixLift 2988767
  have htrace : WordTrace (prefixWord ++ tailWord_2988767) baseStart_2988767 baseEnd_2988767 := by
    simpa [prefixWord, tailWord_2988767, baseEnd_2988767] using wordTrace_append hprefix tailTrace_2988767
  have hstable : (prefixWord ++ tailWord_2988767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988767).length < 2 ^ (prefixWord ++ tailWord_2988767).sum := by decide
  have hdescent : baseEnd_2988767 < baseStart_2988767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988771 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 2, 3]
def baseStart_2988771 : Nat := 118140960795 + 2988771 * 2 ^ 59
def prefixEnd_2988771 : Nat := 4983230072969 + 3 ^ 40 * 2988771 * 2
def baseEnd_2988771 : Nat := 1023117392812687435611599

theorem tailTrace_2988771 : CollatzResearch.WordTrace tailWord_2988771 prefixEnd_2988771 1023117392812687435611599 := by
  unfold tailWord_2988771
  simp only [CollatzResearch.WordTrace]
  refine ⟨109009433855200583293590167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72672955903467055529060111 109009433855200583293590167)
  ·
    refine ⟨163514150782800874940385251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109009433855200583293590167 163514150782800874940385251)
    ·
      refine ⟨245271226174201312410577877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163514150782800874940385251 245271226174201312410577877)
      ·
        refine ⟨5748544363457843259622919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 245271226174201312410577877 5748544363457843259622919)
        ·
          refine ⟨8622816545186764889434379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748544363457843259622919 8622816545186764889434379)
          ·
            refine ⟨12934224817780147334151569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8622816545186764889434379 12934224817780147334151569)
            ·
              refine ⟨9700668613335110500613677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12934224817780147334151569 9700668613335110500613677)
              ·
                refine ⟨3637750730000666437730129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9700668613335110500613677 3637750730000666437730129)
                ·
                  refine ⟨2728313047500499828297597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3637750730000666437730129 2728313047500499828297597)
                  ·
                    refine ⟨1023117392812687435611599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728313047500499828297597 1023117392812687435611599)
                    ·
                      rfl

theorem cell22_2988771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 3].length) (baseStart_2988771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988771 prefixEnd_2988771 := by exact prefixLift 2988771
  have htrace : WordTrace (prefixWord ++ tailWord_2988771) baseStart_2988771 baseEnd_2988771 := by
    simpa [prefixWord, tailWord_2988771, baseEnd_2988771] using wordTrace_append hprefix tailTrace_2988771
  have hstable : (prefixWord ++ tailWord_2988771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988771).length < 2 ^ (prefixWord ++ tailWord_2988771).sum := by decide
  have hdescent : baseEnd_2988771 < baseStart_2988771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988786 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2988786 : Nat := 118140960795 + 2988786 * 2 ^ 59
def prefixEnd_2988786 : Nat := 4983230072969 + 3 ^ 40 * 2988786 * 2
def baseEnd_2988786 : Nat := 1023122527619232396486553

theorem tailTrace_2988786 : CollatzResearch.WordTrace tailWord_2988786 prefixEnd_2988786 1023122527619232396486553 := by
  unfold tailWord_2988786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27252495237536560213846553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72673320633430827236924141 27252495237536560213846553)
  ·
    refine ⟨20439371428152420160384915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27252495237536560213846553 20439371428152420160384915)
    ·
      refine ⟨30659057142228630240577373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20439371428152420160384915 30659057142228630240577373)
      ·
        refine ⟨11497146428335736340216515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30659057142228630240577373 11497146428335736340216515)
        ·
          refine ⟨17245719642503604510324773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11497146428335736340216515 17245719642503604510324773)
          ·
            refine ⟨3233572432969425845685895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17245719642503604510324773 3233572432969425845685895)
            ·
              refine ⟨4850358649454138768528843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233572432969425845685895 4850358649454138768528843)
              ·
                refine ⟨7275537974181208152793265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4850358649454138768528843 7275537974181208152793265)
                ·
                  refine ⟨5456653480635906114594949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7275537974181208152793265 5456653480635906114594949)
                  ·
                    refine ⟨1023122527619232396486553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5456653480635906114594949 1023122527619232396486553)
                    ·
                      rfl

theorem cell22_2988786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2988786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988786 prefixEnd_2988786 := by exact prefixLift 2988786
  have htrace : WordTrace (prefixWord ++ tailWord_2988786) baseStart_2988786 baseEnd_2988786 := by
    simpa [prefixWord, tailWord_2988786, baseEnd_2988786] using wordTrace_append hprefix tailTrace_2988786
  have hstable : (prefixWord ++ tailWord_2988786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988786).length < 2 ^ (prefixWord ++ tailWord_2988786).sum := by decide
  have hdescent : baseEnd_2988786 < baseStart_2988786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988910 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2988910 : Nat := 118140960795 + 2988910 * 2 ^ 59
def prefixEnd_2988910 : Nat := 4983230072969 + 3 ^ 40 * 2988910 * 2
def baseEnd_2988910 : Nat := 1023164975353337406386173

theorem tailTrace_2988910 : CollatzResearch.WordTrace tailWord_2988910 prefixEnd_2988910 1023164975353337406386173 := by
  unfold tailWord_2988910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13626812950212126254112523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72676335734464673355266789 13626812950212126254112523)
  ·
    refine ⟨20440219425318189381168785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13626812950212126254112523 20440219425318189381168785)
    ·
      refine ⟨15330164568988642035876589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20440219425318189381168785 15330164568988642035876589)
      ·
        refine ⟨5748811713370740763453721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15330164568988642035876589 5748811713370740763453721)
        ·
          refine ⟨4311608785028055572590291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5748811713370740763453721 4311608785028055572590291)
          ·
            refine ⟨6467413177542083358885437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311608785028055572590291 6467413177542083358885437)
            ·
              refine ⟨2425279941578281259582039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6467413177542083358885437 2425279941578281259582039)
              ·
                refine ⟨3637919912367421889373059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425279941578281259582039 3637919912367421889373059)
                ·
                  refine ⟨5456879868551132834059589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637919912367421889373059 5456879868551132834059589)
                  ·
                    refine ⟨1023164975353337406386173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5456879868551132834059589 1023164975353337406386173)
                    ·
                      rfl

theorem cell22_2988910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2988910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988910 prefixEnd_2988910 := by exact prefixLift 2988910
  have htrace : WordTrace (prefixWord ++ tailWord_2988910) baseStart_2988910 baseEnd_2988910 := by
    simpa [prefixWord, tailWord_2988910, baseEnd_2988910] using wordTrace_append hprefix tailTrace_2988910
  have hstable : (prefixWord ++ tailWord_2988910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988910).length < 2 ^ (prefixWord ++ tailWord_2988910).sum := by decide
  have hdescent : baseEnd_2988910 < baseStart_2988910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988936 : List Nat := [2, 1, 3, 3, 2, 3, 1, 7]
def baseStart_2988936 : Nat := 118140960795 + 2988936 * 2 ^ 59
def prefixEnd_2988936 : Nat := 4983230072969 + 3 ^ 40 * 2988936 * 2
def baseEnd_2988936 : Nat := 113685986187186889470677

theorem tailTrace_2988936 : CollatzResearch.WordTrace tailWord_2988936 prefixEnd_2988936 113685986187186889470677 := by
  unfold tailWord_2988936
  simp only [CollatzResearch.WordTrace]
  refine ⟨54507725949801408236673331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72676967933068544315564441 54507725949801408236673331)
  ·
    refine ⟨81761588924702112355009997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54507725949801408236673331 81761588924702112355009997)
    ·
      refine ⟨30660595846763292133128749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81761588924702112355009997 30660595846763292133128749)
      ·
        refine ⟨11497723442536234549923281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30660595846763292133128749 11497723442536234549923281)
        ·
          refine ⟨8623292581902175912442461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11497723442536234549923281 8623292581902175912442461)
          ·
            refine ⟨3233734718213315967165923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8623292581902175912442461 3233734718213315967165923)
            ·
              refine ⟨4850602077319973950748885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233734718213315967165923 4850602077319973950748885)
              ·
                refine ⟨113685986187186889470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4850602077319973950748885 113685986187186889470677)
                ·
                  rfl

theorem cell22_2988936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_2988936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988936 prefixEnd_2988936 := by exact prefixLift 2988936
  have htrace : WordTrace (prefixWord ++ tailWord_2988936) baseStart_2988936 baseEnd_2988936 := by
    simpa [prefixWord, tailWord_2988936, baseEnd_2988936] using wordTrace_append hprefix tailTrace_2988936
  have hstable : (prefixWord ++ tailWord_2988936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988936).length < 2 ^ (prefixWord ++ tailWord_2988936).sum := by decide
  have hdescent : baseEnd_2988936 < baseStart_2988936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988951 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 3, 3]
def baseStart_2988951 : Nat := 118140960795 + 2988951 * 2 ^ 59
def prefixEnd_2988951 : Nat := 4983230072969 + 3 ^ 40 * 2988951 * 2
def baseEnd_2988951 : Nat := 1023179010491226966111047

theorem tailTrace_2988951 : CollatzResearch.WordTrace tailWord_2988951 prefixEnd_2988951 1023179010491226966111047 := by
  unfold tailWord_2988951
  simp only [CollatzResearch.WordTrace]
  refine ⟨109015998994548474035142707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72677332663032316023428471 109015998994548474035142707)
  ·
    refine ⟨163523998491822711052714061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109015998994548474035142707 163523998491822711052714061)
    ·
      refine ⟨61321499434433516644767773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163523998491822711052714061 61321499434433516644767773)
      ·
        refine ⟨22995562287912568741787915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61321499434433516644767773 22995562287912568741787915)
        ·
          refine ⟨34493343431868853112681873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22995562287912568741787915 34493343431868853112681873)
          ·
            refine ⟨25870007573901639834511405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34493343431868853112681873 25870007573901639834511405)
            ·
              refine ⟨9701252840213114937941777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25870007573901639834511405 9701252840213114937941777)
              ·
                refine ⟨7275939630159836203456333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9701252840213114937941777 7275939630159836203456333)
                ·
                  refine ⟨2728477361309938576296125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7275939630159836203456333 2728477361309938576296125)
                  ·
                    refine ⟨1023179010491226966111047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728477361309938576296125 1023179010491226966111047)
                    ·
                      rfl

theorem cell22_2988951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_2988951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988951 prefixEnd_2988951 := by exact prefixLift 2988951
  have htrace : WordTrace (prefixWord ++ tailWord_2988951) baseStart_2988951 baseEnd_2988951 := by
    simpa [prefixWord, tailWord_2988951, baseEnd_2988951] using wordTrace_append hprefix tailTrace_2988951
  have hstable : (prefixWord ++ tailWord_2988951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988951).length < 2 ^ (prefixWord ++ tailWord_2988951).sum := by decide
  have hdescent : baseEnd_2988951 < baseStart_2988951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988964 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_2988964 : Nat := 118140960795 + 2988964 * 2 ^ 59
def prefixEnd_2988964 : Nat := 4983230072969 + 3 ^ 40 * 2988964 * 2
def baseEnd_2988964 : Nat := 341061153552299755178669

theorem tailTrace_2988964 : CollatzResearch.WordTrace tailWord_2988964 prefixEnd_2988964 341061153552299755178669 := by
  unfold tailWord_2988964
  simp only [CollatzResearch.WordTrace]
  refine ⟨54508236571750688627682973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72677648762334251503577297 54508236571750688627682973)
  ·
    refine ⟨20440588714406508235381115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54508236571750688627682973 20440588714406508235381115)
    ·
      refine ⟨30660883071609762353071673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20440588714406508235381115 30660883071609762353071673)
      ·
        refine ⟨22995662303707321764803755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30660883071609762353071673 22995662303707321764803755)
        ·
          refine ⟨34493493455560982647205633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22995662303707321764803755 34493493455560982647205633)
          ·
            refine ⟨25870120091670736985404225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34493493455560982647205633 25870120091670736985404225)
            ·
              refine ⟨19402590068753052739053169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25870120091670736985404225 19402590068753052739053169)
              ·
                refine ⟨14551942551564789554289877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19402590068753052739053169 14551942551564789554289877)
                ·
                  refine ⟨341061153552299755178669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14551942551564789554289877 341061153552299755178669)
                  ·
                    rfl

theorem cell22_2988964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_2988964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2988964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2988964 prefixEnd_2988964 := by exact prefixLift 2988964
  have htrace : WordTrace (prefixWord ++ tailWord_2988964) baseStart_2988964 baseEnd_2988964 := by
    simpa [prefixWord, tailWord_2988964, baseEnd_2988964] using wordTrace_append hprefix tailTrace_2988964
  have hstable : (prefixWord ++ tailWord_2988964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988964).length < 2 ^ (prefixWord ++ tailWord_2988964).sum := by decide
  have hdescent : baseEnd_2988964 < baseStart_2988964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989009 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 6]
def baseStart_2989009 : Nat := 118140960795 + 2989009 * 2 ^ 59
def prefixEnd_2989009 : Nat := 4983230072969 + 3 ^ 40 * 2989009 * 2
def baseEnd_2989009 : Nat := 341066288358844716053623

theorem tailTrace_2989009 : CollatzResearch.WordTrace tailWord_2989009 prefixEnd_2989009 341066288358844716053623 := by
  unfold tailWord_2989009
  simp only [CollatzResearch.WordTrace]
  refine ⟨109018114428338349940754081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72678742952225566627169387 109018114428338349940754081)
  ·
    refine ⟨81763585821253762455565561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109018114428338349940754081 81763585821253762455565561)
    ·
      refine ⟨61322689365940321841674171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81763585821253762455565561 61322689365940321841674171)
      ·
        refine ⟨91984034048910482762511257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61322689365940321841674171 91984034048910482762511257)
        ·
          refine ⟨68988025536682862071883443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91984034048910482762511257 68988025536682862071883443)
          ·
            refine ⟨103482038305024293107825165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68988025536682862071883443 103482038305024293107825165)
            ·
              refine ⟨38805764364384109915434437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103482038305024293107825165 38805764364384109915434437)
              ·
                refine ⟨7276080818322020609143957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38805764364384109915434437 7276080818322020609143957)
                ·
                  refine ⟨341066288358844716053623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7276080818322020609143957 341066288358844716053623)
                  ·
                    rfl

theorem cell22_2989009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_2989009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989009 prefixEnd_2989009 := by exact prefixLift 2989009
  have htrace : WordTrace (prefixWord ++ tailWord_2989009) baseStart_2989009 baseEnd_2989009 := by
    simpa [prefixWord, tailWord_2989009, baseEnd_2989009] using wordTrace_append hprefix tailTrace_2989009
  have hstable : (prefixWord ++ tailWord_2989009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989009).length < 2 ^ (prefixWord ++ tailWord_2989009).sum := by decide
  have hdescent : baseEnd_2989009 < baseStart_2989009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989088 : List Nat := [2, 1, 1, 7, 2, 9]
def baseStart_2989088 : Nat := 118140960795 + 2989088 * 2 ^ 59
def prefixEnd_2989088 : Nat := 4983230072969 + 3 ^ 40 * 2989088 * 2
def baseEnd_2989088 : Nat := 12632418622111163894267

theorem tailTrace_2989088 : CollatzResearch.WordTrace tailWord_2989088 prefixEnd_2989088 12632418622111163894267 := by
  unfold tailWord_2989088
  simp only [CollatzResearch.WordTrace]
  refine ⟨54510497897526073216439959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72680663863368097621919945 54510497897526073216439959)
  ·
    refine ⟨81765746846289109824659939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54510497897526073216439959 81765746846289109824659939)
    ·
      refine ⟨122648620269433664736989909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81765746846289109824659939 122648620269433664736989909)
      ·
        refine ⟨2874577037564851517273201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 122648620269433664736989909 2874577037564851517273201)
        ·
          refine ⟨2155932778173638637954901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2874577037564851517273201 2155932778173638637954901)
          ·
            refine ⟨12632418622111163894267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2155932778173638637954901 12632418622111163894267)
            ·
              rfl

theorem cell22_2989088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 9].length) (baseStart_2989088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989088 prefixEnd_2989088 := by exact prefixLift 2989088
  have htrace : WordTrace (prefixWord ++ tailWord_2989088) baseStart_2989088 baseEnd_2989088 := by
    simpa [prefixWord, tailWord_2989088, baseEnd_2989088] using wordTrace_append hprefix tailTrace_2989088
  have hstable : (prefixWord ++ tailWord_2989088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989088).length < 2 ^ (prefixWord ++ tailWord_2989088).sum := by decide
  have hdescent : baseEnd_2989088 < baseStart_2989088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989146 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_2989146 : Nat := 118140960795 + 2989146 * 2 ^ 59
def prefixEnd_2989146 : Nat := 4983230072969 + 3 ^ 40 * 2989146 * 2
def baseEnd_2989146 : Nat := 1023245762976311457485449

theorem tailTrace_2989146 : CollatzResearch.WordTrace tailWord_2989146 prefixEnd_2989146 1023245762976311457485449 := by
  unfold tailWord_2989146
  simp only [CollatzResearch.WordTrace]
  refine ⟨27255777807210505584622823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72682074152561348225660861 27255777807210505584622823)
  ·
    refine ⟨40883666710815758376934235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27255777807210505584622823 40883666710815758376934235)
    ·
      refine ⟨61325500066223637565401353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40883666710815758376934235 61325500066223637565401353)
      ·
        refine ⟨45994125049667728174051015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61325500066223637565401353 45994125049667728174051015)
        ·
          refine ⟨68991187574501592261076523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45994125049667728174051015 68991187574501592261076523)
          ·
            refine ⟨103486781361752388391614785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68991187574501592261076523 103486781361752388391614785)
            ·
              refine ⟨77615086021314291293711089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103486781361752388391614785 77615086021314291293711089)
              ·
                refine ⟨58211314515985718470283317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77615086021314291293711089 58211314515985718470283317)
                ·
                  refine ⟨5457310735873661106589061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58211314515985718470283317 5457310735873661106589061)
                  ·
                    refine ⟨1023245762976311457485449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457310735873661106589061 1023245762976311457485449)
                    ·
                      rfl

theorem cell22_2989146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_2989146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989146 prefixEnd_2989146 := by exact prefixLift 2989146
  have htrace : WordTrace (prefixWord ++ tailWord_2989146) baseStart_2989146 baseEnd_2989146 := by
    simpa [prefixWord, tailWord_2989146, baseEnd_2989146] using wordTrace_append hprefix tailTrace_2989146
  have hstable : (prefixWord ++ tailWord_2989146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989146).length < 2 ^ (prefixWord ++ tailWord_2989146).sum := by decide
  have hdescent : baseEnd_2989146 < baseStart_2989146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989161 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 6]
def baseStart_2989161 : Nat := 118140960795 + 2989161 * 2 ^ 59
def prefixEnd_2989161 : Nat := 4983230072969 + 3 ^ 40 * 2989161 * 2
def baseEnd_2989161 : Nat := 341083632594285472786801

theorem tailTrace_2989161 : CollatzResearch.WordTrace tailWord_2989161 prefixEnd_2989161 341083632594285472786801 := by
  unfold tailWord_2989161
  simp only [CollatzResearch.WordTrace]
  refine ⟨109023658323787679900287337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72682438882525119933524891 109023658323787679900287337)
  ·
    refine ⟨81767743742840759925215503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109023658323787679900287337 81767743742840759925215503)
    ·
      refine ⟨122651615614261139887823255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81767743742840759925215503 122651615614261139887823255)
      ·
        refine ⟨183977423421391709831734883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122651615614261139887823255 183977423421391709831734883)
        ·
          refine ⟨275966135132087564747602325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183977423421391709831734883 275966135132087564747602325)
          ·
            refine ⟨12935912584316604597543859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275966135132087564747602325 12935912584316604597543859)
            ·
              refine ⟨19403868876474906896315789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12935912584316604597543859 19403868876474906896315789)
              ·
                refine ⟨7276450828678090086118421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19403868876474906896315789 7276450828678090086118421)
                ·
                  refine ⟨341083632594285472786801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7276450828678090086118421 341083632594285472786801)
                  ·
                    rfl

theorem cell22_2989161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_2989161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989161 prefixEnd_2989161 := by exact prefixLift 2989161
  have htrace : WordTrace (prefixWord ++ tailWord_2989161) baseStart_2989161 baseEnd_2989161 := by
    simpa [prefixWord, tailWord_2989161, baseEnd_2989161] using wordTrace_append hprefix tailTrace_2989161
  have hstable : (prefixWord ++ tailWord_2989161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989161).length < 2 ^ (prefixWord ++ tailWord_2989161).sum := by decide
  have hdescent : baseEnd_2989161 < baseStart_2989161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989193 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_2989193 : Nat := 118140960795 + 2989193 * 2 ^ 59
def prefixEnd_2989193 : Nat := 4983230072969 + 3 ^ 40 * 2989193 * 2
def baseEnd_2989193 : Nat := 1023261852036819001560305

theorem tailTrace_2989193 : CollatzResearch.WordTrace tailWord_2989193 prefixEnd_2989193 1023261852036819001560305 := by
  unfold tailWord_2989193
  simp only [CollatzResearch.WordTrace]
  refine ⟨109024825459671749365452233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72683216973114499576968155 109024825459671749365452233)
  ·
    refine ⟨81768619094753812024089175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109024825459671749365452233 81768619094753812024089175)
    ·
      refine ⟨122652928642130718036133763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81768619094753812024089175 122652928642130718036133763)
      ·
        refine ⟨183979392963196077054200645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122652928642130718036133763 183979392963196077054200645)
        ·
          refine ⟨34496136180599264447662621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183979392963196077054200645 34496136180599264447662621)
          ·
            refine ⟨12936051067724724167873483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34496136180599264447662621 12936051067724724167873483)
            ·
              refine ⟨19404076601587086251810225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12936051067724724167873483 19404076601587086251810225)
              ·
                refine ⟨14553057451190314688857669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19404076601587086251810225 14553057451190314688857669)
                ·
                  refine ⟨2728698272098184004160813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14553057451190314688857669 2728698272098184004160813)
                  ·
                    refine ⟨1023261852036819001560305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728698272098184004160813 1023261852036819001560305)
                    ·
                      rfl

theorem cell22_2989193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_2989193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989193 prefixEnd_2989193 := by exact prefixLift 2989193
  have htrace : WordTrace (prefixWord ++ tailWord_2989193) baseStart_2989193 baseEnd_2989193 := by
    simpa [prefixWord, tailWord_2989193, baseEnd_2989193] using wordTrace_append hprefix tailTrace_2989193
  have hstable : (prefixWord ++ tailWord_2989193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989193).length < 2 ^ (prefixWord ++ tailWord_2989193).sum := by decide
  have hdescent : baseEnd_2989193 < baseStart_2989193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989208 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_2989208 : Nat := 118140960795 + 2989208 * 2 ^ 59
def prefixEnd_2989208 : Nat := 4983230072969 + 3 ^ 40 * 2989208 * 2
def baseEnd_2989208 : Nat := 1023266986843363962435259

theorem tailTrace_2989208 : CollatzResearch.WordTrace tailWord_2989208 prefixEnd_2989208 1023266986843363962435259 := by
  unfold tailWord_2989208
  simp only [CollatzResearch.WordTrace]
  refine ⟨54512686277308703463624139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72683581703078271284832185 54512686277308703463624139)
  ·
    refine ⟨81769029415963055195436209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54512686277308703463624139 81769029415963055195436209)
    ·
      refine ⟨61326772061972291396577157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81769029415963055195436209 61326772061972291396577157)
      ·
        refine ⟨11498769761619804636858217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61326772061972291396577157 11498769761619804636858217)
        ·
          refine ⟨8624077321214853477643663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11498769761619804636858217 8624077321214853477643663)
          ·
            refine ⟨12936115981822280216465495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624077321214853477643663 12936115981822280216465495)
            ·
              refine ⟨19404173972733420324698243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12936115981822280216465495 19404173972733420324698243)
              ·
                refine ⟨29106260959100130487047365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19404173972733420324698243 29106260959100130487047365)
                ·
                  refine ⟨5457423929831274466321381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29106260959100130487047365 5457423929831274466321381)
                  ·
                    refine ⟨1023266986843363962435259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457423929831274466321381 1023266986843363962435259)
                    ·
                      rfl

theorem cell22_2989208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_2989208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989208 prefixEnd_2989208 := by exact prefixLift 2989208
  have htrace : WordTrace (prefixWord ++ tailWord_2989208) baseStart_2989208 baseEnd_2989208 := by
    simpa [prefixWord, tailWord_2989208, baseEnd_2989208] using wordTrace_append hprefix tailTrace_2989208
  have hstable : (prefixWord ++ tailWord_2989208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989208).length < 2 ^ (prefixWord ++ tailWord_2989208).sum := by decide
  have hdescent : baseEnd_2989208 < baseStart_2989208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989210 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_2989210 : Nat := 118140960795 + 2989210 * 2 ^ 59
def prefixEnd_2989210 : Nat := 4983230072969 + 3 ^ 40 * 2989210 * 2
def baseEnd_2989210 : Nat := 1023267671484236623885253

theorem tailTrace_2989210 : CollatzResearch.WordTrace tailWord_2989210 prefixEnd_2989210 1023267671484236623885253 := by
  unfold tailWord_2989210
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256361375152540317205271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72683630333740107512547389 27256361375152540317205271)
  ·
    refine ⟨40884542062728810475807907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27256361375152540317205271 40884542062728810475807907)
    ·
      refine ⟨61326813094093215713711861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40884542062728810475807907 61326813094093215713711861)
      ·
        refine ⟨5749388727571238973160487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61326813094093215713711861 5749388727571238973160487)
        ·
          refine ⟨8624083091356858459740731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749388727571238973160487 8624083091356858459740731)
          ·
            refine ⟨12936124637035287689611097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624083091356858459740731 12936124637035287689611097)
            ·
              refine ⟨9702093477776465767208323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12936124637035287689611097 9702093477776465767208323)
              ·
                refine ⟨14553140216664698650812485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9702093477776465767208323 14553140216664698650812485)
                ·
                  refine ⟨2728713790624630997027341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14553140216664698650812485 2728713790624630997027341)
                  ·
                    refine ⟨1023267671484236623885253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728713790624630997027341 1023267671484236623885253)
                    ·
                      rfl

theorem cell22_2989210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_2989210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989210 prefixEnd_2989210 := by exact prefixLift 2989210
  have htrace : WordTrace (prefixWord ++ tailWord_2989210) baseStart_2989210 baseEnd_2989210 := by
    simpa [prefixWord, tailWord_2989210, baseEnd_2989210] using wordTrace_append hprefix tailTrace_2989210
  have hstable : (prefixWord ++ tailWord_2989210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989210).length < 2 ^ (prefixWord ++ tailWord_2989210).sum := by decide
  have hdescent : baseEnd_2989210 < baseStart_2989210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989212 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 4]
def baseStart_2989212 : Nat := 118140960795 + 2989212 * 2 ^ 59
def prefixEnd_2989212 : Nat := 4983230072969 + 3 ^ 40 * 2989212 * 2
def baseEnd_2989212 : Nat := 341089452041703095111749

theorem tailTrace_2989212 : CollatzResearch.WordTrace tailWord_2989212 prefixEnd_2989212 341089452041703095111749 := by
  unfold tailWord_2989212
  simp only [CollatzResearch.WordTrace]
  refine ⟨54512759223301457805196945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72683678964401943740262593 54512759223301457805196945)
  ·
    refine ⟨40884569417476093353897709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54512759223301457805196945 40884569417476093353897709)
    ·
      refine ⟨15331713531553535007711641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40884569417476093353897709 15331713531553535007711641)
      ·
        refine ⟨11498785148665151255783731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15331713531553535007711641 11498785148665151255783731)
        ·
          refine ⟨17248177722997726883675597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11498785148665151255783731 17248177722997726883675597)
          ·
            refine ⟨6468066646124147581378349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17248177722997726883675597 6468066646124147581378349)
            ·
              refine ⟨2425524992296555343016881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6468066646124147581378349 2425524992296555343016881)
              ·
                refine ⟨1819143744222416507262661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2425524992296555343016881 1819143744222416507262661)
                ·
                  refine ⟨341089452041703095111749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819143744222416507262661 341089452041703095111749)
                  ·
                    rfl

theorem cell22_2989212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_2989212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989212 prefixEnd_2989212 := by exact prefixLift 2989212
  have htrace : WordTrace (prefixWord ++ tailWord_2989212) baseStart_2989212 baseEnd_2989212 := by
    simpa [prefixWord, tailWord_2989212, baseEnd_2989212] using wordTrace_append hprefix tailTrace_2989212
  have hstable : (prefixWord ++ tailWord_2989212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989212).length < 2 ^ (prefixWord ++ tailWord_2989212).sum := by decide
  have hdescent : baseEnd_2989212 < baseStart_2989212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989223 : List Nat := [1, 1, 6, 2, 1, 1, 1, 9]
def baseStart_2989223 : Nat := 118140960795 + 2989223 * 2 ^ 59
def prefixEnd_2989223 : Nat := 4983230072969 + 3 ^ 40 * 2989223 * 2
def baseEnd_2989223 : Nat := 113696902405545435923357

theorem tailTrace_2989223 : CollatzResearch.WordTrace tailWord_2989223 prefixEnd_2989223 113696902405545435923357 := by
  unfold tailWord_2989223
  simp only [CollatzResearch.WordTrace]
  refine ⟨109025919649563064489044323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72683946433042042992696215 109025919649563064489044323)
  ·
    refine ⟨163538879474344596733566485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109025919649563064489044323 163538879474344596733566485)
    ·
      refine ⟨7665884975359902971885929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163538879474344596733566485 7665884975359902971885929)
      ·
        refine ⟨5749413731519927228914447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7665884975359902971885929 5749413731519927228914447)
        ·
          refine ⟨8624120597279890843371671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749413731519927228914447 8624120597279890843371671)
          ·
            refine ⟨12936180895919836265057507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624120597279890843371671 12936180895919836265057507)
            ·
              refine ⟨19404271343879754397586261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12936180895919836265057507 19404271343879754397586261)
              ·
                refine ⟨113696902405545435923357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19404271343879754397586261 113696902405545435923357)
                ·
                  rfl

theorem cell22_2989223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 9].length) (baseStart_2989223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989223 prefixEnd_2989223 := by exact prefixLift 2989223
  have htrace : WordTrace (prefixWord ++ tailWord_2989223) baseStart_2989223 baseEnd_2989223 := by
    simpa [prefixWord, tailWord_2989223, baseEnd_2989223] using wordTrace_append hprefix tailTrace_2989223
  have hstable : (prefixWord ++ tailWord_2989223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989223).length < 2 ^ (prefixWord ++ tailWord_2989223).sum := by decide
  have hdescent : baseEnd_2989223 < baseStart_2989223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989251 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 7]
def baseStart_2989251 : Nat := 118140960795 + 2989251 * 2 ^ 59
def prefixEnd_2989251 : Nat := 4983230072969 + 3 ^ 40 * 2989251 * 2
def baseEnd_2989251 : Nat := 341093902207375394536709

theorem tailTrace_2989251 : CollatzResearch.WordTrace tailWord_2989251 prefixEnd_2989251 341093902207375394536709 := by
  unfold tailWord_2989251
  simp only [CollatzResearch.WordTrace]
  refine ⟨109026940893461625271063607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72684627262307750180709071 109026940893461625271063607)
  ·
    refine ⟨163540411340192437906595411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109026940893461625271063607 163540411340192437906595411)
    ·
      refine ⟨245310617010288656859893117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163540411340192437906595411 245310617010288656859893117)
      ·
        refine ⟨91991481378858246322459919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245310617010288656859893117 91991481378858246322459919)
        ·
          refine ⟨137987222068287369483689879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91991481378858246322459919 137987222068287369483689879)
          ·
            refine ⟨206980833102431054225534819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137987222068287369483689879 206980833102431054225534819)
            ·
              refine ⟨310471249653646581338302229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206980833102431054225534819 310471249653646581338302229)
              ·
                refine ⟨14553339827514683500232917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 310471249653646581338302229 14553339827514683500232917)
                ·
                  refine ⟨341093902207375394536709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14553339827514683500232917 341093902207375394536709)
                  ·
                    rfl

theorem cell22_2989251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_2989251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989251 prefixEnd_2989251 := by exact prefixLift 2989251
  have htrace : WordTrace (prefixWord ++ tailWord_2989251) baseStart_2989251 baseEnd_2989251 := by
    simpa [prefixWord, tailWord_2989251, baseEnd_2989251] using wordTrace_append hprefix tailTrace_2989251
  have hstable : (prefixWord ++ tailWord_2989251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989251).length < 2 ^ (prefixWord ++ tailWord_2989251).sum := by decide
  have hdescent : baseEnd_2989251 < baseStart_2989251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989261 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2989261 : Nat := 118140960795 + 2989261 * 2 ^ 59
def prefixEnd_2989261 : Nat := 4983230072969 + 3 ^ 40 * 2989261 * 2
def baseEnd_2989261 : Nat := 1023285129826489490860097

theorem tailTrace_2989261 : CollatzResearch.WordTrace tailWord_2989261 prefixEnd_2989261 1023285129826489490860097 := by
  unfold tailWord_2989261
  simp only [CollatzResearch.WordTrace]
  refine ⟨109027305623425396978927637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72684870415616931319285091 109027305623425396978927637)
  ·
    refine ⟨5110654951098065483387233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109027305623425396978927637 5110654951098065483387233)
    ·
      refine ⟨3832991213323549112540425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5110654951098065483387233 3832991213323549112540425)
      ·
        refine ⟨2874743409992661834405319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3832991213323549112540425 2874743409992661834405319)
        ·
          refine ⟨4312115114988992751607979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874743409992661834405319 4312115114988992751607979)
          ·
            refine ⟨6468172672483489127411969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312115114988992751607979 6468172672483489127411969)
            ·
              refine ⟨4851129504362616845558977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6468172672483489127411969 4851129504362616845558977)
              ·
                refine ⟨3638347128271962634169233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4851129504362616845558977 3638347128271962634169233)
                ·
                  refine ⟨2728760346203971975626925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3638347128271962634169233 2728760346203971975626925)
                  ·
                    refine ⟨1023285129826489490860097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728760346203971975626925 1023285129826489490860097)
                    ·
                      rfl

theorem cell22_2989261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2989261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989261 prefixEnd_2989261 := by exact prefixLift 2989261
  have htrace : WordTrace (prefixWord ++ tailWord_2989261) baseStart_2989261 baseEnd_2989261 := by
    simpa [prefixWord, tailWord_2989261, baseEnd_2989261] using wordTrace_append hprefix tailTrace_2989261
  have hstable : (prefixWord ++ tailWord_2989261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989261).length < 2 ^ (prefixWord ++ tailWord_2989261).sum := by decide
  have hdescent : baseEnd_2989261 < baseStart_2989261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
